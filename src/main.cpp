#include <stdio.h>
#include <memory>
#include <array>
#include <vector>
#include <cmath>
#include <string>
#include <unordered_set>
#include <set>
#include <stack>

enum dag_type {
	CONSTANT = 0, INPUT = 1, ADD = 2, SUB = 3, NEG = 4, MUL = 5, DIV = 6, FMA = 7
};

struct dag_node;
using dag_ptr = std::shared_ptr<dag_node>;
struct dag_hash {
	size_t operator()(std::weak_ptr<dag_node> ptr) const {
		return (size_t) std::shared_ptr<dag_node>(ptr).get();
	}
};

using dag_list_t = std::unordered_set<std::weak_ptr<dag_node>, dag_hash>;

dag_list_t dag_list;

std::stack<std::string> var_names;

struct dag_node {
	dag_type op;
	bool sat;
	bool fixed;
	std::string name;
	std::vector<dag_ptr> in;
	~dag_node() {
		if (op != CONSTANT && name != "") {
			var_names.push(name);
		}
	}
};

static int var_cnt = 0;

std::string gen_varname() {
	if (var_names.size()) {
		auto m = var_names.top();
		var_names.pop();
		return m;
	} else {
		return std::string("var") + std::to_string(var_cnt++);
	}
}

bool operator==(std::weak_ptr<dag_node> a, std::weak_ptr<dag_node> b) {
	return std::shared_ptr<dag_node>(a).get() == std::shared_ptr<dag_node>(b).get();
}

std::shared_ptr<dag_node> new_node(std::string nm = "") {
	auto dag = std::make_shared<dag_node>();
	dag->name = nm;
	dag->fixed = false;
	dag->sat = false;
	dag_list.insert(std::weak_ptr<dag_node>(dag));
	return dag;
}

void optimize_fma() {
	for (const auto weak : dag_list) {
		if (weak.use_count()) {
			dag_ptr node = dag_ptr(weak);
			if (node->op == ADD) {
				int i = -1;
				int j;
				if (node->in[0]->op == MUL) {
					i = 0;
					j = 1;
				} else if (node->in[1]->op == MUL) {
					i = 1;
					j = 0;
				}
				if (i != -1) {
					node->op = FMA;
					auto replace = node->in[i];
					auto a = replace->in[0];
					auto b = replace->in[1];
					auto c = node->in[j];
					node->in.resize(0);
					node->in.push_back(a);
					node->in.push_back(b);
					node->in.push_back(c);
				}
			}
		}
	}
}

dag_ptr operator+(dag_ptr a, dag_ptr b) {
	std::string nm;

	auto ptr = new_node(nm);
	ptr->op = ADD;
	ptr->in.resize(0);
	ptr->in.push_back(a);
	ptr->in.push_back(b);
	return ptr;
}

dag_ptr operator-(dag_ptr a, dag_ptr b) {
	std::string nm;

	auto ptr = new_node(nm);
	ptr->op = SUB;
	ptr->in.resize(0);
	ptr->in.push_back(a);
	ptr->in.push_back(b);
	return ptr;
}

dag_ptr operator-(dag_ptr a) {
	std::string nm;

	auto ptr = new_node(nm);
	ptr->op = NEG;
	ptr->in.resize(0);
	ptr->in.push_back(a);
	return ptr;
}

dag_ptr operator*(dag_ptr a, dag_ptr b) {
	std::string nm;

	auto ptr = new_node(nm);
	ptr->op = MUL;
	ptr->in.resize(0);
	ptr->in.push_back(a);
	ptr->in.push_back(b);
	return ptr;
}

dag_ptr dag_constant(double a) {
	char* ptr;
	asprintf(&ptr, "double(%.17e)", a);
	auto dag = new_node(ptr);
	free(ptr);
	dag->sat = true;
	dag->op = CONSTANT;
	return dag;
}

std::vector<std::string> gen_code(dag_ptr out) {
	std::vector<std::string> rc;
	std::string cmd;
	for (auto & i : out->in) {
		if (!i->sat) {
			auto child = gen_code(i);
			rc.insert(rc.end(), child.begin(), child.end());
		}
	}
	if (out->name == "") {
		out->name = gen_varname();
	}
	switch (out->op) {
	case ADD:
		if (out->name == out->in[0]->name) {
			cmd = out->name + " += " + out->in[1]->name + ";";
		} else if (out->name == out->in[1]->name) {
			cmd = out->name + " += " + out->in[0]->name + ";";
		} else {
			cmd = out->name + " = " + out->in[0]->name + " + " + out->in[1]->name + ";";
		}
		break;
	case SUB:
		if (out->name == out->in[0]->name) {
			cmd = out->name + " -= " + out->in[1]->name + ";";
		} else {
			cmd = out->name + " = " + out->in[0]->name + " - " + out->in[1]->name + ";";
		}
		break;
	case NEG:
		cmd = out->name + " = -" + out->in[0]->name + ";";
		break;
	case MUL:
		if (out->name == out->in[0]->name) {
			cmd = out->name + " *= " + out->in[1]->name + ";";
		} else if (out->name == out->in[1]->name) {
			cmd = out->name + " *= " + out->in[0]->name + ";";
		} else {
			cmd = out->name + " = " + out->in[0]->name + " * " + out->in[1]->name + ";";
		}
		break;
	case FMA:
		cmd = out->name + " = std::fma(" + out->in[0]->name + ", " + out->in[1]->name + ", " + out->in[2]->name + ");";
		break;
	case INPUT:
		break;
	}
	if (cmd != "") {
		rc.push_back(cmd);
	}
	out->in.clear();
	out->sat = true;
	return rc;
}

void print_code(std::vector<std::string> code, std::string fname, int incount, int outcount) {
	printf("std::vector<double> %s(std::vector<double> xn) {;\n", fname.c_str());
	printf("\tstd::vector<double> Xk(%i);\n", outcount);
	printf("\tdouble ");
	for (int i = 0; i < var_cnt; i++) {
		printf("var%i, ", i);
		if (i % 8 == 7) {
			printf("\n\t\t");
		}
	}
	printf("var%i;\n", var_cnt);
	for (auto line : code) {
		printf("\t%s\n", line.c_str());
	}
	printf("\treturn std::move(Xk);\n");
	printf("}\n");
}

std::vector<dag_ptr> fft_radix2(std::vector<dag_ptr> xin, int N) {
	if (N == 1) {
		return xin;
	}
	std::vector<dag_ptr> xout(2 * N);
	std::vector<dag_ptr> even, odd;
	for (int n = 0; n < N / 2; n++) {
		even.push_back(xin[4 * n]);
		even.push_back(xin[4 * n + 1]);
	}
	for (int n = 0; n < N / 2; n++) {
		odd.push_back(xin[4 * n + 2]);
		odd.push_back(xin[4 * n + 3]);
	}
	even = fft_radix2(even, N / 2);
	odd = fft_radix2(odd, N / 2);
	for (int k = 0; k < N / 2; k++) {
		double theta = -2.0 * M_PI * k / N;
		if (k == 0) {
			auto tr = odd[2 * k];
			auto ti = odd[2 * k + 1];
			xout[2 * k] = even[2 * k] + tr;
			xout[2 * (k + N / 2)] = even[2 * k] - tr;
			xout[2 * k + 1] = even[2 * k + 1] + ti;
			xout[2 * (k + N / 2) + 1] = even[2 * k + 1] - ti;
		} else if (k == N / 2) {
			auto tr = -odd[2 * k];
			auto ti = -odd[2 * k + 1];
			xout[2 * k] = even[2 * k] + tr;
			xout[2 * (k + N / 2)] = even[2 * k] - tr;
			xout[2 * k + 1] = even[2 * k + 1] + ti;
			xout[2 * (k + N / 2) + 1] = even[2 * k + 1] - ti;
		} else if (k == N / 4) {
			auto tr = odd[2 * k + 1];
			auto ti = -odd[2 * k];
			xout[2 * k] = even[2 * k] + tr;
			xout[2 * (k + N / 2)] = even[2 * k] - tr;
			xout[2 * k + 1] = even[2 * k + 1] + ti;
			xout[2 * (k + N / 2) + 1] = even[2 * k + 1] - ti;
		} else if (k == 3 * N / 4) {
			auto tr = -odd[2 * k + 1];
			auto ti = odd[2 * k];
			xout[2 * k] = even[2 * k] + tr;
			xout[2 * (k + N / 2)] = even[2 * k] - tr;
			xout[2 * k + 1] = even[2 * k + 1] + ti;
			xout[2 * (k + N / 2) + 1] = even[2 * k + 1] - ti;
		} else {
			auto twr = dag_constant(cos(theta));
			auto twi = dag_constant(sin(theta));
			auto tr = odd[2 * k] * twr - odd[2 * k + 1] * twi;
			auto ti = odd[2 * k] * twi + odd[2 * k + 1] * twr;
			xout[2 * k] = even[2 * k] + tr;
			xout[2 * (k + N / 2)] = even[2 * k] - tr;
			xout[2 * k + 1] = even[2 * k + 1] + ti;
			xout[2 * (k + N / 2) + 1] = even[2 * k + 1] - ti;
		}
	}
	return xout;
}

void print_test_header() {
	printf("\n"
			"\n"
			"\n"
			"#include <fftw3.h>\n"
			"#include <cmath>\n"
			"#include <vector>\n"
			"#include <complex>\n"
			"#include <unordered_map>\n"
			"\t");
}

void print_test_code(int N) {
	printf("\n"
			"\n"
			"void fftw(std::vector<std::complex<double>>& x) {\n"
			"\tconst int N = x.size();\n"
			"\tstatic std::unordered_map<int, fftw_plan> plans;\n"
			"\tstatic std::unordered_map<int, fftw_complex*> in;\n"
			"\tstatic std::unordered_map<int, fftw_complex*> out;\n"
			"\tif (plans.find(N) == plans.end()) {\n"
			"\t\tin[N] = (fftw_complex*) malloc(sizeof(fftw_complex) * N);\n"
			"\t\tout[N] = (fftw_complex*) malloc(sizeof(fftw_complex) * N);\n"
			"\t\tplans[N] = fftw_plan_dft_1d(N, in[N], out[N], FFTW_FORWARD, FFTW_ESTIMATE);\n"
			"\t}\n"
			"\tauto* i = in[N];\n"
			"\tauto* o = out[N];\n"
			"\tfor (int n = 0; n < N; n++) {\n"
			"\t\ti[n][0] = x[n].real();\n"
			"\t\ti[n][1] = x[n].imag();\n"
			"\t}\n"
			"\tfftw_execute(plans[N]);\n"
			"\tfor (int n = 0; n < N; n++) {\n"
			"\t\tx[n].real(o[n][0]);\n"
			"\tx[n].imag(o[n][1]);\n"
			"\t}\n"
			"}\n"
			"\n"
			"\n"
			"double rand1() {\n"
			"\treturn (rand() + 0.5) / RAND_MAX;\n"
			"}\n"
			"\n");
	printf(
			"#include <chrono>\n"
					"class timer {\n"
					"\tstd::chrono::time_point<std::chrono::high_resolution_clock> start_time;\n"
					"\tdouble time;\n"
					"public:\n"
					"\tinline timer() {\n"
					"\t\ttime = 0.0;\n"
					"\t}\n"
					"\tinline void stop() {\n"
					"\t\tstd::chrono::time_point<std::chrono::high_resolution_clock> stop_time = std::chrono::high_resolution_clock::now();\n"
					"\t\tstd::chrono::duration<double> dur = stop_time - start_time;\n"
					"\t\ttime += dur.count();\n"
					"\t}\n"
					"\tinline void start() {\n"
					"\t\tstart_time = std::chrono::high_resolution_clock::now();\n"
					"\t}\n"
					"\tinline void reset() {\n"
					"\t\ttime = 0.0;\n"
					"\t}\n"
					"\tinline double read() {\n"
					"\t\treturn time;\n"
					"\t}\n"
					"};\n"
					"\n"
					"\n"
					"\n"
					"int main() {\n"
					"\tconstexpr int N = %i;\n"
					"\tstd::vector<double> xin(2 * N);\n"
					"\tstd::vector<std::complex<double>> y(N);\n"
					"\ttimer tm1, tm2;\n"
					"\tfor( int i = 0; i < 256; i++) {\n"
					"\t\tfor( int n = 0; n < 2 * N; n++) {\n"
					"\t\t\txin[n] = rand1();\n"
					"\t\t\tif( n %% 2 == 0 ) {\n"
					"\t\t\t\ty[n / 2].real(xin[n]);\n"
					"\t\t\t} else {\n"
					"\t\t\t\ty[n / 2].imag(xin[n]);\n"
					"\t\t\t}\n"
					"\t\t}\n"
					"\t\ttm1.start();\n"
					"\t\tauto xout = test(xin);\n"
					"\t\ttm1.stop();\n"
					"\t\ttm2.start();\n"
					"\t\tfftw(y);\n"
					"\t\ttm2.stop();\n"
					"\t\tdouble error = 0.0;\n"
					"\t\tfor( int n = 0; n < N; n++) {\n"
					"\t\t\terror += std::pow(xout[2 * n] - y[n].real(), 2);\n"
					"\t\t\terror += std::pow(xout[2 * n + 1] - y[n].imag(), 2);\n"
					"\t\t}\n"
					"\t\terror = error / (2.0 * N);\n"
					"\t\tif( i == 255 ) {\n"
					"\t\t\tprintf( \"Error = %%e\\n\", error );\n"
					"\t\t}\n"
					"\t}\n"
					"\tprintf( \"%%e %%e %%e\\n\", tm1.read(), tm2.read(), tm2.read() / tm1.read() );\n"
					"\t\n"
					"}\n"
					"", N);
}

bool deps_ready(dag_ptr dag) {
	for (auto in : dag->in) {
		if (!in->sat) {
			return false;
		}
	}
	return true;
}

std::vector<dag_ptr> get_candidates() {
	std::vector<dag_ptr> cands;
	for (auto wdag : dag_list) {
		if (wdag.use_count()) {
			auto dag = dag_ptr(wdag);
			if (!dag->sat) {
				bool ready = true;
				for (auto i : dag->in) {
					if (!i->sat) {
						ready = false;
						break;
					}
				}
				if (ready) {
					cands.push_back(dag);
				}
			}
		}
	}
	return cands;
}

int main() {
	std::vector<dag_ptr> input;
	int N = 8;
	for (int n = 0; n < 2 * N; n++) {
		auto tmp = new_node(std::string("xn[") + std::to_string(n) + "]");
		tmp->op = INPUT;
		tmp->sat = true;
		input.push_back(tmp);
	}

	auto output = fft_radix2(input, N);
	input.clear();
	for (int n = 0; n < 2 * N; n++) {
		output[n]->fixed = true;
		output[n]->name = std::string("Xk[") + std::to_string(n) + "]";
	}
	optimize_fma();
	std::vector<std::string> code;
	auto cands = get_candidates();
	while (cands.size()) {
		auto cd = gen_code(cands.front());
		code.insert(code.end(), cd.begin(), cd.end());
		cands = get_candidates();
	}
	print_test_header();
	print_code(code, "test", 2 * N, 2 * N);
	print_test_code(N);
	fprintf( stderr, "%i total ops\n", code.size());

}
