#include <stdio.h>
#include <memory>
#include <array>
#include <vector>
#include <cmath>
#include <string>
#include <set>
#include <cassert>
#include <unordered_set>
#include <unordered_map>

enum dag_type {
	CONSTANT = 0, INPUT = 1, ADD = 2, SUB = 3, NEG = 4, MUL = 5, DIV = 6, FMA = 7, OUTPUT = 8
};

class dag_node;

using dag_ptr = std::shared_ptr<dag_node>;

dag_ptr operator+(dag_ptr a, dag_ptr b);
dag_ptr operator-(dag_ptr a, dag_ptr b);
dag_ptr operator*(dag_ptr a, dag_ptr b);
dag_ptr operator-(dag_ptr a);
struct dagcmp {
	bool operator()(dag_ptr a, dag_ptr b) const;
};

class dag_node {
	static std::unordered_set<dag_node*> directory;
	static std::set<std::string> unused_names;
	static std::unordered_map<std::string, dag_node*> used_names;
	static std::vector<std::pair<double, std::weak_ptr<dag_node>>>constants;
	static int var_cnt;
	int outnum;
	dag_type type;
	std::vector<dag_ptr> inputs;
	std::string name;
	dag_node* self;
	double value;
	std::string reserve_name(std::string nm) {
		std::string cmd;
		auto i = unused_names.find(nm);
		if (i != unused_names.end()) {
			unused_names.erase(i);
			used_names.insert(std::make_pair(nm, this));
		} else if (used_names.find(nm) != used_names.end()) {
			auto* oldptr = used_names[nm];
			used_names[nm] = this;
			oldptr->name = gen_varname(oldptr);
			cmd = oldptr->name + " = " + nm + ";";
		}
		name = nm;
		return cmd;
	}
	static std::string gen_varname(dag_node* ptr) {
		std::string str;
		if (unused_names.empty()) {
			str = std::string("r") + std::to_string(var_cnt++);
		} else {
			auto nm = *unused_names.begin();
			unused_names.erase(unused_names.begin());
			str = nm;
		}
		used_names[str] = ptr;
		return str;
	}
public:
	static int var_count() {
		return var_cnt;
	}
	bool arithmetic() const {
		return type == ADD || type == SUB || type == MUL || type == NEG || type == DIV || type == FMA;
	}
	static dag_ptr create(dag_type t, dag_ptr in1 = nullptr, dag_ptr in2 = nullptr, dag_ptr in3 = nullptr) {
		auto ptr = std::make_shared<dag_node>();
		ptr->type = t;
		ptr->self = ptr.get();
		if (in1) {
			ptr->inputs.push_back(in1);
		}
		if (in2) {
			ptr->inputs.push_back(in2);
		}
		if (in3) {
			ptr->inputs.push_back(in3);
		}
		directory.insert(ptr.get());
		return ptr;
	}
	static dag_ptr create(double a) {
		if (a < 0.0) {
			auto neg = create(-a);
			auto ptr = std::make_shared<dag_node>();
			ptr->type = NEG;
			ptr->self = ptr.get();
			ptr->inputs.push_back(neg);
			directory.insert(ptr.get());
			return ptr;
		} else {
			for( int i = 0; i < constants.size(); i++) {
				double b = constants[i].first;
				if( std::fabs(a-b) < 1e-14) {
					return dag_ptr(constants[i].second);
				}
			}
			auto ptr = std::make_shared<dag_node>();
			ptr->type = CONSTANT;
			ptr->self = ptr.get();
			ptr->value = a;
			ptr->name = std::to_string(a);
			constants.push_back(std::make_pair(a,ptr));
			directory.insert(ptr.get());
			return ptr;
		}
	}
	static void remove_duplicates() {
		std::set<dag_ptr, dagcmp> uniques;
		std::unordered_map<dag_ptr,std::vector<dag_ptr*>> outputs;
		for( auto i = directory.begin(); i != directory.end(); i++) {
			for( auto& in : (*i)->inputs) {
				if( in->arithmetic() ) {
					if( uniques.find(in) == uniques.end()) {
						uniques.insert(in);
					}
					outputs[in].push_back(&in);
				}
			}
		}
		for( auto i : outputs) {
			auto iter = uniques.find(i.first);
			if( iter != uniques.end()) {
				if( iter->get() != i.first.get()) {
					for( auto* revin : i.second) {
						*revin = *iter;
					}
				}
			}
		}
	}
	static dag_ptr create(dag_type t, std::string nm, dag_ptr in1 = nullptr) {
		auto ptr = std::make_shared<dag_node>();
		ptr->self = ptr.get();
		ptr->type = t;
		ptr->name = nm;
		if (nm != "") {
			used_names.insert(std::make_pair(nm, ptr.get()));
		}
		directory.insert(ptr.get());
		if (in1) {
			ptr->inputs.push_back(in1);
		}
		return ptr;
	}
	static dag_ptr create(int outnum, dag_ptr in1) {
		auto ptr = std::make_shared<dag_node>();
		ptr->self = ptr.get();
		ptr->type = OUTPUT;
		ptr->outnum = outnum;
		ptr->inputs.push_back(in1);
		directory.insert(ptr.get());
		return ptr;
	}
	static int op_count() {
		int cnt = 0;
		for (auto i = directory.begin(); i != directory.end(); i++) {
			if ((*i)->type == ADD || (*i)->type == SUB || (*i)->type == MUL || (*i)->type == DIV || (*i)->type == NEG
					|| (*i)->type == FMA) {
				cnt++;
			}
		}
		return cnt;
	}
	bool deps_satisfied() const {
		for (auto ptr : inputs) {
			if (ptr->inputs.size()) {
				return false;
			}
		}
		return true;
	}
	int free_count() {
		int cnt = 0;
		for (auto& i : inputs) {
			if (i.use_count() == 1) {
				cnt++;
			}
		}
		return cnt;
	}

	static void propagate_signs() {
		bool found_one = true;
		while (found_one) {
			std::vector<dag_node*> nodes(directory.begin(), directory.end());
			found_one = false;
			for (auto& node : nodes) {
				bool prop = false;
				switch (node->type) {
					case ADD:
					if (node->inputs[0]->type == NEG && node->inputs[1]->type == NEG) {
						node->inputs[0] = node->inputs[0]->inputs[0];
						node->inputs[1] = node->inputs[1]->inputs[0];
						prop = true;
					} else if (node->inputs[0]->type == NEG) {
						node->inputs[0] = node->inputs[0]->inputs[0];
						std::swap(node->inputs[0], node->inputs[1]);
						node->type = SUB;
					} else if (node->inputs[1]->type == NEG) {
						node->inputs[1] = node->inputs[1]->inputs[0];
						node->type = SUB;
					}
					break;
					case SUB:
					if (node->inputs[0]->type == NEG && node->inputs[1]->type == NEG) {
						node->inputs[0] = node->inputs[0]->inputs[0];
						node->inputs[1] = node->inputs[1]->inputs[0];
						prop = true;
					} else if (node->inputs[0]->type == NEG) {
						node->inputs[0] = node->inputs[0]->inputs[0];
						prop = true;
						node->type = ADD;
					} else if (node->inputs[1]->type == NEG) {
						node->inputs[1] = node->inputs[1]->inputs[0];
						node->type = ADD;
					}
					break;
					case MUL:
					if (node->inputs[0]->type == NEG && node->inputs[1]->type == NEG) {
						node->inputs[0] = node->inputs[0]->inputs[0];
						node->inputs[1] = node->inputs[1]->inputs[1];
					} else if (node->inputs[0]->type == NEG) {
						node->inputs[0] = node->inputs[0]->inputs[0];
						prop = true;
					} else if (node->inputs[1]->type == NEG) {
						node->inputs[1] = node->inputs[1]->inputs[0];
						prop = true;
					}
					break;
				}
				if (prop) {
					found_one = true;
					auto new_dag = create(node->type, node->inputs[0]);
					for (int i = 1; i < node->inputs.size(); i++) {
						new_dag->inputs.push_back(node->inputs[i]);
					}
					node->type = NEG;
					node->inputs.resize(1);
					node->inputs[0] = new_dag;
				}
			}
		}

	}
	static std::vector<std::string> generate_program() {
		fprintf(stderr, "op count = %i\n", dag_node::op_count());
		std::vector<std::string> code;
		bool found_one = true;
		int opcnt = 0;
		while (found_one) {
			found_one = false;
			std::vector<dag_node*> candidates;
			for (auto i = directory.begin(); i != directory.end(); i++) {
				if ((*i)->inputs.size() && (*i)->deps_satisfied()) {
					found_one = true;
					candidates.push_back(*i);
				}
			}
			if (found_one) {
				int best_cnt = 0;
				dag_node* best_dag = candidates.front();
				for (auto cand : candidates) {
					if (cand->free_count() > best_cnt) {
						best_cnt = cand->free_count();
						best_dag = cand;
					}
				}
				auto tmp = best_dag->gen_code();
				code.insert(code.end(), tmp.begin(), tmp.end());
			}
		}
		return code;
	}
	std::vector<std::string> gen_code() {
		std::vector<std::string> cmds;
		if (name == "" && type != CONSTANT && type != OUTPUT && type != INPUT) {
			name = gen_varname(this);
		}
		std::string code;
		switch (type) {
			case CONSTANT:
			break;
			case INPUT:
			break;
			case ADD:
			code = name + " = " + inputs[0]->name + " + " + inputs[1]->name + ";";
			break;
			case SUB:
			code = name + " = " + inputs[0]->name + " - " + inputs[1]->name + ";";
			break;
			case NEG:
			code = name + " = -" + inputs[0]->name + ";";
			break;
			case MUL:
			code = name + " = " + inputs[0]->name + " * " + inputs[1]->name + ";";
			break;
			case FMA:
			code = name + " = std::fma(" + inputs[0]->name + ", " + inputs[1]->name + ", " + inputs[2]->name + ";";
			break;
			case OUTPUT:
			std::string oname = "x[" + std::to_string(outnum) + "]";
			auto cmd = reserve_name(oname);
			if (cmd != "") {
				cmds.push_back(cmd);
			}
			assert(oname == name);
			code = name + " = " + inputs[0]->name + ";";
			break;
		}
		inputs.resize(0);
		cmds.push_back(code);
		return cmds;
	}
	~dag_node() {
		if (directory.find(self) == directory.end()) {
			printf("Can't find self\n");
		} else {
			directory.erase(self);
		}
		if (name != "" && type != CONSTANT) {
			unused_names.insert(name);
			used_names.erase(name);
		}
	}
	friend struct dagcmp;

};

std::vector<std::pair<double, std::weak_ptr<dag_node>>>dag_node::constants;

dag_ptr operator+(dag_ptr a, dag_ptr b) {
	return dag_node::create(ADD, a, b);
}

dag_ptr operator-(dag_ptr a, dag_ptr b) {
	return dag_node::create(SUB, a, b);
}

dag_ptr operator*(dag_ptr a, dag_ptr b) {
	return dag_node::create(MUL, a, b);
}

dag_ptr operator-(dag_ptr a) {
	return dag_node::create(NEG, a);
}

bool dagcmp::operator()(dag_ptr a, dag_ptr b) const {
	if ((int) a->type < (int) b->type) {
		return true;
	} else if ((int) a->type > (int) b->type) {
		return false;
	} else {
		for (int i = 0; i < a->inputs.size(); i++) {
			if (a->inputs[i].get() < b->inputs[i].get()) {
				return true;
			} else if (a->inputs[i].get() > b->inputs[i].get()) {
				return false;
			}
		}
	}

	return false;
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

void print_code(std::vector<std::string> code, std::string fname, int incount, int outcount) {
	printf("std::vector<double> %s(std::vector<double>& x) {;\n", fname.c_str());
	printf("\tstd::vector<double> Xk(%i);\n", outcount);
	printf("\tdouble ");
	for (int i = 0; i < dag_node::var_count(); i++) {
		printf("r%i, ", i);
		if (i % 8 == 7) {
			printf("\n\t\t");
		}
	}
	printf("r%i;\n", dag_node::var_count());
	for (auto line : code) {
		printf("\t%s\n", line.c_str());
	}
	printf("\tXk = x;\n");
	printf("\treturn std::move(Xk);\n");
	printf("}\n");
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
					"\tfor( int i = 0; i < 1; i++) {\n"
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
					"\t\t\tprintf( \"%%i %%e %%e %%e %%e;\\n\", n, xout[2*n], xout[2*n+1], y[n].real(), y[n].imag())\n;\n"
					"\t\t}\n"
					"\t\terror = error / (2.0 * N);\n"
					"\t\tif( i == 0 ) {\n"
					"\t\t\tprintf( \"Error = %%e\\n\", error );\n"
					"\t\t}\n"
					"\t}\n"
					"\tprintf( \"%%e %%e %%e\\n\", tm1.read(), tm2.read(), tm2.read() / tm1.read() );\n"
					"\t\n"
					"}\n"
					"", N);
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
			auto twr = dag_node::create(cos(theta));
			auto twi = dag_node::create(sin(theta));
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

std::vector<dag_ptr> fft_radix4(std::vector<dag_ptr> xin, int N) {
	if (N == 1) {
		return xin;
	}
	std::vector<dag_ptr> xout(2 * N);
	std::vector<dag_ptr> even, odd1, odd3;
	for (int n = 0; n < N / 2; n++) {
		even.push_back(xin[4 * n]);
		even.push_back(xin[4 * n + 1]);
	}
	for (int n = 0; n < N / 4; n++) {
		odd1.push_back(xin[8 * n + 2]);
		odd1.push_back(xin[8 * n + 3]);
		odd3.push_back(xin[8 * n + 6]);
		odd3.push_back(xin[8 * n + 7]);
	}
	if (N == 4) {
		even = fft_radix2(even, 2);
		odd1 = fft_radix2(odd1, 1);
		odd3 = fft_radix2(odd3, 1);
	} else if (N == 8) {
		even = fft_radix4(even, 4);
		odd1 = fft_radix2(odd1, 2);
		odd3 = fft_radix2(odd3, 2);
	} else {
		even = fft_radix4(even, N / 2);
		odd1 = fft_radix4(odd1, N / 4);
		odd3 = fft_radix4(odd3, N / 4);
	}
	const auto tw_mult = [N](int k, dag_ptr r, dag_ptr i) {
		std::pair<dag_ptr, dag_ptr> rc;
		double theta = -2.0 * M_PI * k / N;
		if( k == 0 ) {
			rc.first = r;
			rc.second = i;
		} else if( k == N / 2 ) {
			rc.first = i;
			rc.second = -r;
		} else if( k == N / 4 ) {
			rc.first = -r;
			rc.second = -i;
		} else if( k == 3 * N / 4 ) {
			rc.first = -i;
			rc.second = r;
		} else {
			auto twr = dag_node::create(cos(theta));
			auto twi = dag_node::create(sin(theta));
			rc.first = r * twr - i * twi;
			rc.second = i * twr + r * twi;
		}
		return rc;
	};
	for (int k = 0; k < N / 4; k++) {
		auto odds1 = tw_mult(k, odd1[2 * k], odd1[2 * k + 1]);
		auto odds3 = tw_mult(3 * k, odd3[2 * k], odd3[2 * k + 1]);
		auto zsr = odds1.first + odds3.first;
		auto zsi = odds1.second + odds3.second;
		auto zdr = odds1.first - odds3.first;
		auto zdi = odds1.second - odds3.second;
		auto ur0 = even[2 * k + 0] + zsr;
		auto ui0 = even[2 * k + 1] + zsi;
		auto ur1 = even[2 * (k + N / 4) + 0] + zdi;
		auto ui1 = even[2 * (k + N / 4) + 1] - zdr;
		auto ur2 = even[2 * k + 0] - zsr;
		auto ui2 = even[2 * k + 1] - zsi;
		auto ur3 = even[2 * (k + N / 4) + 0] - zdi;
		auto ui3 = even[2 * (k + N / 4) + 1] + zdr;
		xout[2 * k] = ur0;
		xout[2 * k + 1] = ui0;
		xout[2 * (k + N / 4)] = ur1;
		xout[2 * (k + N / 4) + 1] = ui1;
		xout[2 * (k + N / 2)] = ur2;
		xout[2 * (k + N / 2) + 1] = ui2;
		xout[2 * (k + 3 * N / 4)] = ur3;
		xout[2 * (k + 3 * N / 4) + 1] = ui3;
		/*if (k == 0) {
		 auto tr1 = odd[2 * k];
		 auto ti1 = odd[2 * k + 1];
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
		 auto twr = dag_node::create(cos(theta));
		 auto twi = dag_node::create(sin(theta));
		 auto tr = odd[2 * k] * twr - odd[2 * k + 1] * twi;
		 auto ti = odd[2 * k] * twi + odd[2 * k + 1] * twr;
		 xout[2 * k] = even[2 * k] + tr;
		 xout[2 * (k + N / 2)] = even[2 * k] - tr;
		 xout[2 * k + 1] = even[2 * k + 1] + ti;
		 xout[2 * (k + N / 2) + 1] = even[2 * k + 1] - ti;
		 }*/
	}
	return xout;
}

std::unordered_set<dag_node*> dag_node::directory;
std::set<std::string> dag_node::unused_names;
std::unordered_map<std::string, dag_node*> dag_node::used_names;
int dag_node::var_cnt = 0;

int main() {
	std::vector<dag_ptr> input;
	int N = 32;
	for (int n = 0; n < 2 * N; n++) {
		input.push_back(dag_node::create(INPUT, std::string("x[") + std::to_string(n) + "]"));
	}

	auto output = fft_radix4(input, N);
	input.clear();
	for (int n = 0; n < 2 * N; n++) {
		output[n] = dag_node::create(n, output[n]);
	}
	dag_node::propagate_signs();
	dag_node::remove_duplicates();
	auto prog = dag_node::generate_program();
	print_test_header();
	print_code(prog, "test", 2 * N, 2 * N);
	print_test_code(N);
	return 0;
}

/*


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

 class dag_node {
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
 */
