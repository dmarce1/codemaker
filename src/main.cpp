#include <stdio.h>
#include <memory>
#include <array>
#include <vector>
#include <cmath>
#include <string>

#define MAX_INPUT 3

enum dag_type {
	CONSTANT, INPUT, ADD, SUB, NEG, MUL, DIV, FMA
};

struct dag_node;

using dag_ptr = std::shared_ptr<dag_node>;

struct dag_node {
	dag_type op;
	bool sat;
	std::string name;
	std::array<dag_ptr, MAX_INPUT> inp;
};

static int var_cnt = -1;

std::vector<std::weak_ptr<dag_node>> dag_list;

std::string gen_varname() {
	var_cnt++;
	return std::string("var") + std::to_string(var_cnt);
}

std::shared_ptr<dag_node> new_node(std::string nm = "") {
	auto dag = std::make_shared<dag_node>();
	if (nm == "") {
		dag->name = gen_varname();
	} else {
		dag->name = nm;
	}
	dag->sat = false;
	dag_list.push_back(dag);
	return dag;
}

void optimize_fma() {
	for (const auto weak : dag_list) {
		dag_ptr node = dag_ptr(weak);
		if (node->op == ADD) {
			int i = -1;
			int j;
			if (node->inp[0]->op == MUL) {
				i = 0;
				j = 1;
			} else if (node->inp[1]->op == MUL) {
				i = 1;
				j = 0;
			}
			if (i != -1) {
				node->op = FMA;
				auto replace = node->inp[i];
				auto a = replace->inp[0];
				auto b = replace->inp[1];
				auto c = node->inp[j];
				node->inp[0] = a;
				node->inp[1] = b;
				node->inp[2] = c;
			}
		}
	}
}

dag_ptr operator+(dag_ptr a, dag_ptr b) {
	std::string nm;

	auto ptr = new_node(nm);
	ptr->op = ADD;
	ptr->inp[0] = a;
	ptr->inp[1] = b;
	return ptr;
}

dag_ptr operator-(dag_ptr a, dag_ptr b) {
	std::string nm;

	auto ptr = new_node(nm);
	ptr->op = SUB;
	ptr->inp[0] = a;
	ptr->inp[1] = b;
	return ptr;
}

dag_ptr operator*(dag_ptr a, dag_ptr b) {
	std::string nm;

	auto ptr = new_node(nm);
	ptr->op = MUL;
	ptr->inp[0] = a;
	ptr->inp[1] = b;
	return ptr;
}

dag_ptr dag_constant(double a) {
	auto ptr = new_node(std::to_string(a));
	ptr->op = CONSTANT;
	return ptr;
}

std::vector<std::string> gen_code(dag_ptr out) {
	std::vector<std::string> rc;
	if (out->sat) {
		return std::vector<std::string>();
	}
	std::string cmd;
	for (int i = 0; i < MAX_INPUT; i++) {
		if (out->inp[i] == nullptr) {
			break;
		}
		auto child = gen_code(out->inp[i]);
		rc.insert(rc.end(), child.begin(), child.end());
		out->sat = true;
	}
	switch (out->op) {
	case ADD:
		cmd = out->name + " = " + out->inp[0]->name + " + " + out->inp[1]->name + ";";
		break;
	case SUB:
		cmd = out->name + " = " + out->inp[0]->name + " - " + out->inp[1]->name + ";";
		break;
	case MUL:
		cmd = out->name + " = " + out->inp[0]->name + " * " + out->inp[1]->name + ";";
		break;
	case FMA:
		cmd = out->name + " = std::fma(" + out->inp[0]->name + ", " + out->inp[1]->name + ", " + out->inp[2]->name + ");";
		break;
	case INPUT:
		break;
	}
	if (cmd != "") {
		rc.push_back(cmd);
	}
	out->sat = true;
	return rc;
}

void print_code(std::vector<std::string> code, std::string fname, int incount, int outcount) {
	printf("std::vector<double> %s(const std::vector<double> xn) {;\n", fname.c_str());
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
		auto twr = dag_constant(cos(theta));
		auto twi = dag_constant(sin(theta));
		auto tr = odd[2 * k] * twr - odd[2 * k + 1] * twi;
		auto ti = odd[2 * k] * twi + odd[2 * k + 1] * twr;
		xout[2 * k] = even[2 * k] + tr;
		xout[2 * (k + N / 2)] = even[2 * k] - tr;
		xout[2 * k + 1] = even[2 * k + 1] + ti;
		xout[2 * (k + N / 2) + 1] = even[2 * k + 1] - ti;
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
			"\n"
			"int main() {\n"
			"\tconstexpr int N = ");
	printf(std::string(std::to_string(N) + ";\n"
			"\tstd::vector<double> xin(2 * N);\n"
			"\tstd::vector<std::complex<double>> y(N);\n"
			"\tfor( int n = 0; n < 2 * N; n++) {\n"
			"\t\txin[n] = rand1();\n"
			"\t\tif( n % 2 == 0 ) {\n"
			"\t\t\ty[n / 2].real(xin[n]);\n"
			"\t\t} else {\n"
			"\t\t\ty[n / 2].imag(xin[n]);\n"
			"\t\t}\n"
			"\t}\n"
			"\tauto xout = test(xin);\n"
			"\tfftw(y);\n"
			"\tfor( int n = 0; n < N; n++) {\n"
			"\t\tprintf( \"%%i %%e %%e %%e %%e\\n\", n, xout[2 * n], xout[2 * n + 1], y[n].real(), y[n].imag() );\n"
			"\t}\n"
			"}\n"
			"\n"
			"").c_str());
}

int main() {
	std::vector<dag_ptr> input;
	int N = 64;
	for (int n = 0; n < 2 * N; n++) {
		auto tmp = new_node(std::string("xn[") + std::to_string(n) + "]");
		tmp->op = INPUT;
		input.push_back(tmp);
	}

	auto output = fft_radix2(input, N);
	for (int n = 0; n < 2 * N; n++) {
		output[n]->name = std::string("Xk[") + std::to_string(n) + "]";
	}
	optimize_fma();
	std::vector<std::string> code;
	for (auto o : output) {
		auto cd = gen_code(o);
		code.insert(code.end(), cd.begin(), cd.end());
	}
	print_test_header();
	print_code(code, "test", 2 * N, 2 * N);
	print_test_code(N);

}
