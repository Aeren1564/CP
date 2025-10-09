#include <bits/stdc++.h>
// #include <x86intrin.h>
using namespace std;
#if __cplusplus >= 202002L
using namespace numbers;
#endif
mt19937 rng(chrono::high_resolution_clock::now().time_since_epoch().count());
mt19937_64 rngll(chrono::high_resolution_clock::now().time_since_epoch().count());
using randint_t = uniform_int_distribution<int>;
using randll_t = uniform_int_distribution<long long>;
using randd_t = uniform_real_distribution<double>;
// return x with probability p, y with probability 1-p
template<class T>
T pick(T x, T y, double p = 0.5){
	assert(-0.0001 <= p && p <= 1.0001);
	return randd_t(0, 1)(rng) <= p ? x : y;
}
array<int, 2> gen_range(int n, bool allow_empty_range = false){
	if(allow_empty_range){
		int l = rng() % (n + 1), r = rng() % (n + 1);
		if(l > r) swap(l, r);
		return {l, r};
	}
	else{
		int l = rng() % n, r = rng() % n;
		if(l > r) swap(l, r);
		return {l, r + 1};
	}
}



int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int n = 3, m = 10, nc = 4, qn = 100;
	cout << n << " " << m << " " << nc << " " << qn << "\n";
	auto gen_n = [&]()->int{
		return rng() % n;
	};
	auto gen_c = [&]()->int{
		return rng() % nc;
	};
	for(auto qi = 0; qi < qn; ++ qi){
		int type = rng() % 3;
		cout << type << "\n";
		if(type <= 1){
			auto [l, r] = gen_range(m);
			cout << gen_n() << " " << l << " " << r << " " << gen_c() << "\n";
		}
		else{
			for(auto i = 0; i < 3; ++ i){
				cout << gen_n() << " ";
			}
			cout << gen_c() << "\n";
		}
	}
	return 0;
}

/*

*/