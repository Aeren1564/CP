#include <bits/stdc++.h>
using namespace std;
#if __cplusplus > 201703L
#include <ranges>
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
array<int, 2> get_range(int n){
	int l = rng() % n, r = rng() % n;
	if(l > r) swap(l, r);
	return {l, r + 1};
}


int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	auto gen_len = [&]()->int{
		return rng() % 3 == 0 ? rng() % 5 + 1 : rng() % 2 == 0 ? rng() % 128 + 1 : rng() % 1000 + 1;
	};
	for(auto i = 0; i < 2; ++ i){
		if(rng() % 3){
			cout << "+-"[rng() % 2];
		}
		int len = gen_len();
		for(auto i = 0; i < len; ++ i){
			cout << rng() % 2;
		}
		cout << "\n";
	}
	return 0;
}

/*

*/

////////////////////////////////////////////////////////////////////////////////////////
//                                                                                    //
//                                   Coded by Aeren                                   //
//                                                                                    //
////////////////////////////////////////////////////////////////////////////////////////