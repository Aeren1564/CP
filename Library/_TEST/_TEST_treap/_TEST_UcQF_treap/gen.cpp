#include <x86intrin.h>
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
array<int, 2> get_range(int n, bool allow_empty_range = false){
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
	int qn = 10000, mx = 1000000000;
	cout << qn << "\n";
	int n = 0;
	for(auto qi = 0; qi < qn; ++ qi){
		int type;
		while(true){
			type = rng() % 10;
			if(type == 0 || type >= 8){
				int p = rng() % (n + 1);
				cout << "0 " << p << " " << rng() % mx << "\n";
				++ n;
				break;
			}
			else if(type == 1){
				if(n){
					int p = rng() % n;
					cout << type << " " << p << "\n";
					-- n;
					break;
				}
			}
			else if(type == 2){
				if(n){
					int p = rng() % n;
					cout << type << " " << p << " " << rng() % mx << "\n";
					break;
				}
			}
			else if(type == 3){
				if(n){
					int p = rng() % n;
					cout << type << " " << p << " " << rng() % mx << "\n";
					break;
				}
			}
			else if(type == 4){
				auto [l, r] = get_range(n, true);
				cout << type << " " << l << " " << r << " " << rng() % mx << "\n";
				break;
			}
			else if(type == 5){
				if(n){
					int p = rng() % n;
					cout << type << " " << p << "\n";
					break;
				}
			}
			else if(type == 6){
				auto [l, r] = get_range(n, true);
				cout << type << " " << l << " " << r << "\n";
				break;
			}
			else{
				auto [l, r] = get_range(n, true);
				cout << type << " " << l << " " << r << "\n";
				break;
			}
		}
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