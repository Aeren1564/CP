// #pragma GCC optimize("O3,unroll-loops")
#include <bits/stdc++.h>
// #include <x86intrin.h>
using namespace std;
#if __cplusplus >= 202002L
using namespace numbers;
#endif
mt19937 rng(chrono::high_resolution_clock::now().time_since_epoch().count());
mt19937_64 rngll(chrono::high_resolution_clock::now().time_since_epoch().count());
using randint_t = uniform_int_distribution<int>;
using randll_t = uniform_int_distribution<int64_t>;
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
template<class T>
vector<T> sample_array(int n, T low, T high, bool distinct = false){
	assert(low < high && (!distinct || high - low >= n));
	set<T> used;
	vector<T> array(n);
	for(auto i = 0; i < n; ++ i){
		T x = randll_t(low, high - 1)(rng);
		if(distinct){
			if(used.count(x)){
				-- i;
				continue;
			}
			used.insert(x);
		}
		array[i] = x;
	}
	return array;
}

// Returns indices i<j such that a[i]+a[j]<a[i&j]+a[i|j]
// O(n * log(n)^2)
template<class T>
optional<array<int, 2>> check_antisubmodularity(const vector<T> &a){
	int n = (int)a.size();
	assert(n >= 1 && __builtin_popcount(n) == 1);
	int w = __lg(n);
	for(auto x = 0; x < n; ++ x) for(auto i = 0; i < w; ++ i) if(~x >> i & 1) for(auto j = i + 1; j < w; ++ j) if(~x >> j & 1) if(a[x | 1 << i] + a[x | 1 << j] < a[x] + a[x | 1 << i | 1 << j]) return array{x | 1 << i, x | 1 << j};
	return {};
}

int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int nv = rng() % 10 + 1;
	int minimize = rng() % 2;
	int n = rng() % 20;
	int th = 10;
	int mx = 10;
	cout << nv << " " << minimize << " " << n << "\n";
	for(auto i = 0; i < n; ++ i){
		int type = rng() % 5;
		if(type >= th || type <= 3 && type > nv){
			-- i;
			continue;
		}
		if(type <= 3){
			auto array = sample_array(type, 0, nv, true);
			vector<int> value(1 << type);
			while(true){
				for(auto mask = 0; mask < 1 << type; ++ mask){
					value[mask] = int(rng() % (2 * mx + 1)) - mx;
				}
				if(!minimize){
					for(auto &x: value){
						x = -x;
					}
				}
				auto res = !check_antisubmodularity(value);
				if(!minimize){
					for(auto &x: value){
						x = -x;
					}
				}
				if(res){
					break;
				}
			}
			cout << type << "\n";
			for(auto i: array){
				cout << i << " ";
			}
			cout << "\n";
			for(auto mask = 0; mask < 1 << type; ++ mask){
				cout << value[mask] << " ";
			}
			cout << "\n";
		}
		else{
			int m = rng() % nv + 1, base = rng() % 2, value = (minimize ? -1 : 1) * int(rng() % mx + 1);
			cout << type << "\n" << m << " " << base << " " << value << "\n";
			auto array = sample_array(m, 0, nv, true);
			for(auto i: array){
				cout << i << " ";
			}
			cout << "\n";
		}
	}
	return 0;
}

/*

*/