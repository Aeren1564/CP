// #include <bits/allocator.h> // Temp fix for gcc13 global pragma
// #pragma GCC target("avx2,bmi2,popcnt,lzcnt")
// #pragma GCC optimize("O3,unroll-loops")
#include <bits/stdc++.h>
// #include <x86intrin.h>
using namespace std;
#if __cplusplus >= 202002L
using namespace numbers;
#endif
#ifdef LOCAL
	#include "Debug.h"
#else
	#define debug_endl() 42
	#define debug(...) 42
	#define debug2(...) 42
	#define debug_bin(...) 42
#endif



int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	long long l, r, iv, is;
	int qn;
	cin >> l >> r >> iv >> is >> qn;
	vector<long long> value(r - l);
	vector<long long> slope(r - l, is);
	for(auto x = l; x < r; ++ x){
		value[x - l] = iv + is * (x - l);
	}
	for(auto qi = 0; qi < qn; ++ qi){
		int type;
		cin >> type;
		if(type == 0){
			long long cl, cr, v, s;
			cin >> cl >> cr >> v >> s;
			for(auto x = cl; x < cr; ++ x){
				if(l <= x && x < r){
					value[x - l] += v + s * (x - cl);
					slope[x - l] += s;
				}
			}
		}
		else if(type == 1){
			long long cl, cr, v, s;
			cin >> cl >> cr >> v >> s;
			for(auto x = cl; x < cr; ++ x){
				if(l <= x && x < r){
					value[x - l] += v + s * (cr - x);
					slope[x - l] -= s;
				}
			}
		}
		else if(type == 2){
			int n;
			cin >> n;
			vector<pair<long long, long long>> piecewise_line(n);
			for(auto &[x, y]: piecewise_line){
				cin >> x >> y;
			}
			for(auto i = 0; i < n - 1; ++ i){
				auto [x, y] = piecewise_line[i];
				auto [z, w] = piecewise_line[i + 1];
				long long s = (w - y) / (z - x);
				for(auto t = x; t < z; ++ t){
					if(l <= t && t < r){
						value[t - l] += y + s * (t - x);
						slope[t - l] += s;
					}
				}
			}
		}
		else{
			long long cl, cr;
			cin >> cl >> cr;
			vector<array<long long, 4>> res;
			for(auto ccl = cl; ccl < cr; ){
				int ccr = ccl + 1;
				while(ccr < cr && slope[ccl - l] == value[ccr - l] - value[ccr - 1 - l] && slope[ccr - l] == slope[ccl - l]){
					++ ccr;
				}
				res.push_back({ccl, ccr, value[ccl - l], slope[ccl - l]});
				ccl = ccr;
			}
			cout << (int)res.size() << "\n";
			for(auto [l, r, v, s]: res){
				cout << l << " " << r << " " << v << " " << s << "\n";
			}
		}
	}
	return 0;
}

/*

*/