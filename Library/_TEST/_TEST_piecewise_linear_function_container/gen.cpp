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

vector<array<int, 2>> generate_tree(auto &&rng, int n, optional<vector<int>> input_deg = {}){
	if(input_deg){
		assert((int)input_deg->size() == n);
		assert(accumulate(input_deg->begin(), input_deg->end(), 0) == 2 * n - 2);
		for(auto d: *input_deg) assert(1 <= d);
	}
	vector<array<int, 2>> res;
	if(n <= 3 || !input_deg && rng() & 1) for(auto u = 1; u < n; ++ u) res.push_back({int(rng() % u), u});
	else{
		vector<int> prufer(n - 2), deg(n, 1);
		if(input_deg){
			deg = *input_deg;
			prufer.clear();
			for(auto u = 0; u < n; ++ u) for(auto i = 0; i < deg[u] - 1; ++ i) prufer.push_back(u);
		}
		else for(auto &u: prufer) ++ deg[u = rng() % n];
		int leaf = find(deg.begin(), deg.end(), 1) - deg.begin(), u = leaf;
		for(auto v: prufer){
			res.push_back({min(leaf, v), max(leaf, v)});
			if(-- deg[v] == 1 && v < u) leaf = v;
			else{
				u = find(deg.begin() + u + 1, deg.end(), 1) - deg.begin();
				leaf = u;
			}
		}
		res.push_back({leaf, n - 1});
	}
	vector<int> label(n);
	iota(label.begin(), label.end(), 0);
	shuffle(label.begin(), label.end(), rng);
	for(auto &[u, v]: res){
		u = label[u], v = label[v];
		if(rng() & 1) swap(u, v);
	}
	shuffle(res.begin(), res.end(), rng);
	return res;
}

int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	auto gen = [&]()->long long{
		return int(rng() % 21) - 10;
	};
	long long l = gen();
	long long r = gen();
	long long v = gen();
	long long s = gen();
	if(l > r){
		swap(l, r);
	}
	if(l == r){
		++ r;
	}
	cout << l << " " << r << " " << v << " " << s << "\n";
	int qn = 100;
	cout << qn << "\n\n";
	for(auto qi = 0; qi < qn; ++ qi){
		int type = rng() % 4;
		cout << type << " ";
		if(type < 2){
			long long l = gen();
			long long r = gen();
			long long v = gen();
			long long s = gen();
			if(l > r){
				swap(l, r);
			}
			cout << l << " " << r << " " << v << " " << s << "\n";
		}
		else if(type == 2){
			vector<array<long long, 2>> piecewise_line;
			while(true){
				piecewise_line.clear();
				for(auto x = l - 3; x <= r + 3; ++ x){
					if(rng() % 2){
						piecewise_line.push_back({x, int(rng() % 11) - 5});
					}
				}
				for(auto i = 0; i < (int)piecewise_line.size() - 1; ++ i){
					auto [x, y] = piecewise_line[i];
					auto [z, w] = piecewise_line[i + 1];
					if((w - y) % (z - x)){
						goto FAIL;
					}
				}
				break;
				FAIL:;
			}
			cout << (int)piecewise_line.size() << "\n";
			for(auto [x, y]: piecewise_line){
				cout << x << " " << y << "\n";
			}
		}
		else{
			long long cl = rng() % (r - l + 1) + l;
			long long cr = rng() % (r - l + 1) + l;
			if(cl > cr){
				swap(cl, cr);
			}
			cout << cl << " " << cr << "\n";
		}
		cout << "\n";
	}
	return 0;
}

/*

*/