#include <bits/stdc++.h>
// #include <x86intrin.h>
using namespace std;
#if __cplusplus >= 202002L
using namespace numbers;
#endif

// B: coordinate type, C: color type
template<class B, class C>
struct colorful_interval_set{
	map<array<B, 2>, C> data;
	colorful_interval_set(C initial_color = {}): data({{{numeric_limits<B>::min(), numeric_limits<B>::max()}, initial_color}}){ }
	colorful_interval_set(const map<array<B, 2>, C> &data): data(data){ assert(is_valid(data)); }
	// is_valid(*this) holds after all operations
	static bool is_valid(const map<array<B, 2>, C> &data){
		if(data.empty() || data.begin()->first[0] != numeric_limits<B>::min() || data.rbegin()->first[1] != numeric_limits<B>::max()) return false;
		for(auto it = data.begin(); next(it) != data.end(); ++ it) if(it->first[1] != next(it)->first[0] || it->second == next(it)->second) return false;
		return true;
	}
	auto belongs(B p){
		return prev(data.upper_bound({p, numeric_limits<B>::max()}));
	}
	// Cover the range [ql, qr) with the color c
	// process(l, r, pc): color of non-empty range [l, r) is changed from pc to c
	// The set of intervals [l, r) accessed by process() forms a partition of [ql, qr) in order of increasing l
	// Amortized O(1) process calls
	optional<typename map<array<B, 2>, C>::iterator>
	cover(B ql, B qr, C c, auto process){
		assert(ql <= qr);
		if(ql == qr) return {};
		array<B, 2> I{ql, ql};
		auto it = data.lower_bound(I);
		if(it != data.begin() && ql < prev(it)->first[1]){
			it = prev(it);
			auto x = *it;
			it = data.erase(it);
			data.insert(it, {{x.first[0], ql}, x.second});
			it = data.insert(it, {{ql, x.first[1]}, x.second});
		}
		while(it != data.end() && it->first[0] < qr){
			if(qr < it->first[1]){
				auto x = *it;
				it = data.erase(it);
				it = data.insert(it, {{x.first[0], qr}, x.second});
				data.insert(next(it), {{qr, x.first[1]}, x.second});
			}
			process(it->first[0], min(qr, it->first[1]), it->second);
			I = {min(I[0], it->first[0]), max(I[1], it->first[1])};
			it = data.erase(it);
		}
		if(it != data.begin() && prev(it)->second == c){
			I[0] = prev(it)->first[0];
			data.erase(prev(it));
		}
		if(it != data.end() && it->second == c){
			I[1] = it->first[1];
			it = data.erase(it);
		}
		return data.insert(it, {I, c});
	}
	optional<typename map<array<B, 2>, C>::iterator>
	cover(B ql, B qr, C c){
		return cover(ql, qr, c, [&](B, B, C){  });
	}
	// new_color(l, r, c): returns the new color for the non-empty range [l, r), previously colored with c
	// The set of intervals [l, r) accessed by new_color() forms a partition of [ql, qr) in order of increasing l
	// O(Number of color ranges affected)
	void recolor(B ql, B qr, auto new_color){
		assert(ql <= qr);
		if(ql == qr) return;
		auto it = data.lower_bound({ql, ql});
		if(it != data.begin() && ql < prev(it)->first[1]){
			it = prev(it);
			auto [inter, c] = *it;
			it = data.erase(it);
			data.insert(it, {{inter[0], ql}, c});
			it = data.insert(it, {{ql, inter[1]}, c});
		}
		while(it != data.end() && it->first[0] < qr){
			if(qr < it->first[1]){
				auto x = *it;
				it = data.erase(it);
				it = data.insert(it, {{x.first[0], qr}, x.second});
				data.insert(next(it), {{qr, x.first[1]}, x.second});
			}
			it->second = new_color(it->first[0], it->first[1], it->second);
			if(it != data.begin() && prev(it)->second == it->second){
				array<B, 2> I{prev(it)->first[0], it->first[1]};
				C c = it->second;
				data.erase(prev(it));
				it = data.erase(it);
				it = data.insert(it, {I, c});
			}
			++ it;
		}
		if(it != data.begin() && it != data.end() && prev(it)->second == it->second){
			array<B, 2> I{prev(it)->first[0], it->first[1]};
			C c = it->second;
			data.erase(prev(it));
			it = data.erase(it);
			it = data.insert(it, {I, c});
		}
	}
	friend ostream &operator<<(ostream &out, const colorful_interval_set &cis){
		out << "{";
		for(auto it = cis.data.begin(); it != cis.data.end(); ++ it){
			auto [inter, c] = *it;
			auto [l, r] = inter;
			out << "[" << l << ", " << r << "){" << c << "}";
			if(next(it) != cis.data.end()) out << ", ";
		}
		return out << "}";
	}
	// new_color(l, r, c, d): returns the new color for the non-empty range [l, r), where s is colored with c and t is colored with d
	// The set of intervals [l, r) accessed by new_color() forms a partition of [INT_MIN, INT_MAX] in order of increasing l
	// O(Number of color ranges affected)
	friend colorful_interval_set merge(const colorful_interval_set &s, const colorful_interval_set &t, auto new_color){
		map<array<B, 2>, C> res;
		for(auto it_s = s.data.begin(), it_t = t.data.begin(); it_s != s.data.end() && it_t != t.data.end(); ){
			B l = max(it_s->first[0], it_t->first[0]), r;
			C c;
			if(it_s->first[1] <= it_t->first[1]){
				r = it_s->first[1];
				if(l == r){
					++ it_s;
					continue;
				}
				c = new_color(l, r, it_s->second, it_t->second);
				++ it_s;
			}
			else{
				r = it_t->first[1];
				if(l == r){
					++ it_t;
					continue;
				}
				c = new_color(l, r, it_s->second, it_t->second);
				++ it_t;
			}
			if(!res.empty() && res.rbegin()->second == c){
				l = res.rbegin()->first[0];
				res.erase(prev(res.end()));
			}
			res.insert(res.end(), {{l, r}, c});
		}
		return res;
	}
};

int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int n, m, nc, qn;
	cin >> n >> m >> nc >> qn;
	vector<colorful_interval_set<int, int>> cis(n);
	vector<vector<int>> ref(n, vector<int>(m));
	auto gen_set = [&]()->vector<map<array<int, 2>, int>>{
		vector<map<array<int, 2>, int>> res(n);
		for(auto i = 0; i < n; ++ i){
			res[i].insert({{numeric_limits<int>::min(), 0}, 0});
			for(auto l = 0; l < m; ){
				int r = l, c = ref[i][l];
				while(r < m && ref[i][r] == c){
					++ r;
				}
				if(res[i].rbegin()->second == c){
					l = res[i].rbegin()->first[0];
					res[i].erase(prev(res[i].end()));
				}
				res[i][{l, r}] = c;
				l = r;
			}
			int l = m, r = numeric_limits<int>::max();
			if(res[i].rbegin()->second == 0){
				l = res[i].rbegin()->first[0];
				res[i].erase(prev(res[i].end()));
			}
			res[i][{l, r}] = 0;
		}
		return res;
	};
	for(auto qi = 0; qi < qn; ++ qi){
		int type;
		cin >> type;
		if(type == 0){
			int i, l, r, c;
			cin >> i >> l >> r >> c;
			int last = l;
			cis[i].cover(l, r, c, [&](int l, int r, int pc){
				assert(last == l);
				assert(l < r);
				last = r;
			});
			assert(last == r);
			for(auto j = l; j < r; ++ j){
				ref[i][j] = c;
			}
		}
		else if(type == 1){
			int i, l, r, shift;
			cin >> i >> l >> r >> shift;
			int last = l;
			cis[i].recolor(l, r, [&](int l, int r, int c){
				assert(last == l);
				assert(l < r);
				last = r;
				return c ? (c + shift) % nc : 0;
			});
			assert(last == r);
			for(auto j = l; j < r; ++ j){
				ref[i][j] = ref[i][j] ? (ref[i][j] + shift) % nc : 0;
			}
		}
		else{
			int i, j, k, shift;
			cin >> i >> j >> k >> shift;
			int last = numeric_limits<int>::min();
			cis[k] = merge(cis[i], cis[j], [&](int l, int r, int c, int d){
				assert(last == l);
				assert(l < r);
				last = r;
				return c || d ? (c + d + shift) % nc : 0;
			});
			assert(last == numeric_limits<int>::max());
			vector<int> res = ref[k];
			for(auto x = 0; x < m; ++ x){
				res[x] = ref[i][x] || ref[j][x] ? (ref[i][x] + ref[j][x] + shift) % nc : 0;
			}
			ref[k] = res;
		}
		auto ref_cis = gen_set();
		for(auto i = 0; i < n; ++ i){
			assert((colorful_interval_set<int, int>::is_valid(cis[i].data)));
			assert(cis[i].data == ref_cis[i]);
		}
	}
	return 0;
}

/*

*/