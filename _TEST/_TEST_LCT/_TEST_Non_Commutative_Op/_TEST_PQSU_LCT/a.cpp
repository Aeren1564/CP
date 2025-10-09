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

template<class data_t, data_t _mod>
struct modular_fixed_base{
#define IS_INTEGRAL(T) (is_integral_v<T> || is_same_v<T, __int128_t> || is_same_v<T, __uint128_t>)
#define IS_UNSIGNED(T) (is_unsigned_v<T> || is_same_v<T, __uint128_t>)
	static_assert(IS_UNSIGNED(data_t));
	static_assert(1 <= _mod && _mod < data_t(1) << 8 * sizeof(data_t) - 1);
	static constexpr bool VARIATE_MOD_FLAG = false;
	static constexpr data_t mod(){
		return _mod;
	}
	template<class T>
	static constexpr vector<modular_fixed_base> precalc_power(T base, int SZ){
		vector<modular_fixed_base> res(SZ + 1, 1);
		for(auto i = 1; i <= SZ; ++ i) res[i] = res[i - 1] * base;
		return res;
	}
	template<class T>
	static constexpr vector<modular_fixed_base> precalc_geometric_sum(T base, int SZ){
		vector<modular_fixed_base> res(SZ + 1);
		for(auto i = 1; i <= SZ; ++ i) res[i] = res[i - 1] * base + base;
		return res;
	}
	static vector<modular_fixed_base> _INV;
	static constexpr void precalc_inverse(int SZ){
		if(_INV.empty()) _INV.assign(2, 1);
		for(auto x = _INV.size(); x <= SZ; ++ x) _INV.push_back(_mod / x * -_INV[_mod % x]);
	}
	// _mod must be a prime
	static modular_fixed_base _primitive_root;
	static constexpr modular_fixed_base primitive_root(){
		if(_primitive_root) return _primitive_root;
		if(_mod == 2) return _primitive_root = 1;
		if(_mod == 998244353) return _primitive_root = 3;
		data_t divs[20] = {};
		divs[0] = 2;
		int cnt = 1;
		data_t x = (_mod - 1) / 2;
		while(x % 2 == 0) x /= 2;
		for(auto i = 3; 1LL * i * i <= x; i += 2){
			if(x % i == 0){
				divs[cnt ++] = i;
				while(x % i == 0) x /= i;
			}
		}
		if(x > 1) divs[cnt ++] = x;
		for(auto g = 2; ; ++ g){
			bool ok = true;
			for(auto i = 0; i < cnt; ++ i){
				if(modular_fixed_base(g).power((_mod - 1) / divs[i]) == 1){
					ok = false;
					break;
				}
			}
			if(ok) return _primitive_root = g;
		}
	}
	constexpr modular_fixed_base(){ }
	constexpr modular_fixed_base(const double &x){ _data = _normalize(llround(x)); }
	constexpr modular_fixed_base(const long double &x){ _data = _normalize(llround(x)); }
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr> constexpr modular_fixed_base(const T &x){ _data = _normalize(x); }
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr> static constexpr data_t _normalize(const T &x){
		int sign = x >= 0 ? 1 : -1;
		data_t v =  _mod <= sign * x ? sign * x % _mod : sign * x;
		if(sign == -1 && v) v = _mod - v;
		return v;
	}
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr> constexpr operator T() const{ return data(); }
	constexpr modular_fixed_base &operator+=(const modular_fixed_base &otr){ if((_data += otr._data) >= _mod) _data -= _mod; return *this; }
	constexpr modular_fixed_base &operator-=(const modular_fixed_base &otr){ if((_data += _mod - otr._data) >= _mod) _data -= _mod; return *this; }
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr> constexpr modular_fixed_base &operator+=(const T &otr){ return *this += modular_fixed_base(otr); }
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr> constexpr modular_fixed_base &operator-=(const T &otr){ return *this -= modular_fixed_base(otr); }
	constexpr modular_fixed_base &operator++(){ return *this += 1; }
	constexpr modular_fixed_base &operator--(){ return *this += _mod - 1; }
	constexpr modular_fixed_base operator++(int){ modular_fixed_base result(*this); *this += 1; return result; }
	constexpr modular_fixed_base operator--(int){ modular_fixed_base result(*this); *this += _mod - 1; return result; }
	constexpr modular_fixed_base operator-() const{ return modular_fixed_base(_mod - _data); }
	constexpr modular_fixed_base &operator*=(const modular_fixed_base &rhs){
		if constexpr(is_same_v<data_t, unsigned int>) _data = (unsigned long long)_data * rhs._data % _mod;
		else if constexpr(is_same_v<data_t, unsigned long long>){
			long long res = _data * rhs._data - _mod * (unsigned long long)(1.L / _mod * _data * rhs._data);
			_data = res + _mod * (res < 0) - _mod * (res >= (long long)_mod);
		}
		else _data = _normalize(_data * rhs._data);
		return *this;
	}
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>
	constexpr modular_fixed_base &inplace_power(T e){
		if(e == 0) return *this = 1;
		if(_data == 0) return *this = {};
		if(_data == 1 || e == 1) return *this;
		if(_data == mod() - 1) return e % 2 ? *this : *this = -*this;
		if(e < 0) *this = 1 / *this, e = -e;
		if(e == 1) return *this;
		modular_fixed_base res = 1;
		for(; e; *this *= *this, e >>= 1) if(e & 1) res *= *this;
		return *this = res;
	}
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>
	constexpr modular_fixed_base power(T e) const{
		return modular_fixed_base(*this).inplace_power(e);
	}
	// c + c * x + ... + c * x^{e-1}
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>
	constexpr modular_fixed_base &inplace_geometric_sum(T e, modular_fixed_base c = 1){
		if(e == 0) return *this = {};
		if(_data == 0) return *this = {};
		if(_data == 1) return *this = c * e;
		if(e == 1) return *this = c;
		if(_data == mod() - 1) return *this = c * abs(e % 2);
		modular_fixed_base res = 0;
		if(e < 0) return *this = geometric_sum(-e + 1, -*this) - 1;
		if(e == 1) return *this = c * *this;
		for(; e; c *= 1 + *this, *this *= *this, e >>= 1) if(e & 1) res += c, c *= *this;
		return *this = res;
	}
	// c + c * x + ... + c * x^{e-1}
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>
	constexpr modular_fixed_base geometric_sum(T e, modular_fixed_base c = 1) const{
		return modular_fixed_base(*this).inplace_geometric_sum(e, c);
	}
	// Returns the minimum integer e>0 with b^e=*this, if it exists
	// O(sqrt(mod)) applications of hashmap
	constexpr optional<data_t> log(const modular_fixed_base &b) const{
		data_t m = mod(), n = sqrtl(m) + 1, j = 1;
		modular_fixed_base e = 1, f = 1;
		unordered_map<data_t, data_t> A;
		while(j <= n && (f = e *= b) != *this) A[(e * *this).data()] = j ++;
		if(e == *this) return j;
		if(gcd(mod(), e.data()) == gcd(mod(), data())) for(auto i = 2; i < n + 2; ++ i) if(A.count((e *= f).data())) return n * i - A[e.data()];
		return {};
	}
	constexpr optional<modular_fixed_base> inverse() const{
		make_signed_t<data_t> a = data(), m = _mod, u = 0, v = 1;
		if(data() < _INV.size()) return _INV[data()];
		while(a){
			make_signed_t<data_t> t = m / a;
			m -= t * a; swap(a, m);
			u -= t * v; swap(u, v);
		}
		if(m != 1) return {};
		return modular_fixed_base{u};
	}
	modular_fixed_base &operator/=(const modular_fixed_base &otr){
		auto inv_ptr = otr.inverse();
		assert(inv_ptr);
		return *this = *this * *inv_ptr;
	}
#define ARITHMETIC_OP(op, apply_op)\
constexpr modular_fixed_base operator op(const modular_fixed_base &x) const{ return modular_fixed_base(*this) apply_op x; }\
template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>\
constexpr modular_fixed_base operator op(const T &x) const{ return modular_fixed_base(*this) apply_op modular_fixed_base(x); }\
template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>\
constexpr friend modular_fixed_base operator op(const T &x, const modular_fixed_base &y){ return modular_fixed_base(x) apply_op y; }
	ARITHMETIC_OP(+, +=) ARITHMETIC_OP(-, -=) ARITHMETIC_OP(*, *=) ARITHMETIC_OP(/, /=)
#undef ARITHMETIC_OP
#define COMPARE_OP(op)\
constexpr bool operator op(const modular_fixed_base &x) const{ return _data op x._data; }\
template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>\
constexpr bool operator op(const T &x) const{ return _data op modular_fixed_base(x)._data; }\
template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>\
constexpr friend bool operator op(const T &x, const modular_fixed_base &y){ return modular_fixed_base(x)._data op y._data; }
	COMPARE_OP(==) COMPARE_OP(!=) COMPARE_OP(<) COMPARE_OP(<=) COMPARE_OP(>) COMPARE_OP(>=)
#undef COMPARE_OP
	friend istream &operator>>(istream &in, modular_fixed_base &number){
		long long x;
		in >> x;
		number._data = modular_fixed_base::_normalize(x);
		return in;
	}
	friend ostream &operator<<(ostream &out, const modular_fixed_base &number){
		out << number._data;
#ifdef LOCAL
		cerr << "(";
		for(auto d = 1; ; ++ d){
			if((number * d)._data <= 1000000){
				cerr << (number * d)._data;
				if(d != 1) cerr << "/" << d;
				break;
			}
			else if((-number * d)._data <= 1000000){
				cerr << "-" << (-number * d)._data;
				if(d != 1) cerr << "/" << d;
				break;
			}
		}
		cerr << ")";
#endif
		return out;
	}
	data_t _data = 0;
	constexpr data_t data() const{ return _data; }
#undef IS_INTEGRAL
#undef IS_UNSIGNED
};
template<class data_t, data_t _mod> vector<modular_fixed_base<data_t, _mod>> modular_fixed_base<data_t, _mod>::_INV;
template<class data_t, data_t _mod> modular_fixed_base<data_t, _mod> modular_fixed_base<data_t, _mod>::_primitive_root;

constexpr unsigned int mod = (119 << 23) + 1; // 998244353
// constexpr unsigned int mod = 1e9 + 7; // 1000000007
// constexpr unsigned int mod = 1e9 + 9; // 1000000009
// constexpr unsigned long long mod = (unsigned long long)1e18 + 9;
using modular = modular_fixed_base<decay_t<decltype(mod)>, mod>;

constexpr modular operator""_m(const char *x){
	modular res = 0;
	long long buffer = 0;
	long long buffer_width = 1;
	constexpr long long buffer_th = 1'000'000'000'000'000'000LL;
	while(*x){
		#ifdef LOCAL
		assert(isdigit(*x));
		#endif
		buffer = buffer * 10 + (*(x ++) - '0');
		if((buffer_width *= 10) == buffer_th){
			res = buffer_width * res + buffer;
			buffer = 0;
			buffer_width = 1;
		}
	}
	res = buffer_width * res + buffer;
	return res;
}

template<class T, size_t N, size_t M>
struct matrix_fixed_base{
	int n, m;
	array<array<T, M>, N> data;
	array<T, M> &operator[](int i){
		assert(0 <= i && i < n);
		return data[i];
	}
	const array<T, M> &operator[](int i) const{
		assert(0 <= i && i < n);
		return data[i];
	}
	matrix_fixed_base &inplace_slice(int il, int ir, int jl, int jr){
		assert(0 <= il && il <= ir && ir <= n);
		assert(0 <= jl && jl <= jr && jr <= m);
		n = ir - il, m = jr - jl;
		if(il > 0) for(auto i = 0; i < n; ++ i) swap(data[i], data[il + i]);
		data.resize(n);
		for(auto &row: data){
			row.erase(row.begin(), row.begin() + jl);
			row.resize(m);
		}
		return *this;
	}
	matrix_fixed_base slice(int il, int ir, int jl, int jr) const{
		return matrix_fixed_base(*this).inplace_slice(il, ir, jl, jr);
	}
	matrix_fixed_base &inplace_row_slice(int il, int ir){
		assert(0 <= il && il <= ir && ir <= n);
		n = ir - il;
		if(il > 0) for(auto i = 0; i < n; ++ i) swap(data[i], data[il + i]);
		data.resize(n);
		return *this;
	}
	matrix_fixed_base row_slice(int il, int ir) const{
		return matrix_fixed_base(*this).inplace_row_slice(il, ir);
	}
	matrix_fixed_base &inplace_column_slice(int jl, int jr){
		assert(0 <= jl && jl <= jr && jr <= m);
		m = jr - jl;
		for(auto &row: data){
			row.erase(row.begin(), row.begin() + jl);
			row.resize(m);
		}
		return *this;
	}
	matrix_fixed_base column_slice(int jl, int jr) const{
		return matrix_fixed_base(*this).inplace_column_slice(jl, jr);
	}
	bool operator==(const matrix_fixed_base &a) const{
		assert(n == a.n && m == a.m);
		return data == a.data;
	}
	bool operator!=(const matrix_fixed_base &a) const{
		assert(n == a.n && m == a.m);
		return data != a.data;
	}
	matrix_fixed_base &operator+=(const matrix_fixed_base &a){
		assert(n == a.n && m == a.m);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] += a[i][j];
		return *this;
	}
	matrix_fixed_base operator+(const matrix_fixed_base &a) const{
		return matrix_fixed_base(*this) += a;
	}
	matrix_fixed_base &operator-=(const matrix_fixed_base &a){
		assert(n == a.n && m == a.m);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] -= a[i][j];
		return *this;
	}
	matrix_fixed_base operator-(const matrix_fixed_base &a) const{
		return matrix_fixed_base(*this) -= a;
	}
	matrix_fixed_base operator*=(const matrix_fixed_base &a){
		assert(m == a.n);
		int l = a.m;
		matrix_fixed_base res(n, l);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) for(auto k = 0; k < l; ++ k) res[i][k] += data[i][j] * a[j][k];
		return *this = res;
	}
	matrix_fixed_base operator*(const matrix_fixed_base &a) const{
		return matrix_fixed_base(*this) *= a;
	}
	matrix_fixed_base &operator*=(T c){
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] *= c;
		return *this;
	}
	matrix_fixed_base operator*(T c) const{
		return matrix_fixed_base(*this) *= c;
	}
	friend matrix_fixed_base operator*(T c, matrix_fixed_base a){
		for(auto i = 0; i < a.n; ++ i) for(auto j = 0; j < a.m; ++ j) a[i][j] = c * a[i][j];
		return a;
	}
	template<class U, typename enable_if<is_integral<U>::value>::type* = nullptr>
	matrix_fixed_base &inplace_power(U e){
		assert(n == m && e >= 0);
		matrix_fixed_base res(n, n, T{1});
		for(; e; *this *= *this, e >>= 1) if(e & 1) res *= *this;
		return *this = res;
	}
	template<class U>
	matrix_fixed_base power(U e) const{
		return matrix_fixed_base(*this).inplace_power(e);
	}
	matrix_fixed_base &inplace_transpose(){
		assert(n == m);
		for(auto i = 0; i < n; ++ i) for(auto j = i + 1; j < n; ++ j) swap(data[i][j], data[j][i]);
		return *this;
	}
	matrix_fixed_base transpose() const{
		if(n == m) return matrix_fixed_base(*this).inplace_transpose();
		matrix_fixed_base res(m, n);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) res[j][i] = data[i][j];
		return res;
	}
	vector<T> operator*(const vector<T> &v) const{
		assert(m == (int)v.size());
		vector<T> res(n, T{0});
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) res[i] += data[i][j] * v[j];
		return res;
	}
	friend vector<T> operator*(const vector<T> &v, const matrix_fixed_base &a){
		vector<T> res(a.m, T{0});
		for(auto i = 0; i < a.n; ++ i) for(auto j = 0; j < a.m; ++ j) res[j] += v[i] * a[i][j];
		return res;
	}
	// Assumes T is either a floating, integral, or a modular type.
	// If T is a floating type, O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Otherwise, O(n * up_to * log(size)) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base &, T, int> inplace_REF(int up_to = -1){
		if(n == 0) return {*this, T{1}, 0};
		if(!~up_to) up_to = m;
		T det = 1;
		int rank = 0;
		for(auto j = 0; j < up_to; ++ j){
			if constexpr(is_floating_point_v<T>){
				static const T eps = 1e-9;
				int pivot = rank;
				for(auto i = rank + 1; i < n; ++ i) if(abs(data[pivot][j]) < abs(data[i][j])) pivot = i;
				if(rank != pivot){
					swap(data[rank], data[pivot]);
					det *= -1;
				}
				if(abs(data[rank][j]) <= eps) continue;
				det *= data[rank][j];
				T inv = 1 / data[rank][j];
				for(auto i = rank + 1; i < n; ++ i) if(abs(data[i][j]) > eps){
					T coef = data[i][j] * inv;
					for(auto k = j; k < m; ++ k) data[i][k] -= coef * data[rank][k];
				}
				++ rank;
			}
			else{
				for(auto i = rank + 1; i < n; ++ i) while(data[i][j]){
					T q;
					if constexpr(is_integral_v<T> || is_same_v<T, __int128_t> || is_same_v<T, __uint128_t>) q = data[rank][j] / data[i][j];
					else q = data[rank][j].data / data[i][j].data;
					if(q) for(auto k = j; k < m; ++ k) data[rank][k] -= q * data[i][k];
					swap(data[rank], data[i]);
					det *= -1;
				}
				if(rank == j) det *= data[rank][j];
				else det = T(0);
				if(data[rank][j]) ++ rank;
			}
			if(rank == n) break;
		}
		return {*this, det, rank};
	}
	// Assumes T is either a floating, integral, or a modular type.
	// If T is a floating type, O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Otherwise, O(n * up_to * log(size)) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base, T, int> REF(int up_to = -1) const{
		return matrix_fixed_base(*this).inplace_REF(up_to);
	}
	// Assumes T is a field.
	// O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base &, T, int> inplace_REF_field(int up_to = -1){
		if(n == 0) return {*this, T{1}, 0};
		if(!~up_to) up_to = m;
		T det = T{1};
		int rank = 0;
		for(auto j = 0; j < up_to; ++ j){
			int pivot = -1;
			for(auto i = rank; i < n; ++ i) if(data[i][j] != T(0)){
				pivot = i;
				break;
			}
			if(!~pivot){
				det = T(0);
				continue;
			}
			if(rank != pivot){
				swap(data[rank], data[pivot]);
				det *= -1;
			}
			det *= data[rank][j];
			T inv = 1 / data[rank][j];
			for(auto i = rank + 1; i < n; ++ i) if(data[i][j] != T(0)){
				T coef = data[i][j] * inv;
				for(auto k = j; k < m; ++ k) data[i][k] -= coef * data[rank][k];
			}
			++ rank;
			if(rank == n) break;
		}
		return {*this, det, rank};
	}
	// Assumes T is a field.
	// O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base, T, int> REF_field(int up_to = -1) const{
		return matrix_fixed_base(*this).inplace_REF_field(up_to);
	}
	// Assumes T is a field.
	// O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base &, T, int> inplace_RREF_field(int up_to = -1){
		if(n == 0) return {*this, T{1}, 0};
		auto [mat, det, rank] = inplace_REF_field(up_to);
		for(auto i = rank - 1; i >= 0; -- i){
			int pivot = find_if(mat[i].begin(), mat[i].end(), [&](const T &x){ return x != T{0}; }) - mat[i].begin();
			T inv = T{1} / mat[i][pivot];
			for(auto t = 0; t < i; ++ t){
				T coef = mat[t][pivot] * inv;
				for(auto j = 0; j < m; ++ j) mat[t][j] -= coef * mat[i][j];
			}
		}
		return {mat, det, rank};
	}
	// Assumes T is a field.
	// O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base, T, int> RREF_field(int up_to = -1) const{
		return matrix_fixed_base(*this).inplace_RREF_field(up_to);
	}
	// Assumes T is either a floating, integral, or a modular type.
	// If T is a floating type, O(n) divisions with O(n^3) additions, subtractions, and multiplications.
	// Otherwise, O(n^2 * log(size)) divisions with O(n^3) additions, subtractions, and multiplications.
	T determinant() const{
		assert(n == m);
		return get<1>(REF());
	}
	// Assumes T is a field.
	// O(n) divisions with O(n^3) additions, subtractions, and multiplications.
	T determinant_field() const{
		assert(n == m);
		return get<1>(REF_field());
	}
	// Assumes T is either a floating, integral, or a modular type.
	// If T is a floating type, O(n) divisions with O(n^3) additions, subtractions, and multiplications.
	// Otherwise, O(n^2 * log(size)) divisions with O(n^3) additions, subtractions, and multiplications.
	int rank() const{
		return get<2>(REF());
	}
	// Assumes T is a field.
	// O(n) divisions with O(n^3) additions, subtractions, and multiplications.
	int rank_field() const{
		return get<2>(REF_field());
	}
	// Regarding the matrix as a system of linear equations by separating first m-1 columns,
	// find a solution of the system along with the basis for the nullspace
	// Assumes T is a field
	// O(n * m^2)
	optional<pair<vector<T>, vector<vector<T>>>> solve_right() const{
		assert(m >= 1);
		auto [rref, _, rank] = RREF_field(m - 1);
		for(auto i = rank; i < n; ++ i) if(rref[i][m - 1] != T{0}) return {};
		vector<T> res(m - 1);
		vector<int> pivot(rank), appear_as_pivot(m - 1);
		for(auto i = rank - 1; i >= 0; -- i){
			pivot[i] = find_if(rref[i].begin(), rref[i].end(), [&](const T &x){ return x != T{0}; }) - rref[i].begin();
			assert(pivot[i] < m - 1);
			appear_as_pivot[pivot[i]] = true;
			res[pivot[i]] = rref[i][m - 1] / rref[i][pivot[i]];
		}
		vector<vector<T>> basis;
		for(auto j = 0; j < m - 1; ++ j){
			if(appear_as_pivot[j]) continue;
			vector<T> b(m - 1);
			b[j] = T{1};
			for(auto i = 0; i < rank; ++ i){
				if(rref[i][j] == T{0}) continue;
				b[pivot[i]] = -rref[i][j] / rref[i][pivot[i]];
			}
			basis.push_back(b);
		}
		return pair{res, basis};
	}
	// Assumes T is a field.
	// O(n) divisions with O(n^3) additions, subtractions, and multiplications.
	optional<matrix_fixed_base> inverse() const{
		assert(n == m);
		if(n == 0) return *this;
		auto a = data;
		auto res = multiplicative_identity(n, m);
		for(auto j = 0; j < n; ++ j){
			int rank = j, pivot = -1;
			if constexpr(is_floating_point_v<T>){
				static const T eps = 1e-9;
				pivot = rank;
				for(auto i = rank + 1; i < n; ++ i) if(abs(a[pivot][j]) < abs(a[i][j])) pivot = i;
				if(abs(a[pivot][j]) <= eps) return {};
			}
			else{
				for(auto i = rank; i < n; ++ i) if(a[i][j] != T(0)){
					pivot = i;
					break;
				}
				if(!~pivot) return {};
			}
			swap(a[rank], a[pivot]), swap(res[rank], res[pivot]);
			T inv = 1 / a[rank][j];
			for(auto k = 0; k < n; ++ k) a[rank][k] *= inv, res[rank][k] *= inv;
			for(auto i = 0; i < n; ++ i){
				if constexpr(is_floating_point_v<T>){
					static const T eps = 1e-9;
					if(i != rank && abs(a[i][j]) > eps){
						T d = a[i][j];
						for(auto k = 0; k < n; ++ k) a[i][k] -= d * a[rank][k], res[i][k] -= d * res[rank][k];
					}
				}
				else if(i != rank && a[i][j] != T(0)){
					T d = a[i][j];
					for(auto k = 0; k < n; ++ k) a[i][k] -= d * a[rank][k], res[i][k] -= d * res[rank][k];
				}
			}
		}
		return res;
	}
	// O(n * 2^n)
	T permanent() const{
		assert(n <= 30 && n == m);
		T perm = n ? 0 : 1;
		array<T, N> sum;
		sum.fill(T{0});
		for(auto order = 1; order < 1 << n; ++ order){
			int j = __lg(order ^ order >> 1 ^ order - 1 ^ order - 1 >> 1), sign = (order ^ order >> 1) & 1 << j ? 1 : -1;
			T prod = order & 1 ? -1 : 1;
			if((order ^ order >> 1) & 1 << j) for(auto i = 0; i < n; ++ i) prod *= sum[i] += data[i][j];
			else for(auto i = 0; i < n; ++ i) prod *= sum[i] -= data[i][j];
			perm += prod;
		}
		return perm * (n & 1 ? -1 : 1);
	}
	template<class output_stream>
	friend output_stream &operator<<(output_stream &out, const matrix_fixed_base &a){
		out << "\n";
		for(auto i = 0; i < a.n; ++ i){
			for(auto j = 0; j < a.m; ++ j) out << a[i][j] << " ";
			out << "\n";
		}
		return out;
	}
	matrix_fixed_base(int n, int m, T init_diagonal = T{0}, T init_off_diagonal = T{0}): n(n), m(m){
		assert(0 <= n && n <= N && 0 <= m && m <= M);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] = i == j ? init_diagonal : init_off_diagonal;
	}
	matrix_fixed_base(int n, int m, const array<array<T, M>, N> &a): n(n), m(m), data(a){ assert(0 <= n && n <= N && 0 <= m && m <= M); }
	matrix_fixed_base(int n, int m, const array<T, N * M> &a): n(n), m(m){
		assert(0 <= n && n <= N && 0 <= m && m <= M);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] = a[m * i + j];
	}
	static matrix_fixed_base additive_identity(int n, int m){
		return matrix_fixed_base(n, m, T{0}, T{0});
	}
	static matrix_fixed_base multiplicative_identity(int n, int m){
		return matrix_fixed_base(n, m, T{1}, T{0});
	}
};

template<class T>
using matrix = matrix_fixed_base<T, 2, 2>;

template<bool HAS_PATH_QUERY, bool HAS_PATH_UPDATE, bool HAS_SUBTREE_QUERY, bool HAS_SUBTREE_UPDATE, bool IS_COMMUTATIVE, class T, class U, class F1, class F2, class F3, class F4, class F5, class F6>
struct link_cut_trees_base{
#ifdef LOCAL
	#define ASSERT(x) assert(x)
#else
	#define ASSERT(x) 42
#endif
#define ifPQ if constexpr(HAS_PATH_QUERY)
#define ifPU if constexpr(HAS_PATH_UPDATE)
#define ifSQ if constexpr(HAS_SUBTREE_QUERY)
#define ifSU if constexpr(HAS_SUBTREE_UPDATE)
#define ifNC if constexpr(!IS_COMMUTATIVE)
#define ifPUSU if constexpr(HAS_PATH_UPDATE || HAS_SUBTREE_UPDATE)
	// If there is path update and subtree query, it needs path aggregation to do lazy propagation
	static_assert(HAS_PATH_QUERY || !HAS_PATH_UPDATE || !HAS_SUBTREE_QUERY);
	// If there is subtree query, T has to be commutative and invertible
	static_assert(!HAS_SUBTREE_QUERY || IS_COMMUTATIVE);
	vector<int> size, lazy_flip, pv, left, right;
	vector<T> data;
	vector<T> aux_data; // aggregation of data in the subtree in the auxiliary splay tree, aggregates in fixed order
	vector<T> virtual_data; // aggregation of subtr data of virtual childs
	vector<T> subtr_data; // aggregation of data in the subtree in the auxiliary splay tree along with their virtual data
	vector<U> aux_lazy; // update splay subtree
	vector<U> virtual_lazy; // update virtual childs
	vector<U> subtr_lazy; // update splay subtree along with their virtual childs
	F1 TT; // monoid operation (always adjacent)
	T T_id; // monoid identity
	F2 Tinv; // group inverse
	F3 Tflip; // flip the operation order
	F4 UU; // monoid operation (superset, subset)
	U U_id; // monoid identity
	F5 Uinv; // group inverse
	F6 UT; // action of U on T (superset, subset)
	link_cut_trees_base(F1 TT, T T_id, F2 Tinv, F3 Tflip, F4 UU, U U_id, F5 Uinv, F6 UT): TT(TT), T_id(T_id), Tinv(Tinv), Tflip(Tflip), UU(UU), U_id(U_id), Uinv(Uinv), UT(UT){ }
	void _apply_aux(int u, const U &f){
		static_assert(HAS_PATH_UPDATE);
		ASSERT(0 <= u && u < (int)data.size());
		data[u] = UT(f, data[u]);
		aux_lazy[u] = UU(f, aux_lazy[u]);
		ifPQ{
			T x = UT(f, aux_data[u]);
			ifSQ subtr_data[u] = TT(x, TT(subtr_data[u], Tinv(aux_data[u])));
			aux_data[u] = x;
		}
	}
	void _apply_subtr(int u, const U &f){
		static_assert(HAS_SUBTREE_UPDATE);
		ASSERT(0 <= u && u < (int)data.size());
		data[u] = UT(f, data[u]);
		ifPQ aux_data[u] = UT(f, aux_data[u]);
		ifSQ{
			virtual_data[u] = UT(f, virtual_data[u]);
			subtr_data[u] = UT(f, subtr_data[u]);
		}
		virtual_lazy[u] = UU(f, virtual_lazy[u]);
		subtr_lazy[u] = UU(f, subtr_lazy[u]);
	}
	void _apply_flip(int u){
		ASSERT(0 <= u && u < (int)data.size());
		lazy_flip[u] ^= 1;
		ifNC aux_data[u] = Tflip(aux_data[u]);
		swap(left[u], right[u]);
	}
	template<bool sign>
	void _apply_virtual(int u, int v){
		static_assert(HAS_SUBTREE_QUERY || HAS_SUBTREE_UPDATE);
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size());
		if constexpr(sign == 0){
			ifSQ virtual_data[u] = TT(virtual_data[u], subtr_data[v]);
			ifSU _apply_subtr(v, Uinv(virtual_lazy[u]));
		}
		else{
			ifSU _apply_subtr(v, virtual_lazy[u]);
			ifSQ virtual_data[u] = TT(virtual_data[u], Tinv(subtr_data[v]));
		}
	}
	void _push(int u){
		ASSERT(0 <= u && u < (int)data.size());
		ifPU if(aux_lazy[u] != U_id){
			if(~left[u]) _apply_aux(left[u], aux_lazy[u]);
			if(~right[u]) _apply_aux(right[u], aux_lazy[u]);
			aux_lazy[u] = U_id;
		}
		ifSU{
			if(subtr_lazy[u] != U_id){
				if(~left[u]) _apply_subtr(left[u], subtr_lazy[u]);
				if(~right[u]) _apply_subtr(right[u], subtr_lazy[u]);
				subtr_lazy[u] = U_id;
			}
		}
		if(lazy_flip[u]){
			if(~left[u]) _apply_flip(left[u]);
			if(~right[u]) _apply_flip(right[u]);
			lazy_flip[u] = false;
		}
	}
	void _refresh(int u){
		ASSERT(0 <= u && u < (int)data.size());
		ifPU ASSERT(aux_lazy[u] == U_id);
		ifSU ASSERT(subtr_lazy[u] == U_id);
		size[u] = 1 + _internal_size(left[u]) + _internal_size(right[u]);
		ifPQ aux_data[u] = data[u];
		ifSQ subtr_data[u] = TT(data[u], virtual_data[u]);
		if(auto v = left[u]; ~v){
			ifPQ aux_data[u] = TT(aux_data[v], aux_data[u]);
			ifSQ subtr_data[u] = TT(subtr_data[u], subtr_data[v]);
		}
		if(auto w = right[u]; ~w){
			ifPQ aux_data[u] = TT(aux_data[u], aux_data[w]);
			ifSQ subtr_data[u] = TT(subtr_data[u], subtr_data[w]);
		}
	}
	int _dir(int u){
		ASSERT(0 <= u && u < (int)data.size());
		if(!~pv[u]) return -2; // root of its splay tree which contains LCT component root
		if(left[pv[u]] == u) return 0; // left child
		if(right[pv[u]] == u) return 1; // right child
		return -1; // root of its splay tree which does not contain LCT component root
	}
	bool _is_auxiliary_root(int u){
		ASSERT(0 <= u && u < (int)data.size());
		return _dir(u) < 0;
	}
	void _set_link(int u, int v, int d){
		ASSERT(-1 <= min(u, v) && max(u, v) < (int)data.size());
		if(~v) pv[v] = u;
		if(d >= 0) (d == 0 ? left : right)[u] = v;
	}
	// Assumes p and p->p propagated
	void _rotate(int u){
		ASSERT(0 <= u && u < (int)data.size() && !_is_auxiliary_root(u));
		int x = _dir(u), g = pv[u];
		_set_link(pv[g], u, _dir(g));
		_set_link(g, x == 1 ? left[u] : right[u], x);
		_set_link(u, g, x ^ 1);
		_refresh(g);
	}
	// Bring the node to the top
	void _splay(int u){
		ASSERT(0 <= u && u < (int)data.size());
		for(; !_is_auxiliary_root(u) && !_is_auxiliary_root(pv[u]); _rotate(u)){
			_push(pv[pv[u]]), _push(pv[u]), _push(u);
			_dir(u) == _dir(pv[u]) ? _rotate(pv[u]) : _rotate(u);
		}
		if(!_is_auxiliary_root(u)) _push(pv[u]), _push(u), _rotate(u);
		_push(u), _refresh(u);
	}
	int _internal_size(int u){
		ASSERT(-1 <= u && u < (int)data.size());
		return ~u ? size[u] : 0;
	}
	// Put u on the preferred path then splay it (right subtree is empty)
	void _access(int u){
		ASSERT(0 <= u && u < (int)data.size());
		for(auto v = u, p = -1; ~v; v = pv[p = v]){
			_splay(v);
			if constexpr(HAS_SUBTREE_QUERY || HAS_SUBTREE_UPDATE){
				if(~p) _apply_virtual<1>(v, p);
				if(~right[v]) _apply_virtual<0>(v, right[v]);
			}
			right[v] = p;
			_refresh(v);
		}
		_splay(u);
		ASSERT(!~right[u]);
	}
	void build(int n){
		ASSERT(0 <= n);
		build(vector<T>(n, T_id));
	}
	void build(int n, T init){
		ASSERT(0 <= n);
		build(vector<T>(n, init));
	}
	template<class V>
	void build(const vector<V> &a){
		int n = (int)a.size();
		size.assign(n, 1);
		lazy_flip.assign(n, false);
		pv.assign(n, -1);
		left.assign(n, -1);
		right.assign(n, -1);
		data = vector<T>(a.begin(), a.end());
		ifPQ aux_data = vector<T>(a.begin(), a.end());
		ifSQ{
			virtual_data.assign(n, T_id);
			subtr_data = data;
		}
		ifPU aux_lazy.assign(n, U_id);
		ifSU{
			virtual_lazy.assign(n, U_id);
			subtr_lazy.assign(n, U_id);
		}
	}
	int new_node(const T &x){
		size.push_back(1);
		lazy_flip.push_back(false);
		pv.push_back(-1);
		left.push_back(-1);
		right.push_back(-1);
		data.push_back(x);
		ifPQ aux_data.push_back(x);
		ifSQ{
			virtual_data.push_back(T_id);
			subtr_data.push_back(x);
		}
		ifPU aux_lazy.push_back(U_id);
		ifSU{
			virtual_lazy.push_back(U_id);
			subtr_lazy.push_back(U_id);
		}
		return (int)data.size() - 1;
	}
	// Make u the root of its connected component
	void reroot(int u){
		ASSERT(0 <= u && u < (int)data.size());
		_access(u), _apply_flip(u), _access(u);
		ASSERT(!~left[u] && !~right[u]);
	}
	int root_of(int u){
		ASSERT(0 <= u && u < (int)data.size());
		for(_access(u); ~left[u]; _push(u)) u = left[u];
		return _access(u), u;
	}
	// If u is a non-root vertex in its component, return its parent
	// Otherwise, return -1
	int parent_or_is_root(int u){
		ASSERT(0 <= u && u < (int)data.size());
		_access(u);
		if(!~left[u]) return -1;
		for(_push(u = left[u]); ~right[u]; _push(u)) u = right[u];
		return _access(u), u;
	}
	// If u and v are in the same component, find the lca
	// Otherwise, return -1
	int lca_or_disconnected(int u, int v){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size());
		if(u == v) return u;
		_access(u), _access(v);
		if(!~pv[u]) return -1;
		_splay(u);
		return ~pv[u] ? pv[u] : u;
	}
	bool adjacent(int u, int v){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size());
		if(u == v) return false;
		int w = lca_or_disconnected(u, v);
		if(!~w || u != w && v != w) return false;
		return u != w ? w == parent_or_is_root(u) : w == parent_or_is_root(v);
	}
	int depth(int u){
		ASSERT(0 <= u && u < (int)data.size());
		_access(u);
		return _internal_size(left[u]);
	}
	template<bool RESTORE_ROOT = true>
	int distance(int u, int v){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v));
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(u), _access(v);
		int res = _internal_size(left[v]);
		if constexpr(RESTORE_ROOT) reroot(init_root);
		return res;
	}
	bool connected(int u, int v){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size());
		if(u == v) return true;
		_access(u), _access(v);
		return ~pv[u];
	}
	// Returns the k-th ancestor on the path to root
	int find_ancestor_by_order(int u, int k){
		ASSERT(0 <= u && u < (int)data.size() && 0 <= k);
		k = depth(u) - k;
		ASSERT(k >= 0);
		for(; ; _push(u)){
			int size = _internal_size(left[u]);
			if(size == k) return _access(u), u;
			if(size < k) k -= size + 1, u = right[u];
			else u = left[u];
		}
		ASSERT(false);
	}
	// Returns the k-th vertex on the u-v path
	template<bool RESTORE_ROOT = true>
	int find_vertex_by_order(int u, int v, int k){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v) && 0 <= k);
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(v);
		int res = find_ancestor_by_order(u, k);
		if constexpr(RESTORE_ROOT) reroot(init_root);
		return res;
	}
	// Make u the parent of v
	void link(int u, int v){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && !connected(u, v));
		reroot(v), _access(u), _set_link(v, u, 0), _refresh(v);
	}
	void cut_from_parent(int u){
		ASSERT(0 <= u && u < (int)data.size());
		_access(u);
		ASSERT(~left[u]); // Assumes u is not the root of its component
		left[u] = pv[left[u]] = -1;
		_refresh(u);
	}
	// Assumes u and v are adjacent in tree
	void cut(int u, int v){
		ASSERT(adjacent(u, v));
		cut_from_parent(depth(u) > depth(v) ? u : v);
	}
	T query(int u){
		ASSERT(0 <= u && u < (int)data.size());
		ifPUSU _access(u);
		return data[u];
	}
	template<bool RESTORE_ROOT = true>
	T query_path(int u, int v){
		static_assert(HAS_PATH_QUERY);
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v));
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(u), _access(v);
		T res = aux_data[v];
		if constexpr(RESTORE_ROOT) reroot(init_root);
		return res;
	}
	T query_subtree(int u){
		static_assert(HAS_SUBTREE_QUERY);
		ASSERT(0 <= u && u < (int)data.size());
		int v = parent_or_is_root(u);
		if(~v) cut_from_parent(u);
		T res = subtr_data[u];
		if(~v) link(v, u);
		return res;
	}
	void set(int u, const T &x){
		ASSERT(0 <= u && u < (int)data.size());
		_access(u);
		data[u] = x;
		_refresh(u);
	}
	void update(int u, const U &f){
		static_assert(HAS_PATH_UPDATE || HAS_SUBTREE_UPDATE);
		ASSERT(0 <= u && u < (int)data.size());
		_access(u);
		data[u] = UT(f, data[u]);
		_refresh(u);
	}
	template<bool RESTORE_ROOT = true>
	void update_path(int u, int v, const U &f){
		static_assert(HAS_PATH_UPDATE);
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v));
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(u), _access(v), _apply_aux(v, f);
		if constexpr(RESTORE_ROOT) reroot(init_root);
	}
	void update_subtree(int u, const U &f){
		static_assert(HAS_SUBTREE_UPDATE);
		ASSERT(0 <= u && u < (int)data.size());
		int v = parent_or_is_root(u);
		if(~v) cut_from_parent(u);
		_apply_subtr(u, f);
		if(~v) link(v, u);
	}
	// Let the data on the u-v path be represented by an array A
	// A must be sorted by pred
	// Returns the r where everything in A[0, r) evaluates to true, and A[r, len(A)) evalutes to false
	template<bool RESTORE_ROOT = true>
	int partition_point(int u, int v, auto pred){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v));
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(u), _access(v);
		int res = 0;
		while(true){
			_push(v);
			if(pred(data[v])){
				res += _internal_size(left[v]) + 1;
				if(!~right[v]){
					_splay(v);
					break;
				}
				v = right[v];
			}
			else{
				if(!~left[v]){
					_splay(v);
					break;
				}
				v = left[v];
			}
		}
		if constexpr(RESTORE_ROOT) reroot(init_root);
		return res;
	}
	// Let the data on the u-v path be represented by an array A
	// Assumes pred(A[0, r)) is T, ..., T, F, ..., F for 0 <= r <= len(A)
	// Returns max r with T
	template<bool RESTORE_ROOT = true>
	int max_pref(int u, int v, auto pred){
		static_assert(HAS_PATH_QUERY);
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v) && pred(T_id));
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(u);
		int n = depth(v) + 1;
		if(pred(aux_data[v])){
			if constexpr(RESTORE_ROOT) reroot(init_root);
			return n;
		}
		T sum = T_id;
		auto recurse = [&](auto self, int u, int l)->int{
			if(!~u) return n;
			if(auto x = TT(sum, aux_data[u]); pred(x)){
				sum = x;
				return n;
			}
			_push(u);
			if(auto p = self(self, left[u], l); p < n) return p;
			l += _internal_size(left[u]);
			if(!pred(sum = TT(sum, data[u]))){
				_splay(u);
				return l;
			}
			return self(self, right[u], l + 1);
		};
		int res = recurse(recurse, v, 0);
		if constexpr(RESTORE_ROOT) reroot(init_root);
		return res;
	}
#undef ASSERT
#undef ifPQ
#undef ifPU
#undef ifSQ
#undef ifSU
#undef ifNC
#undef ifPUSU
};

template<class T>
auto make_LCT(){
	using U = int;
	auto TT = [&](){ assert(false); };
	using F1 = decltype(TT);
	T T_id = {};
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	auto UU = [&](){ assert(false); };
	using F4 = decltype(UU);
	U U_id = {};
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	auto UT = [&](){ assert(false); };
	using F6 = decltype(UT);
	return link_cut_trees_base<false, false, false, false, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path query
// IS_COMMUTATIVE = true results in slightly better constant factor, Tflip is totally ignored in such case
template<bool IS_COMMUTATIVE, class T, class F1, class F3>
auto make_PQ_LCT(F1 TT, T T_id, F3 Tflip){
	using U = int;
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto UU = [&](){ assert(false); };
	using F4 = decltype(UU);
	U U_id = {};
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	auto UT = [&](){ assert(false); };
	using F6 = decltype(UT);
	return link_cut_trees_base<true, false, false, false, IS_COMMUTATIVE, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path update
template<class T, class U, class F4, class F6>
auto make_PU_LCT(F4 UU, U U_id, F6 UT){
	auto TT = [&](){ assert(false); };
	using F1 = decltype(TT);
	T T_id = {};
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	return link_cut_trees_base<false, true, false, false, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - subtree query (commutative & invertible)
template<class T, class F1, class F2>
auto make_SQ_LCT(F1 TT, T T_id, F2 Tinv){
	using U = int;
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	auto UU = [&](){ assert(false); };
	using F4 = decltype(UU);
	U U_id = {};
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	auto UT = [&](){ assert(false); };
	using F6 = decltype(UT);
	return link_cut_trees_base<false, false, true, false, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports:
// - subtree update (commutative & invertible)
template<class T, class U, class F4, class F5, class F6>
auto make_SU_LCT(F4 UU, U U_id, F5 Uinv, F6 UT){
	auto TT = [&](){ assert(false); };
	using F1 = decltype(TT);
	T T_id = {};
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	return link_cut_trees_base<false, false, false, true, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path query
// - path update
// IS_COMMUTATIVE = true results in slightly better constant factor, Tflip is totally ignored in such case
template<bool IS_COMMUTATIVE, class T, class U, class F1, class F3, class F4, class F6>
auto make_PQPU_LCT(F1 TT, T T_id, F3 Tflip, F4 UU, U U_id, F6 UT){
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	return link_cut_trees_base<true, true, false, false, IS_COMMUTATIVE, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path + subtree query (commutative & invertible)
template<class T, class F1, class F2>
auto make_PQSQ_LCT(F1 TT, T T_id, F2 Tinv){
	using U = int;
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	auto UU = [&](){ assert(false); };
	using F4 = decltype(UU);
	U U_id = {};
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	auto UT = [&](){ assert(false); };
	using F6 = decltype(UT);
	return link_cut_trees_base<true, false, true, false, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path query
// - subtree update (commutative & invertible)
// IS_COMMUTATIVE = true results in slightly better constant factor, Tflip is totally ignored in such case
template<bool IS_COMMUTATIVE, class T, class U, class F1, class F3, class F4, class F5, class F6>
auto make_PQSU_LCT(F1 TT, T T_id, F3 Tflip, F4 UU, U U_id, F5 Uinv, F6 UT){
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	return link_cut_trees_base<true, false, false, true, IS_COMMUTATIVE, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path + subtree update (commutative & invertible)
template<class T, class U, class F4, class F5, class F6>
auto make_PUSU_LCT(F4 UU, U U_id, F5 Uinv, F6 UT){
	auto TT = [&](){ assert(false); };
	using F1 = decltype(TT);
	T T_id = {};
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	return link_cut_trees_base<false, true, false, true, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - subtree query (commutative & invertible)
// - subtree update (commutative & invertible)
template<class T, class U, class F1, class F2, class F4, class F5, class F6>
auto make_SQSU_LCT(F1 TT, T T_id, F2 Tinv, F4 UU, U U_id, F5 Uinv, F6 UT){
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	return link_cut_trees_base<false, false, true, true, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path + subtree query (commutative & invertible)
// - path update
template<class T, class U, class F1, class F2, class F4, class F6>
auto make_PQPUSQ_LCT(F1 TT, T T_id, F2 Tinv, F4 UU, U U_id, F6 UT){
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	return link_cut_trees_base<true, true, true, false, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path query
// - path + subtree update (commutative & invertible)
// IS_COMMUTATIVE = true results in slightly better constant factor, Tflip is totally ignored in such case
template<bool IS_COMMUTATIVE, class T, class U, class F1, class F3, class F4, class F5, class F6>
auto make_PQPUSU_LCT(F1 TT, T T_id, F3 Tflip, F4 UU, U U_id, F5 Uinv, F6 UT){
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	return link_cut_trees_base<true, true, false, true, IS_COMMUTATIVE, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path + subtree query (commutative & invertible)
// - subtree update (commutative & invertible)
template<class T, class U, class F1, class F2, class F4, class F5, class F6>
auto make_PQSQSU_LCT(F1 TT, T T_id, F2 Tinv, F4 UU, U U_id, F5 Uinv, F6 UT){
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	return link_cut_trees_base<true, false, true, true, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path + subtree query (commutative & invertible)
// - path + subtree update (commutative & invertible)
template<class T, class U, class F1, class F2, class F4, class F5, class F6>
auto make_PQPUSQSU_LCT(F1 TT, T T_id, F2 Tinv, F4 UU, U U_id, F5 Uinv, F6 UT){
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	return link_cut_trees_base<true, true, true, true, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}

int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int n, qn;
	cin >> n >> qn;
	using M = matrix<modular>;
	using T = tuple<M, M, int>;
	auto TT = [&](const T &x, const T &y)->T{
		return {get<0>(x) * get<0>(y), get<1>(y) * get<1>(x), get<2>(x) + get<2>(y)};
	};
	T T_id{M::multiplicative_identity(2, 2), M::multiplicative_identity(2, 2), 0};
	auto Tinv = [&](const T &x)->T{
		return {*get<0>(x).inverse(), *get<1>(x).inverse(), get<2>(x)};
	};
	auto Tflip = [&](const T &x)->T{
		return {get<1>(x), get<0>(x), get<2>(x)};
	};
	using U = modular;
	auto UU = multiplies<>();
	U U_id = 1_m;
	auto Uinv = [&](const U &f)->U{
		return 1_m / f;
	};
	auto UT = [&](modular f, const T &x)->T{
		return {f.power(get<2>(x)) * get<0>(x), f.power(get<2>(x)) * get<1>(x), get<2>(x)};
	};
	auto lct = make_PQSU_LCT<false>(TT, T_id, Tflip, UU, U_id, Uinv, UT);
	auto read = [&]()->M{
		M mat(2, 2);
		for(auto i = 0; i < 2; ++ i){
			for(auto j = 0; j < 2; ++ j){
				cin >> mat[i][j];
			}
		}
		return mat;
	};
	auto write = [&](T mat)->void{
		for(auto i = 0; i < 2; ++ i){
			for(auto j = 0; j < 2; ++ j){
				cout << get<0>(mat)[i][j] << " ";
			}
		}
	};
	vector<T> init(n, T{M(2, 2), M(2, 2), 1});
	for(auto i = 0; i < n; ++ i){
		auto x = read();
		init[i] = {x, x, 1};
	}
	lct.build(init);
	for(auto qi = 0; qi < qn; ++ qi){
		string op;
		cin >> op;
		if(op == "link"){
			int u, v;
			cin >> u >> v;
			lct.link(u, v);
		}
		else if(op == "cut"){
			int u, v;
			cin >> u >> v;
			lct.cut(u, v);
		}
		else if(op == "reroot"){
			int u;
			cin >> u;
			lct.reroot(u);
		}
		else if(op == "root_of"){
			int u;
			cin >> u;
			cout << lct.root_of(u) << "\n";
		}
		else if(op == "parent_or_is_root"){
			int u;
			cin >> u;
			cout << lct.parent_or_is_root(u) << '\n';
		}
		else if(op == "lca_or_disconnected"){
			int u, v;
			cin >> u >> v;
			cout << lct.lca_or_disconnected(u, v) << '\n';
		}
		else if(op == "adjacent"){
			int u, v;
			cin >> u >> v;
			cout << lct.adjacent(u, v) << "\n";
		}
		else if(op == "depth"){
			int u; cin >> u;
			cout << lct.depth(u) << '\n';
		}
		else if(op == "distance"){
			int u, v; cin >> u >> v;
			cout << lct.distance(u, v) << "\n";
		}
		else if(op == "connected"){
			int u, v; cin >> u >> v;
			cout << lct.connected(u, v) << "\n";
		}
		else if(op == "find_ancestor_by_order"){
			int u, k; cin >> u >> k;
			cout << lct.find_ancestor_by_order(u, k) << "\n";
		}
		else if(op == "find_vertex_by_order"){
			int u, v, k; cin >> u >> v >> k;
			cout << lct.find_vertex_by_order(u, v, k) << "\n";
		}
		else if(op == "query"){
			int u;
			cin >> u;
			write(lct.query(u));
			cout << "\n";
		}
		else if(op == "query_path"){
			int u, v;
			cin >> u >> v;
			write(lct.query_path(u, v));
			cout << "\n";
		}
		else if(op == "query_subtree"){
			// int u;
			// cin >> u;
			// write(lct.query_subtree(u)[0]);
			// cout << "\n";
		}
		else if(op == "set"){
			int u;
			cin >> u;
			M mat = read();
			lct.set(u, {mat, mat, 1});
		}
		else if(op == "update"){
			int u, f;
			cin >> u >> f;
			lct.update(u, f);
		}
		else if(op == "update_path"){
			// int u, v, f;
			// cin >> u >> v >> f;
			// lct.update_path(u, v, f);
		}
		else if(op == "update_subtree"){
			int u, f;
			cin >> u >> f;
			lct.update_subtree(u, f);
		}
		else{
			assert(false);
		}
		cout.flush();
	}
	return 0;
}

/*
debug(lct.size);
debug(lct.lazy_flip);
debug(lct.pv);
debug(lct.left);
debug(lct.right);
debug(lct.data);
debug(lct.aux_data);
debug(lct.virtual_data);
debug(lct.subtr_data);
debug(lct.aux_lazy);
debug(lct.virtual_lazy);
debug(lct.subtr_lazy);
debug_endl();
*/