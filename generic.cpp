// https://codeforces.com/contest/1591/problem/F
#pragma GCC optimize("Ofast")
#pragma GCC optimization ("unroll-loops")
#include <bits/stdc++.h>
#define rsrt(v) sort(v.begin(), v.end(), greater<int>())
#define fi(i,a,b) for(int i=a;i<b;i++)
#define srt(v) sort(v.begin(),v.end())
#define pb push_back
#define vi vector<int>
#define pii pair<int,int>
#define all(x) (x).begin(),(x).end()
#define ll long long
#define int long long
ll md = 998244353;
int inf = 1e18;
#define X first
#define Y second
using namespace std;
template <typename T>
T pw(T a, T b) {T c = 1, m = a;while(b) {if (b & 1) c=(c*m); m=(m*m); b/=2;} return c;}
template <typename T>
T ceel(T a, T b){if (a%b==0) return a/b; else return a/b + 1;}
template <typename T>
T gcd(T a, T b) {return b == 0 ? a : gcd(b, a % b);}
ll pwmd(ll a, ll b) {ll c = 1, m = a%md;while(b) {if (b & 1) c=(c*m)%md; m=(m*m)%md; b/=2;} return c;}
ll modinv(ll n){return pwmd(n, md - 2);}
mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
ll random(ll l, ll r){ // gives random number in [l,r]
  return uniform_int_distribution<ll>(l, r)(rng);
}
template <class T1, class T2>
ostream &operator<<(ostream &os, const pair<T1, T2> &p) {
  return os << '{' << p.first << ", " << p.second << '}';
}
template <class T, class = decay_t<decltype(*begin(declval<T>()))>,
          class = enable_if_t<!is_same<T, string>::value>>
ostream &operator<<(ostream &os, const T &c) {
  os << '[';
  for (auto it = c.begin(); it != c.end(); ++it)
    os << &", "[2 * (it == c.begin())] << *it;
  return os << ']';
}
//support up to 5 args
#define _NTH_ARG(_1, _2, _3, _4, _5, _6, N, ...) N
#define _FE_0(_CALL, ...)
#define _FE_1(_CALL, x) _CALL(x)
#define _FE_2(_CALL, x, ...) _CALL(x) _FE_1(_CALL, __VA_ARGS__)
#define _FE_3(_CALL, x, ...) _CALL(x) _FE_2(_CALL, __VA_ARGS__)
#define _FE_4(_CALL, x, ...) _CALL(x) _FE_3(_CALL, __VA_ARGS__)
#define _FE_5(_CALL, x, ...) _CALL(x) _FE_4(_CALL, __VA_ARGS__)
#define FOR_EACH_MACRO(MACRO, ...)                                             \
  _NTH_ARG(dummy, ##__VA_ARGS__, _FE_5, _FE_4, _FE_3, _FE_2, _FE_1, _FE_0)     \
  (MACRO, ##__VA_ARGS__)
// #ifdef LOCAL
#define out(x) #x " = " << x << "; "
#define dbg(...)                                                              \
  cerr << "Line " << __LINE__ << ": " FOR_EACH_MACRO(out, __VA_ARGS__) << "\n"
// #else
// #define debug(...) 42
// #endif
//--------------------------------theartofwar-------------------------------------------//
struct node
{
    int no_of_pnts = 0, q = 0;
    node() {}
    node(pair<int, int> val)
    {
        q = val.first;
        no_of_pnts = val.second;
    }
    void merge(const node &l, const node &r)
    { // store the thing you wanna query

        q = (l.q + r.q) % md;
        if (q < 0) q += md;
        no_of_pnts = (l.no_of_pnts + r.no_of_pnts) % md;
    }
};
struct update
{
    int k = 1, b = 0; //      val => k * val + b
    update() {}
    update(pair<int, int> val)
    {
        k = val.first, b = val.second;
        if (k < 0) k += md;
    }
    void combine(update &other, const int32_t &tl, const int32_t &tr)
    {
        k = (k * other.k) % md;  //   k1 * (k*val + b) + b1 = k * k1 * val + k1 * b + b1
        if (k < 0) k += md;
        b = ((other.k * b) % md + other.b) % md;
        if (b < 0) b += md;
    }
    void apply(node &x, const int32_t &tl, const int32_t &tr)
    {
        x.q = ((x.q * k) % md + (x.no_of_pnts * b) % md) % md;
        if (x.q < 0) x.q += md;
    }
};
//template <typename node, typename update>
struct segtree
{
    int len;
    vector<node> t;
    vector<update> u;
    vector<bool> lazy;
    node identity_element;
    update identity_transformation;
    segtree(int l)
    {
        len = l;
        t.resize(4 * len);
        u.resize(4 * len);
        lazy.resize(4 * len);
        identity_element = node();
        identity_transformation = update();
    }
    void pushdown(const int32_t &v, const int32_t &tl, const int32_t &tr)
    {
        if (!lazy[v])
            return;
        int32_t tm = (tl + tr) >> 1;
        apply(v << 1, tl, tm, u[v]);
        apply(v << 1 | 1, tm + 1, tr, u[v]);
        u[v] = identity_transformation;
        lazy[v] = 0;
    }
    void apply(const int32_t &v, const int32_t &tl, const int32_t &tr, update upd)
    {
        if (tl != tr)
        {
            lazy[v] = 1;
            u[v].combine(upd, tl, tr);
        }
        upd.apply(t[v], tl, tr);
    }
    template <typename T>
    void build(const T &arr, const int32_t &v, const int32_t &tl, const int32_t &tr)
    {
        if (tl == tr)
        {
            t[v] = arr[tl];
            return;
        }
        int32_t tm = (tl + tr) >> 1;
        build(arr, v << 1, tl, tm);
        build(arr, v << 1 | 1, tm + 1, tr);
        t[v].merge(t[v << 1], t[v << 1 | 1]);
    }
    node query(const int32_t &v, const int32_t &tl, const int32_t &tr, const int32_t &l, const int32_t &r)
    {
        if (l > tr || r < tl)
        {
            return identity_element;
        }
        if (tl >= l && tr <= r)
        {
            return t[v];
        }
        pushdown(v, tl, tr);
        int32_t tm = (tl + tr) >> 1;
        node a = query(v << 1, tl, tm, l, r), b = query(v << 1 | 1, tm + 1, tr, l, r), ans;
        ans.merge(a, b);
        return ans;
    }
    // rupd = range update
    void rupd(const int32_t &v, const int32_t &tl, const int32_t &tr, const int32_t &l, const int32_t &r, const update &upd)
    {
        if (l > tr || r < tl)
        {
            return;
        }
        if (tl >= l && tr <= r)
        {
            apply(v, tl, tr, upd);
            return;
        }
        pushdown(v, tl, tr);
        int32_t tm = (tl + tr) >> 1;
        rupd(v << 1, tl, tm, l, r, upd);
        rupd(v << 1 | 1, tm + 1, tr, l, r, upd);
        t[v].merge(t[v << 1], t[v << 1 | 1]);
    }
    public:
    template <typename T>
    void build(const T &arr)
    {
        build(arr, 1, 0, len - 1);
    }
    node query(const int32_t &l, const int32_t &r)
    {
        return query(1, 0, len - 1, l, r);
    }
    void rupd(const int32_t &l, const int32_t &r, const update &upd)
    {
        rupd(1, 0, len - 1, l, r, upd);
    }
};
signed main()
{
    ios_base::sync_with_stdio(false),cin.tie(0),cout.tie(0);
    int n, a;
    cin >> n;
    vector<int> v;
    set<int> temp;
    for (int i = 0; i < n; i++) cin >> a, v.push_back(a), temp.insert(a);
    vector<pair<int, int>> pre;
    map<int, int> mp;
    int p = 0, id = 0;
    for (auto it = temp.begin(); it != temp.end(); it++) {
        int val = *it;
        if (val != p + 1) pre.push_back({0, val - p - 1}), id++;
        pre.push_back({0, 1}), id++;
        mp[val] = id - 1;
        p = val;
    }
    int m = pre.size(), tot = 0;
    for (int i = 0; i < m; i++) {
        tot += pre[i].second;
        if (tot <= v[0]) pre[i].first = pre[i].second;
    }
    segtree s(m);
    s.build(pre);
    for (int i = 1; i < n; i++) {
        int pos = mp[v[i]], sum = s.query(0, m).q;
        pair<int, int> p1 = {-1, sum}, p2 = {0, 0}; 
        s.rupd(0, pos, p1); // In [1, pos]   v => -1 * v + sum
        if (pos + 1 <= m) s.rupd(pos + 1, m, p2); // In [pos + 1, m] v => 0 * v + 0
    }
    cout << s.query(0, m).q;
}
