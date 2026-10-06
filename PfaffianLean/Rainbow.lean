import PfaffianLean.LowerBounds

/-!
# The rainbow bound

* Outer-pair bound: for even `n ≥ 2` and `K ∈ 𝒜_n`, `Pf(K) ≥ K(1, n) · Pf(K_{[2, n-1]})`.
* Additive rainbow bound: for even `n` and `K ∈ 𝒜_n`, `Pf(K) ≥ ∏_{k=1}^{n/2} K(k, n+1-k)`.
* Convex rainbow bound: for `f` positive, nonincreasing and convex on `(0, ∞)`, even `n` and
  `x_1 < ⋯ < x_n`, `Pf A_f(x) ≥ ∏_{k=1}^{n/2} f(x_{n+1-k} - x_k) > 0`.

The outer-pair bound goes through the first-row expansion. For a family `K` on `[n]`, let
`L = K_{[2,n]}`, read on `[n - 1]` (`K.submatrix (· + 1) (· + 1)`). The partial first-row sums
`T_m = ∑_{j=2}^{m} (-1)^j K(1, j) Pf([n] \ {1, j})` are rewritten by Abel summation in terms of
the prefix sums `Z_q(L)` of the bordered-Pfaffian cofactors of `L`, which are `≥ 0` on `𝒜_{n-1}`.
The prefix sums are shown `≥ 0` with a one-border family: a new first point whose row is a step.
The rainbow bound then follows by peeling outer pairs, using that `𝒜_n` is closed under deleting
the first or the last point.
-/

open Finset

/-! ### Restriction -/

/-- Deleting the last point keeps a family additive: `K ∈ 𝒜_{n+1}` implies `K ∈ 𝒜_n`. -/
theorem mem_additiveClass_of_succ {n : ℕ} {K : Matrix ℕ ℕ ℝ} (hK : K ∈ additiveClass (n + 1)) :
    K ∈ additiveClass n := by
  sorry

/-- Deleting the first point keeps a family additive: if `K ∈ 𝒜_{n+1}`, then `K_{[2, n+1]}`,
read on `[n]`, is in `𝒜_n`. -/
theorem submatrix_succ_mem_additiveClass {n : ℕ} {K : Matrix ℕ ℕ ℝ}
    (hK : K ∈ additiveClass (n + 1)) :
    K.submatrix (· + 1) (· + 1) ∈ additiveClass n := by
  sorry

/-- Shifting the index set by one: `Pf(A_{[a+1, b+1]}) = Pf(A'_{[a, b]})`, with
`A'(i, j) = A(i + 1, j + 1)`. -/
theorem pfaffian_Icc_succ {R : Type*} [CommRing R] (a b : ℕ) (A : Matrix ℕ ℕ R) :
    pfaffian (Icc (a + 1) (b + 1)) A = pfaffian (Icc a b) (A.submatrix (· + 1) (· + 1)) := by
  sorry

/-! ### Prefix sums of the bordered-Pfaffian cofactors -/

/-- The prefix sum `Z_q(L) = c'_1(L) + ⋯ + c'_{q-1}(L)` of the bordered-Pfaffian cofactors
`c'_t(L) = (-1)^(t+1) Pf(L_{[N] \ {t}})` of a family `L` on `[N]`. -/
def prefixSum (N : ℕ) (L : Matrix ℕ ℕ ℝ) (q : ℕ) : ℝ :=
  ∑ t ∈ Ico 1 q, (-1) ^ (t + 1) * pfaffian (Icc 1 N \ {t}) L

/-- The one-border family of `L` at `q` with height `h`, a family on `[N + 1]` when `L` is on
`[N]`: a new first point is added and the points of `L` move up by one. The new point is joined
to each `j ≤ q` with weight `h` and to each `j > q` with weight `0` (a step row), and `h` is added
to every entry of `L` between two points of `[1, q - 1]` (old numbering). -/
def oneBorder (L : Matrix ℕ ℕ ℝ) (q : ℕ) (h : ℝ) : Matrix ℕ ℕ ℝ :=
  Matrix.of fun i j => (if i = 1 then 0 else L (i - 1) (j - 1)) + if j ≤ q then h else 0

/-- **One-border identity.** The Pfaffian of the one-border family is `h · Z_q` of `L` with `h`
added on `[1, q - 1]`. -/
theorem pfaffian_oneBorder (N : ℕ) (L : Matrix ℕ ℕ ℝ) {q : ℕ} (hq : q ≤ N + 1) (h : ℝ) :
    pfaffian (Icc 1 (N + 1)) (oneBorder L q h) =
      h * prefixSum N (Matrix.of fun i j => L i j + if j < q then h else 0) q := by
  sorry

/-- **One-border additivity.** For `L ∈ 𝒜_N`, `2 ≤ q ≤ N + 1` and `h ≥ 0`, the one-border family
is in `𝒜_{N+1}`. -/
theorem oneBorder_mem_additiveClass {N : ℕ} {L : Matrix ℕ ℕ ℝ} (hL : L ∈ additiveClass N)
    {q : ℕ} (hq2 : 2 ≤ q) (hq : q ≤ N + 1) {h : ℝ} (hh : 0 ≤ h) :
    oneBorder L q h ∈ additiveClass (N + 1) := by
  sorry

/-- **Prefix sums are nonnegative.** For odd `N`, `L ∈ 𝒜_N` and `q ≤ N + 1`: `Z_q(L) ≥ 0`. -/
theorem prefixSum_nonneg {N : ℕ} (hN : Odd N) {L : Matrix ℕ ℕ ℝ} (hL : L ∈ additiveClass N)
    {q : ℕ} (hq : q ≤ N + 1) : 0 ≤ prefixSum N L q := by
  sorry

/-! ### The outer-pair bound -/

/-- **Abel summation for `T_m`.** For a family `K` on `[n]` and `2 ≤ m ≤ n`, with
`L = K_{[2, n]}` read on `[n - 1]`:
`T_m = ∑_{q=2}^{m-1} α_[1,q](K) Z_q(L) + K(1, m) Z_m(L)`. -/
theorem firstRowPartial_eq_abel (n : ℕ) (K : Matrix ℕ ℕ ℝ) {m : ℕ} (hm2 : 2 ≤ m)
    (hmn : m ≤ n) :
    ∑ j ∈ Icc 2 m, (-1) ^ j * K 1 j * pfaffian (Icc 2 n \ {j}) K =
      ∑ q ∈ Ico 2 m, alpha n K (1, q) * prefixSum (n - 1) (K.submatrix (· + 1) (· + 1)) q +
        K 1 m * prefixSum (n - 1) (K.submatrix (· + 1) (· + 1)) m := by
  sorry

/-- **`T_{n-1}`.** For even `n ≥ 2`: `T_{n-1} = Pf(K) - K(1, n) Pf(K_{[2, n-1]})`. -/
theorem firstRowPartial_eq_sub (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) (K : Matrix ℕ ℕ ℝ) :
    ∑ j ∈ Icc 2 (n - 1), (-1) ^ j * K 1 j * pfaffian (Icc 2 n \ {j}) K =
      pfaffian (Icc 1 n) K - K 1 n * pfaffian (Icc 2 (n - 1)) K := by
  sorry

/-- **Outer-pair bound.** For even `n ≥ 2` and `K ∈ 𝒜_n`: `Pf(K) ≥ K(1, n) · Pf(K_{[2, n-1]})`. -/
theorem outer_pair_bound (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K ≥ K 1 n * pfaffian (Icc 2 (n - 1)) K := by
  sorry

/-! ### The rainbow bound -/

/-- **Additive rainbow bound.** For even `n` and `K ∈ 𝒜_n`:
`Pf(K) ≥ ∏_{k=1}^{n/2} K(k, n+1-k)`. -/
theorem additive_rainbow_bound (n : ℕ) (hn : Even n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K ≥ ∏ k ∈ Icc 1 (n / 2), K k (n + 1 - k) := by
  sorry

/-- **Convex rainbow bound.** For every positive, nonincreasing, convex `f` on `(0, ∞)`, every
even `n` and every `x_1 < ⋯ < x_n`: `Pf A_f(x) ≥ ∏_{k=1}^{n/2} f(x_{n+1-k} - x_k) > 0`. -/
theorem convex_rainbow_bound (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel f x) ≥ ∏ k ∈ Icc 1 (n / 2), f (x (n + 1 - k) - x k) ∧
      ∏ k ∈ Icc 1 (n / 2), f (x (n + 1 - k) - x k) > 0 := by
  sorry
