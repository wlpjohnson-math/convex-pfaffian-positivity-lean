import PfaffianLean.IntervalDecomposition
import PfaffianLean.ConvexKernel
import PfaffianLean.CoeffPositivity

/-!
# The Additive lower bound and the Convex lower bound

Reference: `refs/pfaffian-convex.tex`, Section 3, Theorems (Additive lower bound) and
(Convex lower bound).

* Additive lower bound: for even `n ≥ 2` and `K ∈ 𝒜_n`, `Pf(K) = F_n(α(K)) ≥ K(1, n)^(n/2) ≥ 0`.
* Convex lower bound: for `f` positive, nonincreasing and convex on `(0, ∞)`, even `n`, and
  `x_1 < ⋯ < x_n`, `Pf A_f(x) ≥ f(x_n - x_1)^(n/2) > 0`.
-/

open Finset MvPolynomial

/-- A polynomial with nonnegative integer coefficients, evaluated at a point with nonnegative
coordinates, is at least any single one of its terms `c_μ a^μ`. -/
theorem term_le_aeval {σ : Type*} (p : MvPolynomial σ ℤ) (hp : ∀ m, 0 ≤ p.coeff m) (a : σ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (μ : σ →₀ ℕ) :
    (p.coeff μ : ℝ) * ∏ i ∈ μ.support, a i ^ μ i ≤ aeval a p := by
  have hterm : ∀ d, 0 ≤ (p.coeff d : ℝ) * ∏ i ∈ d.support, a i ^ d i := fun d =>
    mul_nonneg (Int.cast_nonneg (hp d)) (prod_nonneg fun i _ => pow_nonneg (ha i) _)
  rw [aeval_def, eval₂_eq]
  simp only [algebraMap_int_eq, eq_intCast]
  by_cases hμ : μ ∈ p.support
  · exact single_le_sum (fun d _ => hterm d) hμ
  · rw [notMem_support_iff.1 hμ, Int.cast_zero, zero_mul]
    exact sum_nonneg fun d _ => hterm d

/-- **Additive lower bound.** For even `n ≥ 2` and `K ∈ 𝒜_n`:
`Pf(K) = F_n(α(K)) ≥ K(1, n)^(n/2) ≥ 0`. -/
theorem additive_lower_bound (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K = aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) ∧
      aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) ≥ K 1 n ^ (n / 2) ∧
      K 1 n ^ (n / 2) ≥ 0 := by
  -- "By the Interval decomposition lemma, `Pf(K) = F_n(α)` with `α = α(K) ≥ 0` componentwise
  -- (`K ∈ 𝒜_n`)."
  have hpf := interval_decomposition_pfaffian n K
  have hα : ∀ J : intervals n, 0 ≤ alpha n K J := fun J => hK J.1 J.2
  -- "`α_[1,n] = K(1, n)` by Interval decomposition."
  set J₀ : intervals n := ⟨(1, n), corner_mem_intervals h2⟩
  have hcorner : alpha n K J₀ = K 1 n := interval_decomposition_corner n K
  -- "By Coefficient positivity, `F_n(α) = ∑_μ c_μ α^μ` with integers `c_μ ≥ 0`. Every term is
  -- `≥ 0`, and the term of `a_[1,n]^{n/2}` is `α_[1,n]^{n/2} = K(1,n)^{n/2}` (coefficient `1`)."
  have hbound : aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) ≥
      K 1 n ^ (n / 2) := by
    have h := term_le_aeval (intervalPfaffian n) (coeff_nonneg n) _ hα
      (Finsupp.single J₀ (n / 2))
    rwa [coeff_corner n hn h2, Int.cast_one, one_mul,
      Finsupp.support_single _ (by omega), prod_singleton, Finsupp.single_eq_same,
      hcorner] at h
  refine ⟨hpf, hbound, ?_⟩
  rw [← hcorner]
  exact pow_nonneg (hα J₀) _

/-- **Convex lower bound.** For every positive, nonincreasing, convex `f` on `(0, ∞)`, every
even `n` and every `x_1 < ⋯ < x_n`: `Pf A_f(x) ≥ f(x_n - x_1)^(n/2) > 0`. -/
theorem convex_lower_bound (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel f x) ≥ f (x n - x 1) ^ (n / 2) ∧ f (x n - x 1) ^ (n / 2) > 0 := by
  -- "For `n = 0` both sides equal `1`."
  rcases Nat.eq_zero_or_pos n with rfl | hpos0
  · rw [show (Icc 1 0 : Finset ℕ) = ∅ by decide, pfaffian_empty]
    norm_num
  have h2 : 2 ≤ n := by
    obtain ⟨r, hr⟩ := hn
    omega
  -- "For `n ≥ 2`: `K_{f,x} ∈ 𝒜_n` by Additivity of convex kernels, …"
  obtain ⟨hK, -⟩ := convex_kernel_additive f (fun t ht => (hpos t ht).le) hanti hconv n x hx
  -- "… so the Additive lower bound applies, …"
  obtain ⟨hpf, hge, -⟩ := additive_lower_bound n hn h2 (kernel f x) hK
  -- "… and `K_{f,x}(1, n) = f(x_n − x_1) > 0`."
  have hK1n : kernel f x 1 n = f (x n - x 1) := rfl
  have hgap : x n - x 1 ∈ Set.Ioi 0 :=
    sub_pos.2 (hx ⟨le_rfl, by omega⟩ ⟨by omega, le_rfl⟩ (by omega))
  refine ⟨?_, pow_pos (hpos _ hgap) _⟩
  rw [hpf, ← hK1n]
  exact hge
