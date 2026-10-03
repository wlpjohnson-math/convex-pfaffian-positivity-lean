import PfaffianLean.Families

/-!
# The Interval decomposition lemma

Reference: `refs/pfaffian-convex.tex`, Section 3, Lemma (Interval decomposition).

For every family `K` on `[n]` and all `1 ≤ i < j ≤ n`,
`K(i, j) = ∑_{J ∈ I_n, J ∋ i, j} α_J(K)`. Hence `Pf(K) = F_n(α(K))` (via the evaluation lemma
`RingHom.map_pfaffian`), and `α_[1,n](K) = K(1, n)`.
-/

open Finset MvPolynomial

/-- **Interval decomposition.** `K(i, j)` is the sum of `α_J(K)` over the intervals `J ∈ I_n`
containing `i` and `j`. -/
theorem interval_decomposition (n : ℕ) (K : Matrix ℕ ℕ ℝ) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (hj : j ≤ n) :
    K i j = ∑ J ∈ intervals n with i ∈ Icc J.1 J.2 ∧ j ∈ Icc J.1 J.2, alpha n K J := by
  sorry

/-- **Interval decomposition**, Pfaffian form: `Pf(K) = F_n(α(K))`. -/
theorem interval_decomposition_pfaffian (n : ℕ) (K : Matrix ℕ ℕ ℝ) :
    pfaffian (Icc 1 n) K = aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) := by
  sorry

/-- **Interval decomposition**, corner: `α_[1,n](K) = K(1, n)`. -/
theorem interval_decomposition_corner (n : ℕ) (K : Matrix ℕ ℕ ℝ) : alpha n K (1, n) = K 1 n := by
  sorry
