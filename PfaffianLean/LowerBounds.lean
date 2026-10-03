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

/-- **Additive lower bound.** For even `n ≥ 2` and `K ∈ 𝒜_n`:
`Pf(K) = F_n(α(K)) ≥ K(1, n)^(n/2) ≥ 0`. -/
theorem additive_lower_bound (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K = aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) ∧
      aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) ≥ K 1 n ^ (n / 2) ∧
      K 1 n ^ (n / 2) ≥ 0 := by
  sorry

/-- **Convex lower bound.** For every positive, nonincreasing, convex `f` on `(0, ∞)`, every
even `n` and every `x_1 < ⋯ < x_n`: `Pf A_f(x) ≥ f(x_n - x_1)^(n/2) > 0`. -/
theorem convex_lower_bound (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel f x) ≥ f (x n - x 1) ^ (n / 2) ∧ f (x n - x 1) ^ (n / 2) > 0 := by
  sorry
