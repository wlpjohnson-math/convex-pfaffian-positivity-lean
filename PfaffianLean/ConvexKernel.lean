import PfaffianLean.Families

/-!
# Additivity of convex kernels

Reference: `refs/pfaffian-convex.tex`, Section 3, Lemma (Additivity of convex kernels).

If `f ≥ 0` is nonincreasing and convex on `(0, ∞)` and `x_1 < ⋯ < x_n`, then
`K_{f,x} ∈ 𝒜_n` and `α_[1,n](K_{f,x}) = f(x_n - x_1)`.
-/

/-- **Additivity of convex kernels.** -/
theorem convex_kernel_additive (f : ℝ → ℝ) (hf : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    kernel f x ∈ additiveClass n ∧ alpha n (kernel f x) (1, n) = f (x n - x 1) := by
  sorry
