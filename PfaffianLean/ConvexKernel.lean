import PfaffianLean.IntervalDecomposition

/-!
# Additivity of convex kernels

If `f ≥ 0` is nonincreasing and convex on `(0, ∞)` and `x_1 < ⋯ < x_n`, then
`K_{f,x} ∈ 𝒜_n` and `α_[1,n](K_{f,x}) = f(x_n - x_1)`.
-/

open Finset

/-- **Additivity of convex kernels.** -/
theorem convex_kernel_additive (f : ℝ → ℝ) (hf : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    kernel f x ∈ additiveClass n ∧ alpha n (kernel f x) (1, n) = f (x n - x 1) := by
  -- Write `K = K_{f,x}`.
  set K := kernel f x with hK
  have hKapp : ∀ i j, K i j = f (x j - x i) := fun _ _ => rfl
  -- Gaps between the points `x_1 < ⋯ < x_n` are positive.
  have hgap : ∀ a b, 1 ≤ a → a < b → b ≤ n → x b - x a ∈ Set.Ioi 0 := fun a b ha hab hb =>
    sub_pos.2 (hx (Set.mem_Icc.2 ⟨ha, by omega⟩) (Set.mem_Icc.2 ⟨by omega, hb⟩) hab)
  -- `α_[1,n](K) = K(1, n) = f(x_n - x_1)`, by the corner case of Interval decomposition.
  have hcorner : alpha n K (1, n) = f (x n - x 1) := interval_decomposition_corner n K
  refine ⟨fun J hJ => ?_, hcorner⟩
  obtain ⟨p, q⟩ := J
  simp only [intervals, mem_filter, mem_product, mem_Icc] at hJ
  obtain ⟨⟨⟨hp1, -⟩, -, hqn⟩, hpq⟩ := hJ
  rcases hp1.eq_or_lt with rfl | hp1 <;> rcases hqn.eq_or_lt with rfl | hqn
  · -- If `p = 1` and `q = n`: `α = f(x_n − x_1) ≥ 0`, since `f ≥ 0`.
    rw [hcorner]
    exact hf _ (hgap 1 q le_rfl hpq le_rfl)
  · -- If `p = 1` and `q < n`: `α = f(x_q − x_1) − f(x_{q+1} − x_1) ≥ 0`, since `f` is
    -- nonincreasing.
    have hα : alpha n K (1, q) = f (x q - x 1) - f (x (q + 1) - x 1) := by
      simp only [alpha, Nat.sub_self, pad_zero_left,
        pad_of_ne n K one_ne_zero (by omega : q ≠ n + 1),
        pad_of_ne n K one_ne_zero (by omega : q + 1 ≠ n + 1), hKapp]
      ring
    rw [hα, sub_nonneg]
    refine hanti (hgap 1 q le_rfl hpq (by omega)) (hgap 1 (q + 1) le_rfl (by omega) hqn) ?_
    exact sub_le_sub_right (le_of_lt (sub_pos.1 (hgap q (q + 1) (by omega) (by omega) hqn))) _
  · -- If `p > 1` and `q = n`: `α = f(x_n − x_p) − f(x_n − x_{p−1}) ≥ 0`. (Here `n` has been
    -- substituted by `q`.)
    have hα : alpha q K (p, q) = f (x q - x p) - f (x q - x (p - 1)) := by
      simp only [alpha, pad_succ_right, pad_of_ne q K (by omega : p ≠ 0) (by omega : q ≠ q + 1),
        pad_of_ne q K (by omega : p - 1 ≠ 0) (by omega : q ≠ q + 1), hKapp]
      ring
    rw [hα, sub_nonneg]
    refine hanti (hgap p q (by omega) hpq le_rfl) (hgap (p - 1) q (by omega) (by omega) le_rfl) ?_
    exact sub_le_sub_left (le_of_lt (sub_pos.1 (hgap (p - 1) p (by omega) (by omega) (by omega)))) _
  · -- If `1 < p < q < n`, put `s = x_q − x_p`, `A = x_p − x_{p−1}` and `B = x_{q+1} − x_q`,
    -- all `> 0`. Then `α = f(s) + f(s + A + B) − f(s + A) − f(s + B)`.
    set s := x q - x p with hs_def
    set A := x p - x (p - 1) with hA_def
    set B := x (q + 1) - x q with hB_def
    have hs : s ∈ Set.Ioi 0 := hgap p q (by omega) hpq (by omega)
    have hA : (0 : ℝ) < A := hgap (p - 1) p (by omega) (by omega) (by omega)
    have hB : (0 : ℝ) < B := hgap q (q + 1) (by omega) (by omega) hqn
    have hsAB : s + A + B ∈ Set.Ioi 0 := by
      rw [Set.mem_Ioi] at hs ⊢
      linarith
    have hα : alpha n K (p, q) = f s + f (s + A + B) - f (s + A) - f (s + B) := by
      simp only [alpha, pad_of_ne n K (by omega : p ≠ 0) (by omega : q ≠ n + 1),
        pad_of_ne n K (by omega : p - 1 ≠ 0) (by omega : q ≠ n + 1),
        pad_of_ne n K (by omega : p ≠ 0) (by omega : q + 1 ≠ n + 1),
        pad_of_ne n K (by omega : p - 1 ≠ 0) (by omega : q + 1 ≠ n + 1), hKapp]
      rw [show x q - x (p - 1) = s + A by ring, show x (q + 1) - x p = s + B by ring,
        show x (q + 1) - x (p - 1) = s + A + B by ring]
      ring
    -- With `λ = B/(A + B)`, `s + A = λ s + (1 − λ)(s + A + B)` and
    -- `s + B = (1 − λ) s + λ (s + A + B)`.
    set lam := B / (A + B) with hlam_def
    have hAB : (0 : ℝ) < A + B := add_pos hA hB
    have hlam0 : 0 ≤ lam := div_nonneg hB.le hAB.le
    have hlam1 : 0 ≤ 1 - lam := by
      rw [sub_nonneg, div_le_one hAB]
      linarith
    have hpointA : lam * s + (1 - lam) * (s + A + B) = s + A := by
      rw [hlam_def]
      field_simp
      ring
    have hpointB : (1 - lam) * s + lam * (s + A + B) = s + B := by
      rw [hlam_def]
      field_simp
      ring
    -- Convexity gives `f(s + A) ≤ λ f(s) + (1 − λ) f(s + A + B)` and
    -- `f(s + B) ≤ (1 − λ) f(s) + λ f(s + A + B)`.
    have hconvA := hconv.2 hs hsAB hlam0 hlam1 (by ring)
    have hconvB := hconv.2 hs hsAB hlam1 hlam0 (by ring)
    simp only [smul_eq_mul, hpointA, hpointB] at hconvA hconvB
    -- Adding, `f(s + A) + f(s + B) ≤ f(s) + f(s + A + B)`.
    rw [hα]
    linarith
