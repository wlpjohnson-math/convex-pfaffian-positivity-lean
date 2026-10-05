import PfaffianLean.LowerBounds

/-!
# Power kernels

The Convex lower bound specialised to `f(r) = r^(-p)` (`Real.rpow`), `p > 0`: for even `n` and
`x_1 < ⋯ < x_n`, `Pf A_f(x) ≥ ((x_n - x_1)^(-p))^(n/2) > 0`. The case `p = 2` is the
Albouy–Moeckel kernel.

Mathlib has convexity of `r ↦ r^p` only for `p ≥ 1` (`convexOn_rpow`), concavity for
`0 ≤ p ≤ 1` (`Real.concaveOn_rpow`) and convexity for integer exponents (`convexOn_zpow`), so the
convexity of `r ↦ r^(-p)` on `(0, ∞)` is proved here by composition (`convexOn_rpow_neg`).
-/

open Finset

/-- `r ↦ r⁻¹` maps `(0, ∞)` onto `(0, ∞)`. -/
theorem image_inv_Ioi_zero : (fun r : ℝ => r⁻¹) '' Set.Ioi 0 = Set.Ioi 0 := by
  ext t
  simp only [Set.mem_image, Set.mem_Ioi]
  refine ⟨?_, fun ht => ⟨t⁻¹, inv_pos.2 ht, inv_inv t⟩⟩
  rintro ⟨r, hr, rfl⟩
  exact inv_pos.2 hr

/-- For `p ≠ 0`, `r ↦ r^p` maps `(0, ∞)` onto `(0, ∞)`. -/
theorem image_rpow_Ioi_zero {p : ℝ} (hp : p ≠ 0) :
    (fun r : ℝ => r ^ p) '' Set.Ioi 0 = Set.Ioi 0 := by
  ext t
  simp only [Set.mem_image, Set.mem_Ioi]
  refine ⟨?_, fun ht => ⟨t ^ p⁻¹, Real.rpow_pos_of_pos ht _, Real.rpow_inv_rpow ht.le hp⟩⟩
  rintro ⟨r, hr, rfl⟩
  exact Real.rpow_pos_of_pos hr p

/-- For `p > 0`, `r ↦ r^(-p)` is convex on `(0, ∞)`. -/
theorem convexOn_rpow_neg {p : ℝ} (hp : 0 < p) :
    ConvexOn ℝ (Set.Ioi 0) fun r : ℝ => r ^ (-p) := by
  -- On `(0, ∞)`, `r^(-p) = (r^p)⁻¹ = (r⁻¹)^p`.
  have hneg : ∀ r ∈ Set.Ioi (0 : ℝ), r ^ (-p) = (r ^ p)⁻¹ := fun r hr =>
    Real.rpow_neg (le_of_lt hr) p
  -- `r ↦ r⁻¹` is convex on `(0, ∞)`.
  have hinv : ConvexOn ℝ (Set.Ioi 0) fun r : ℝ => r⁻¹ := by
    simpa only [zpow_neg_one] using convexOn_zpow (𝕜 := ℝ) (-1)
  rcases le_total p 1 with hp1 | hp1
  · -- `0 < p ≤ 1`: `r ↦ r^p` is concave, and `t ↦ t⁻¹` is convex and nonincreasing.
    have hconc : ConcaveOn ℝ (Set.Ioi 0) fun r : ℝ => r ^ p :=
      (Real.concaveOn_rpow hp.le hp1).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)
    rw [← image_rpow_Ioi_zero hp.ne'] at hinv
    have h := hinv.comp_concaveOn hconc
      (by rw [image_rpow_Ioi_zero hp.ne']; exact inv_antitoneOn_Ioi)
    exact h.congr fun r hr => (hneg r hr).symm
  · -- `p ≥ 1`: `r ↦ r⁻¹` is convex, and `t ↦ t^p` is convex and nondecreasing on `[0, ∞)`.
    have hpow : ConvexOn ℝ ((fun r : ℝ => r⁻¹) '' Set.Ioi 0) fun t : ℝ => t ^ p := by
      rw [image_inv_Ioi_zero]
      exact (convexOn_rpow hp1).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)
    have h := hpow.comp hinv (by
      rw [image_inv_Ioi_zero]
      exact (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hp.le).mono Set.Ioi_subset_Ici_self)
    refine h.congr fun r hr => ?_
    simp only [Function.comp_apply]
    rw [Real.inv_rpow (le_of_lt hr), hneg r hr]

/-- **Power kernels.** For `p > 0`, even `n` and `x_1 < ⋯ < x_n`, the Convex lower bound for
`f(r) = r^(-p)`: `Pf A_f(x) ≥ ((x_n - x_1)^(-p))^(n/2) > 0`. -/
theorem power_kernel_lower_bound (p : ℝ) (hp : 0 < p) (n : ℕ) (hn : Even n) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel (fun r => r ^ (-p)) x) ≥ ((x n - x 1) ^ (-p)) ^ (n / 2) ∧
      ((x n - x 1) ^ (-p)) ^ (n / 2) > 0 := by
  -- `f(r) = r^(-p)` is positive, nonincreasing and convex on `(0, ∞)`.
  have hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < t ^ (-p) := fun t ht => Real.rpow_pos_of_pos ht _
  have hanti : AntitoneOn (fun r : ℝ => r ^ (-p)) (Set.Ioi 0) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.2 hp.le)
  have hconv : ConvexOn ℝ (Set.Ioi 0) fun r : ℝ => r ^ (-p) := convexOn_rpow_neg hp
  -- So the Convex lower bound applies.
  exact convex_lower_bound (fun r => r ^ (-p)) hpos hanti hconv n hn x hx

/-- **Albouy–Moeckel kernel.** The case `p = 2`: for even `n` and `x_1 < ⋯ < x_n`, the Pfaffian
of `A_ij = (x_j - x_i)^(-2)` is positive. -/
theorem albouy_moeckel_pos (n : ℕ) (hn : Even n) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel (fun r => r ^ (-2 : ℝ)) x) > 0 := by
  obtain ⟨hge, hpos⟩ := power_kernel_lower_bound 2 two_pos n hn x hx
  exact lt_of_lt_of_le hpos hge
