import PfaffianLean.LowerBounds

/-!
# Power kernels

The Convex lower bound specialised to `f(r) = r^(-p)` (`Real.rpow`), `p > 0`: for even `n` and
`x_1 < ⋯ < x_n`, `Pf A_f(x) ≥ ((x_n - x_1)^(-p))^(n/2) > 0`. The case `p = 2` is the
Albouy–Moeckel kernel.
-/

open Finset

/-- **Power kernels.** For `p > 0`, even `n` and `x_1 < ⋯ < x_n`, the Convex lower bound for
`f(r) = r^(-p)`: `Pf A_f(x) ≥ ((x_n - x_1)^(-p))^(n/2) > 0`. -/
theorem power_kernel_lower_bound (p : ℝ) (hp : 0 < p) (n : ℕ) (hn : Even n) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel (fun r => r ^ (-p)) x) ≥ ((x n - x 1) ^ (-p)) ^ (n / 2) ∧
      ((x n - x 1) ^ (-p)) ^ (n / 2) > 0 := by
  sorry

/-- **Albouy–Moeckel kernel.** The case `p = 2`: for even `n` and `x_1 < ⋯ < x_n`, the Pfaffian
of `A_ij = (x_j - x_i)^(-2)` is positive. -/
theorem albouy_moeckel_pos (n : ℕ) (hn : Even n) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel (fun r => r ^ (-2 : ℝ)) x) > 0 := by
  sorry
