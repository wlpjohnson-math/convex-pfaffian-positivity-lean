import PfaffianLean.Pfaffian

/-!
# Sanity tests for the Pfaffian

Small cases of the definition: the `2 × 2` and `4 × 4` formulas, a numerical `4 × 4` value
evaluated by `#guard`, and `Pf(𝒯) = 1` for the skew matrix `𝒯` with all upper entries `1` at
`n = 2, 4, 6`.
-/

open Finset

namespace PfaffianTests

variable {R : Type*} [CommRing R]

/-- `Pf` of a `2 × 2` matrix: `Pf [[0, a], [-a, 0]] = a`. -/
theorem pfaffian_Icc_two (A : Matrix ℕ ℕ R) : pfaffian (Icc 1 2) A = A 1 2 := by
  rw [show (Icc 1 2 : Finset ℕ) = insert 1 {2} by decide]
  simp [pfaffian_insert_of_forall_lt, pfaffian_empty, filter_singleton]

/-- The `4 × 4` formula: `Pf A = A₁₂ A₃₄ - A₁₃ A₂₄ + A₁₄ A₂₃`. -/
theorem pfaffian_Icc_four (A : Matrix ℕ ℕ R) :
    pfaffian (Icc 1 4) A = A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3 := by
  rw [show (Icc 1 4 : Finset ℕ) = insert 1 (insert 2 (insert 3 {4})) by decide]
  simp [pfaffian_insert_of_forall_lt, pfaffian_empty, sum_insert, filter_insert,
    erase_insert_of_ne, filter_singleton]
  ring

-- A numerical `4 × 4` value, for the skew matrix with `A_ij = 10 i + j` for `i < j`:
-- `A₁₂ A₃₄ - A₁₃ A₂₄ + A₁₄ A₂₃ = 408 - 312 + 322 = 418`. `#guard` succeeds silently, which the
-- `#`-command linter would flag.
set_option linter.hashCommand false in
#guard pfaffian (Icc 1 4) (Matrix.of fun i j => ((10 * i + j : ℕ) : ℤ)) = 418

/-- The skew matrix `𝒯` with all upper entries `1`. -/
def skewOnes : Matrix ℕ ℕ R :=
  skewExtension (Matrix.of fun _ _ => 1)

theorem pfaffian_skewOnes_two : pfaffian (Icc 1 2) (skewOnes : Matrix ℕ ℕ R) = 1 := by
  rw [pfaffian_Icc_two]
  simp [skewOnes, skewExtension]

theorem pfaffian_skewOnes_four : pfaffian (Icc 1 4) (skewOnes : Matrix ℕ ℕ R) = 1 := by
  rw [pfaffian_Icc_four]
  simp [skewOnes, skewExtension]

theorem pfaffian_skewOnes_six : pfaffian (Icc 1 6) (skewOnes : Matrix ℕ ℕ R) = 1 := by
  rw [show (Icc 1 6 : Finset ℕ) = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 {6})))) by
    decide]
  simp [pfaffian_insert_of_forall_lt, pfaffian_empty, sum_insert, filter_insert,
    erase_insert_of_ne, filter_singleton, skewOnes, skewExtension]
  norm_num

end PfaffianTests
