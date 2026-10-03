import PfaffianLean.Pfaffian

/-!
# Sanity tests for the Pfaffian

Reference: `refs/pfaffian-convex.tex`, Section 1.
-/

open Finset

namespace PfaffianTests

variable {R : Type*} [CommRing R]

/-- `Pf` of a `2 × 2` matrix: `Pf [[0, a], [-a, 0]] = a`. -/
theorem pfaffian_Icc_two (A : Matrix ℕ ℕ R) : pfaffian (Icc 1 2) A = A 1 2 := by
  rw [show (Icc 1 2 : Finset ℕ) = insert 1 {2} by decide]
  simp [pfaffian_insert_of_forall_lt, pfaffian_empty, filter_singleton]

/-- Equation (2) of the reference: `Pf A = A₁₂ A₃₄ - A₁₃ A₂₄ + A₁₄ A₂₃`. -/
theorem pfaffian_Icc_four (A : Matrix ℕ ℕ R) :
    pfaffian (Icc 1 4) A = A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3 := by
  rw [show (Icc 1 4 : Finset ℕ) = insert 1 (insert 2 (insert 3 {4})) by decide]
  simp [pfaffian_insert_of_forall_lt, pfaffian_empty, sum_insert, filter_insert,
    erase_insert_of_ne, filter_singleton]
  ring

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
