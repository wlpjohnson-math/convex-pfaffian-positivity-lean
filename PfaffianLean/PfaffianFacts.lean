import PfaffianLean.Pfaffian

/-!
# Further facts about Pfaffians

Reference: `refs/pfaffian-convex.tex`, Section 1.

* `PerfectMatching.two_mul_card`: a perfect matching of `S` has `#S / 2` edges.
* `pfaffian_smul`: `Pf(c A) = c ^ (#S / 2) Pf A`.
* `pfaffian_image_strictMono`: the Pfaffian is unchanged under a strictly monotone change of
  index (used for the map `φ` in Coefficient positivity).
* `pfaffian_eq_zero_of_row`: a zero row (on the upper entries) makes the Pfaffian vanish.
* `pfaffian_skewOnes`: the skew matrix `𝒯` with all upper entries `1` has Pfaffian `1`, proved
  as in the reference by the first-row expansion.
-/

open Finset

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

/-- A perfect matching of `S` has `#S / 2` edges: `2 * #M = #S`. -/
theorem PerfectMatching.two_mul_card {S : Finset ι} {M : Finset (ι × ι)}
    (hM : M ∈ perfectMatchings S) : 2 * #M = #S := by
  sorry

/-- `Pf(c A) = c ^ (#S / 2) Pf A`. -/
theorem pfaffian_smul (S : Finset ι) (c : R) (A : Matrix ι ι R) :
    pfaffian S (c • A) = c ^ (#S / 2) * pfaffian S A := by
  sorry

/-- **Reindexing.** The Pfaffian is unchanged under a strictly monotone change of index: the
Pfaffian of `A` on `ψ(S)` is the Pfaffian on `S` of `A` read through `ψ`. -/
theorem pfaffian_image_strictMono {κ : Type*} [LinearOrder κ] {ψ : ι → κ} (hψ : StrictMono ψ)
    (S : Finset ι) (A : Matrix κ κ R) :
    pfaffian (S.image ψ) A = pfaffian S (A.submatrix ψ ψ) := by
  sorry

/-- A zero row: if every entry of row and column `y ∈ S` that the Pfaffian reads is `0`, then
`Pf_S A = 0`. -/
theorem pfaffian_eq_zero_of_row {S : Finset ι} {A : Matrix ι ι R} {y : ι} (hy : y ∈ S)
    (hrow : ∀ z ∈ S, y < z → A y z = 0) (hcol : ∀ z ∈ S, z < y → A z y = 0) :
    pfaffian S A = 0 := by
  sorry

/-- `Pf(𝒯) = 1` on every index set of even size. -/
theorem pfaffian_skewExtension_ones_of_even_card {S : Finset ι} (hS : Even #S) :
    pfaffian S (skewExtension (Matrix.of fun _ _ => (1 : R))) = 1 := by
  sorry

/-- **`Pf(𝒯_n) = 1`** for every even `n`, where `𝒯_n` is the skew matrix with all upper entries
`1`. -/
theorem pfaffian_skewOnes (n : ℕ) (hn : Even n) :
    pfaffian (Icc 1 n) (skewExtension (Matrix.of fun _ _ => (1 : R))) = 1 := by
  sorry
