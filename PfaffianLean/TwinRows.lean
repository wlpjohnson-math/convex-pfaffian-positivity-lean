import PfaffianLean.Pfaffian

/-!
# The Twin rows lemma

Reference: `refs/pfaffian-convex.tex`, Section 3, Lemma (Twin rows).

If two consecutive rows `y < y'` of `S` are twins, then
`Pf_S A = A_{y y'} · Pf_{S ∖ {y, y'}} A`.

Since `pfaffian` reads only the entries `A a b` with `a < b`, the twin condition is stated on
those entries: `A y z = A y' z` for `z ∈ S` with `z > y'`, and `A z y = A z y'` for `z ∈ S` with
`z < y`. For a skew-symmetric `A` this is the reference's condition `A_{y,z} = A_{y+1,z}` for all
`z ∉ {y, y+1}`.
-/

open Finset

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

/-- **Twin rows**, for two consecutive elements `y < y'` of an arbitrary finite index set `S`. -/
theorem pf_twin_rows_consecutive {S : Finset ι} (A : Matrix ι ι R) {y y' : ι} (hy : y ∈ S)
    (hy' : y' ∈ S) (hyy' : y < y') (hcons : ∀ z ∈ S, ¬(y < z ∧ z < y'))
    (htwin_right : ∀ z ∈ S, y' < z → A y z = A y' z)
    (htwin_left : ∀ z ∈ S, z < y → A z y = A z y') :
    pfaffian S A = A y y' * pfaffian (S \ {y, y'}) A := by
  sorry

/-- **Twin rows**, the reference's form: rows `y` and `y + 1` of `[n]`. -/
theorem pf_twin_rows (n : ℕ) (A : Matrix ℕ ℕ R) {y : ℕ} (hy : 1 ≤ y) (hyn : y + 1 ≤ n)
    (htwin_right : ∀ z ∈ Icc 1 n, y + 1 < z → A y z = A (y + 1) z)
    (htwin_left : ∀ z ∈ Icc 1 n, z < y → A z y = A z (y + 1)) :
    pfaffian (Icc 1 n) A = A y (y + 1) * pfaffian (Icc 1 n \ {y, y + 1}) A := by
  sorry
