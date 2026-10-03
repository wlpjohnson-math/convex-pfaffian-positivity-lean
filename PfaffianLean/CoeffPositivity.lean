import PfaffianLean.Families
import PfaffianLean.TwinRows
import PfaffianLean.PfaffianFacts

/-!
# Coefficient positivity

Reference: `refs/pfaffian-convex.tex`, Section 3, Theorem (Coefficient positivity).

For every `n`, `F_n` (`intervalPfaffian n`) has nonnegative integer coefficients, it is
homogeneous of degree `n / 2`, and for even `n ≥ 2` the coefficient of `a_[1,n]^(n/2)` is `1`.
We also check the expansion of `F_4`.

## Proof outline (following the reference)

* Homogeneity: every term of the matching expansion is a product of `n / 2` entries, each a sum
  of variables.
* Corner coefficient: setting `a_J = 0` for `J ≠ [1, n]` turns the matrix into `a_[1,n] • 𝒯_n`,
  and `Pf(a 𝒯_n) = a ^ (n/2) Pf(𝒯_n) = a ^ (n/2)`.
* Nonnegativity, by induction on `n`: for a monomial `a^μ` with support `S`, the coefficient of
  `a^μ` in `F_n` equals its coefficient in `F^S` (`a_J := 0` for `J ∉ S`); (i) if a point lies in
  no `J ∈ S`, `F^S = 0`; (ii) otherwise some gap `y` is cut by no `J ∈ S`, the rows `y`, `y + 1`
  are twins, and `F^S = s · F_{n-2}(b)` with `s` and the `b_{J'}` sums of variables.
-/

open Finset MvPolynomial

/-! ### Statements -/

/-- The variable `a_[1,n]` exists for `n ≥ 2`: `(1, n) ∈ I_n`. -/
theorem corner_mem_intervals {n : ℕ} (hn : 2 ≤ n) : (1, n) ∈ intervals n := by
  sorry

/-- **Coefficient positivity**, nonnegativity: every coefficient of `F_n` is `≥ 0`. -/
theorem coeff_nonneg (n : ℕ) (m : intervals n →₀ ℕ) : 0 ≤ (intervalPfaffian n).coeff m := by
  sorry

/-- **Coefficient positivity**, homogeneity: `F_n` is homogeneous of degree `n / 2`. -/
theorem intervalPfaffian_isHomogeneous (n : ℕ) : (intervalPfaffian n).IsHomogeneous (n / 2) := by
  sorry

/-- **Coefficient positivity**, corner coefficient: for even `n ≥ 2`, the coefficient of
`a_[1,n] ^ (n / 2)` in `F_n` is `1`. -/
theorem coeff_corner (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) :
    (intervalPfaffian n).coeff (Finsupp.single ⟨(1, n), corner_mem_intervals h2⟩ (n / 2)) = 1 := by
  sorry

/-- **The `F_4` check**: `F_4 = a14² + a14 (a12 + a13 + a23 + a24 + a34) + a12 a34 + a12 a24 +
a13 a34`, nine monomials, each with coefficient `1`. Here `a p q` is the variable of `[p, q]`. -/
theorem intervalPfaffian_four :
    let a : ℕ → ℕ → MvPolynomial (intervals 4) ℤ := fun p q =>
      if h : (p, q) ∈ intervals 4 then X ⟨(p, q), h⟩ else 0
    intervalPfaffian 4 = a 1 4 ^ 2 + a 1 4 * (a 1 2 + a 1 3 + a 2 3 + a 2 4 + a 3 4) +
      a 1 2 * a 3 4 + a 1 2 * a 2 4 + a 1 3 * a 3 4 := by
  sorry

/-! ### Internal steps of the nonnegativity proof -/

/-- `A^T`: the matrix of `F_n` with `a_J := 0` for `J ∉ T`. Its Pfaffian is `F^T`. -/
noncomputable def restrictedMatrix (n : ℕ) (T : Finset (intervals n)) :
    Matrix ℕ ℕ (MvPolynomial (intervals n) ℤ) :=
  Matrix.of fun i j => ∑ J ∈ T with i ∈ Icc J.1.1 J.1.2 ∧ j ∈ Icc J.1.1 J.1.2, X J

/-- "The coefficient of `a^μ` in `F_n` equals its coefficient in `F^S`" when the support of `μ`
is contained in `S`. -/
theorem coeff_intervalPfaffian_eq_restricted (n : ℕ) (T : Finset (intervals n))
    (μ : intervals n →₀ ℕ) (hμ : μ.support ⊆ T) :
    (intervalPfaffian n).coeff μ = (pfaffian (Icc 1 n) (restrictedMatrix n T)).coeff μ := by
  sorry

/-- Case (i): "If some point `y` of `[n]` lies in no `J ∈ S`, then row `y` of `A^S` is zero" and
`F^S = 0`. -/
theorem restricted_eq_zero_of_uncovered (n : ℕ) (T : Finset (intervals n)) {y : ℕ}
    (hy : y ∈ Icc 1 n) (hunc : ∀ J ∈ T, y ∉ Icc J.1.1 J.1.2) :
    pfaffian (Icc 1 n) (restrictedMatrix n T) = 0 := by
  sorry

/-- Case (ii), counting cut gaps: if `2 #S ≤ n`, `n ≥ 2`, and every point of `[n]` lies in some
`J ∈ S`, then some gap `y ∈ [1, n - 1]` is cut by no `J ∈ S` (`J = [p, q]` cuts `y` iff `q = y`
or `p = y + 1`). -/
theorem exists_uncut_gap (n : ℕ) (hn : 2 ≤ n) (T : Finset (intervals n)) (hT : 2 * #T ≤ n)
    (hcov : ∀ i ∈ Icc 1 n, ∃ J ∈ T, i ∈ Icc J.1.1 J.1.2) :
    ∃ y ∈ Icc 1 (n - 1), ∀ J ∈ T, J.1.2 ≠ y ∧ J.1.1 ≠ y + 1 := by
  sorry

/-- The endpoints of `φ(J ∖ {y, y + 1})` for an interval `J = [p, q]` not cut at `y`, where
`φ : [n] ∖ {y, y + 1} → [n - 2]` is the increasing bijection (`k ↦ k` for `k < y`,
`k ↦ k - 2` for `k > y + 1`). When `φ(J ∖ {y, y + 1})` has at most one point, the result has
first coordinate `≥` second, so it is not in `I_{n-2}`. -/
def collapse (y : ℕ) (J : ℕ × ℕ) : ℕ × ℕ :=
  (if J.1 ≤ y then J.1 else J.1 - 2, if J.2 < y then J.2 else J.2 - 2)

/-- "The reduced Pfaffian": if the gap `y` is cut by no `J ∈ S`, then
`F^S = s · F_{n-2}(b)`, with `s = ∑_{J ∈ S, J ∋ y} a_J` and
`b_{J'} = ∑_{J ∈ S, φ(J ∖ {y, y+1}) = J'} a_J`. -/
theorem restricted_eq_mul_aeval {n : ℕ} (hn : 2 ≤ n) (T : Finset (intervals n)) {y : ℕ}
    (hy : y ∈ Icc 1 (n - 1)) (huncut : ∀ J ∈ T, J.1.2 ≠ y ∧ J.1.1 ≠ y + 1) :
    pfaffian (Icc 1 n) (restrictedMatrix n T) =
      (∑ J ∈ T with y ∈ Icc J.1.1 J.1.2, X J) *
        aeval (fun J' : intervals (n - 2) => ∑ J ∈ T with collapse y J.1 = J'.1, X J)
          (intervalPfaffian (n - 2)) := by
  sorry
