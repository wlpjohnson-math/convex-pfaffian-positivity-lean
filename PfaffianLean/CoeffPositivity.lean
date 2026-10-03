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

/-- The variable `a_[1,n]` exists for `n ≥ 2`: `(1, n) ∈ I_n`. -/
theorem corner_mem_intervals {n : ℕ} (hn : 2 ≤ n) : (1, n) ∈ intervals n := by
  simp only [intervals, mem_filter, mem_product, mem_Icc]
  omega

/-! ### Homogeneity -/

/-- **Coefficient positivity**, homogeneity: `F_n` is homogeneous of degree `n / 2`. -/
theorem intervalPfaffian_isHomogeneous (n : ℕ) : (intervalPfaffian n).IsHomogeneous (n / 2) := by
  -- "Every entry of the matrix is a `ℤ`-linear form in the `a_J`".
  have hentry : ∀ i j, (intervalMatrix n i j).IsHomogeneous 1 := fun i j =>
    IsHomogeneous.sum _ _ _ fun J _ => isHomogeneous_X ℤ J
  -- "and every term of the matching expansion is a product of `n/2` entries."
  refine IsHomogeneous.sum _ _ _ fun M hM => ?_
  have hcard : #M = n / 2 := by
    have := PerfectMatching.two_mul_card hM
    simp only [Nat.card_Icc, add_tsub_cancel_right] at this
    omega
  have hsign : ((-1 : MvPolynomial (intervals n) ℤ) ^ crossings M).IsHomogeneous 0 := by
    simpa using ((isHomogeneous_C (intervals n) (1 : ℤ)).neg).pow (crossings M)
  have hprod := IsHomogeneous.prod M (fun e => intervalMatrix n e.1 e.2) (fun _ => 1)
    fun e _ => hentry e.1 e.2
  simpa [hcard] using hsign.mul hprod

/-! ### Bookkeeping: polynomials with nonnegative coefficients -/

/-- The integer polynomials with nonnegative coefficients form a subsemiring. -/
def nonnegCoeffs (σ : Type*) : Subsemiring (MvPolynomial σ ℤ) where
  carrier := {p | ∀ m, 0 ≤ p.coeff m}
  mul_mem' := by
    intro p q hp hq m
    classical
    rw [coeff_mul]
    exact sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)
  one_mem' := by
    intro m
    classical
    rw [coeff_one]
    split_ifs <;> norm_num
  add_mem' := by
    intro p q hp hq m
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply]
    exact add_nonneg (hp m) (hq m)
  zero_mem' := by
    intro m
    simp

theorem mem_nonnegCoeffs {σ : Type*} {p : MvPolynomial σ ℤ} :
    p ∈ nonnegCoeffs σ ↔ ∀ m, 0 ≤ p.coeff m :=
  Iff.rfl

theorem X_mem_nonnegCoeffs {σ : Type*} (i : σ) : (X i : MvPolynomial σ ℤ) ∈ nonnegCoeffs σ := by
  intro m
  classical
  rw [coeff_X]
  split_ifs <;> norm_num

/-- A sum of variables has nonnegative coefficients. -/
theorem sum_X_mem_nonnegCoeffs {σ : Type*} (s : Finset σ) :
    ∑ i ∈ s, (X i : MvPolynomial σ ℤ) ∈ nonnegCoeffs σ :=
  sum_mem fun i _ => X_mem_nonnegCoeffs i

/-- Substituting polynomials with nonnegative coefficients into one with nonnegative
coefficients gives a polynomial with nonnegative coefficients. -/
theorem aeval_mem_nonnegCoeffs {σ τ : Type*} {b : τ → MvPolynomial σ ℤ}
    (hb : ∀ i, b i ∈ nonnegCoeffs σ) {p : MvPolynomial τ ℤ} (hp : p ∈ nonnegCoeffs τ) :
    aeval b p ∈ nonnegCoeffs σ := by
  rw [aeval_def, eval₂_eq]
  refine sum_mem fun d _ => mul_mem ?_ (prod_mem fun i _ => pow_mem (hb i) _)
  intro m
  classical
  rw [algebraMap_eq, coeff_C]
  split_ifs
  · exact hp d
  · exact le_rfl

/-! ### Restriction to the support of a monomial -/

/-- `A^T`: the matrix of `F_n` with `a_J := 0` for `J ∉ T`. Its Pfaffian is `F^T`. -/
noncomputable def restrictedMatrix (n : ℕ) (T : Finset (intervals n)) :
    Matrix ℕ ℕ (MvPolynomial (intervals n) ℤ) :=
  Matrix.of fun i j => ∑ J ∈ T with i ∈ Icc J.1.1 J.1.2 ∧ j ∈ Icc J.1.1 J.1.2, X J

/-- Setting the variables outside `T` to `0` does not change the coefficients of monomials
supported in `T`. -/
theorem coeff_aeval_restrict {σ : Type*} [DecidableEq σ] (T : Finset σ) (p : MvPolynomial σ ℤ)
    (μ : σ →₀ ℕ) (hμ : μ.support ⊆ T) :
    (aeval (fun i => if i ∈ T then X i else 0) p).coeff μ = p.coeff μ := by
  induction p using MvPolynomial.induction_on generalizing μ with
  | C a => simp
  | add p q hp hq =>
    rw [map_add]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply]
    rw [hp μ hμ, hq μ hμ]
  | mul_X p i hp =>
    rw [map_mul, aeval_X, coeff_mul_X']
    by_cases hi : i ∈ T
    · rw [ite_eq_left hi, coeff_mul_X']
      split_ifs with hiμ
      · exact hp _ (fun j hj => hμ (Finsupp.support_tsub hj))
      · rfl
    · rw [ite_eq_right hi, mul_zero, ite_eq_right fun h => hi (hμ h)]
      simp

/-- "The coefficient of `a^μ` in `F_n` equals its coefficient in `F^S`" when the support of `μ`
is contained in `S`. -/
theorem coeff_intervalPfaffian_eq_restricted (n : ℕ) (T : Finset (intervals n))
    (μ : intervals n →₀ ℕ) (hμ : μ.support ⊆ T) :
    (intervalPfaffian n).coeff μ = (pfaffian (Icc 1 n) (restrictedMatrix n T)).coeff μ := by
  set kill : intervals n → MvPolynomial (intervals n) ℤ := fun J => if J ∈ T then X J else 0
  -- `F^S` is `F_n` with `a_J := 0` for `J ∉ S` (evaluation lemma).
  have hFT : pfaffian (Icc 1 n) (restrictedMatrix n T) = aeval kill (intervalPfaffian n) := by
    have heval := RingHom.map_pfaffian (aeval kill).toRingHom (Icc 1 n) (intervalMatrix n)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at heval
    rw [intervalPfaffian, heval]
    congr 1
    funext i j
    simp only [restrictedMatrix, intervalMatrix, Matrix.map_apply, Matrix.of_apply, map_sum,
      aeval_X, kill]
    rw [sum_filter, sum_filter, ← Fintype.sum_ite_mem T]
    refine sum_congr rfl fun J _ => ?_
    split_ifs <;> rfl
  rw [hFT, coeff_aeval_restrict T _ μ hμ]

/-- Case (i): "If some point `y` of `[n]` lies in no `J ∈ S`, then row `y` of `A^S` is zero" and
`F^S = 0`. -/
theorem restricted_eq_zero_of_uncovered (n : ℕ) (T : Finset (intervals n)) {y : ℕ}
    (hy : y ∈ Icc 1 n) (hunc : ∀ J ∈ T, y ∉ Icc J.1.1 J.1.2) :
    pfaffian (Icc 1 n) (restrictedMatrix n T) = 0 := by
  -- "Every perfect matching uses an entry of that row, so `F^S = 0`."
  refine pfaffian_eq_zero_of_row hy (fun z _ _ => ?_) (fun z _ _ => ?_)
  · exact sum_eq_zero fun J hJ => absurd (mem_filter.1 hJ).2.1 (hunc J (mem_filter.1 hJ).1)
  · exact sum_eq_zero fun J hJ => absurd (mem_filter.1 hJ).2.2 (hunc J (mem_filter.1 hJ).1)

/-! ### Case (ii): an uncut gap -/

/-- Case (ii), counting cut gaps: if `2 #S ≤ n`, `n ≥ 2`, and every point of `[n]` lies in some
`J ∈ S`, then some gap `y ∈ [1, n - 1]` is cut by no `J ∈ S` (`J = [p, q]` cuts `y` iff `q = y`
or `p = y + 1`). -/
theorem exists_uncut_gap (n : ℕ) (hn : 2 ≤ n) (T : Finset (intervals n)) (hT : 2 * #T ≤ n)
    (hcov : ∀ i ∈ Icc 1 n, ∃ J ∈ T, i ∈ Icc J.1.1 J.1.2) :
    ∃ y ∈ Icc 1 (n - 1), ∀ J ∈ T, J.1.2 ≠ y ∧ J.1.1 ≠ y + 1 := by
  by_contra hall
  push Not at hall
  -- The gaps cut by `J = [p, q]`: "the gap `q` (if `q ≤ n - 1`) and the gap `p - 1` (if `p ≥ 2`)".
  set cuts : intervals n → Finset ℕ := fun J => {y ∈ Icc 1 (n - 1) | J.1.2 = y ∨ J.1.1 = y + 1}
  set w : intervals n → ℕ := fun J => (if J.1.1 = 1 then 0 else 1) + (if J.1.2 = n then 0 else 1)
  have hJ : ∀ J : intervals n, 1 ≤ J.1.1 ∧ J.1.1 < J.1.2 ∧ J.1.2 ≤ n := fun J => by
    have := J.2
    simp only [intervals, mem_filter, mem_product, mem_Icc] at this
    omega
  -- "Each `J` cuts at most two gaps", at most one if `p = 1` or `q = n`, none if `J = [1, n]`.
  have hcuts : ∀ J, #(cuts J) ≤ w J := by
    intro J
    obtain ⟨h1, h12, h2⟩ := hJ J
    have hsub : cuts J ⊆ (if J.1.2 = n then ∅ else {J.1.2}) ∪
        (if J.1.1 = 1 then ∅ else {J.1.1 - 1}) := by
      intro y hy
      simp only [cuts, mem_filter, mem_Icc] at hy
      split_ifs <;> simp <;> omega
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    simp only [w]
    split_ifs <;> simp [add_comm]
  -- Every gap is cut ("by contradiction"), so `n - 1 ≤ ∑_J #cuts(J)`.
  have hcover : Icc 1 (n - 1) ⊆ T.biUnion cuts := by
    intro y hy
    obtain ⟨J, hJT, hJy⟩ := hall y hy
    exact mem_biUnion.2 ⟨J, hJT, mem_filter.2 ⟨hy, by omega⟩⟩
  have hle : n - 1 ≤ ∑ J ∈ T, w J := by
    have := (card_le_card hcover).trans (card_biUnion_le.trans (sum_le_sum fun J _ => hcuts J))
    simpa using this
  -- "The point `1` lies in some `J ∈ S`, which then has `p = 1`"; "the point `n` lies in some
  -- `J' ∈ S`, which has `q = n`". Hence `∑_J w(J) ≤ 2 |S| - 2`.
  obtain ⟨J₁, hJ₁, h1J₁⟩ := hcov 1 (mem_Icc.2 ⟨le_rfl, by omega⟩)
  obtain ⟨Jn, hJn, hnJn⟩ := hcov n (mem_Icc.2 ⟨by omega, le_rfl⟩)
  have hp1 : J₁.1.1 = 1 := by
    have := hJ J₁
    rw [mem_Icc] at h1J₁
    omega
  have hqn : Jn.1.2 = n := by
    have := hJ Jn
    rw [mem_Icc] at hnJn
    omega
  have hw : ∑ J ∈ T, w J + #{J ∈ T | J.1.1 = 1} + #{J ∈ T | J.1.2 = n} = 2 * #T := by
    simp only [w, sum_add_distrib, sum_ite, sum_const_zero, sum_const, smul_eq_mul, mul_one,
      zero_add]
    have h1 := card_filter_add_card_filter_not (s := T) (fun J => J.1.1 = 1)
    have h2 := card_filter_add_card_filter_not (s := T) (fun J => J.1.2 = n)
    omega
  have hA : 1 ≤ #{J ∈ T | J.1.1 = 1} := card_pos.2 ⟨J₁, mem_filter.2 ⟨hJ₁, hp1⟩⟩
  have hB : 1 ≤ #{J ∈ T | J.1.2 = n} := card_pos.2 ⟨Jn, mem_filter.2 ⟨hJn, hqn⟩⟩
  -- "Hence at most `2|S| - 2 ≤ n - 2` of the `n - 1` gaps are cut."
  omega

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
  rw [mem_Icc] at hy
  set b : intervals (n - 2) → MvPolynomial (intervals n) ℤ :=
    fun J' => ∑ J ∈ T with collapse y J.1 = J'.1, X J
  have hJ : ∀ J : intervals n, 1 ≤ J.1.1 ∧ J.1.1 < J.1.2 ∧ J.1.2 ≤ n := fun J => by
    have := J.2
    simp only [intervals, mem_filter, mem_product, mem_Icc] at this
    omega
  -- "For every `J ∈ S`, then, `y` lies in `J` iff `y + 1` lies in `J`. So for every
  -- `z ∉ {y, y+1}` the `(y, z)` and `(y+1, z)` entries of `A^S` are the same sum." By the
  -- Twin rows lemma, `F^S = s · Pf(A^S_{[n] ∖ {y, y+1}})`.
  have htwin := pf_twin_rows n (restrictedMatrix n T) hy.1 (by omega)
    (fun z _ hz => by
      simp only [restrictedMatrix, Matrix.of_apply]
      refine sum_congr (filter_congr fun J hJT => ?_) fun _ _ => rfl
      have := hJ J
      have := huncut J hJT
      simp only [mem_Icc]
      omega)
    (fun z _ hz => by
      simp only [restrictedMatrix, Matrix.of_apply]
      refine sum_congr (filter_congr fun J hJT => ?_) fun _ _ => rfl
      have := hJ J
      have := huncut J hJT
      simp only [mem_Icc]
      omega)
  -- "`s := A^S_{y,y+1} = ∑_{J ∈ S, J ∋ y} a_J`."
  have hs : restrictedMatrix n T y (y + 1) = ∑ J ∈ T with y ∈ Icc J.1.1 J.1.2, X J := by
    simp only [restrictedMatrix, Matrix.of_apply]
    refine sum_congr (filter_congr fun J hJT => ?_) fun _ _ => rfl
    have := huncut J hJT
    simp only [mem_Icc]
    omega
  rw [htwin, hs]
  congr 1
  -- "The reduced Pfaffian. Let `φ` be the increasing bijection of `[n] ∖ {y, y+1}` onto
  -- `[n - 2]`": we reindex along its inverse `ψ`.
  set ψ : ℕ → ℕ := fun k => if k < y then k else k + 2 with hψ_def
  have hψ : StrictMono ψ := by
    intro a b hab
    simp only [hψ_def]
    split_ifs <;> omega
  have himage : Icc 1 n \ {y, y + 1} = (Icc 1 (n - 2)).image ψ := by
    ext x
    simp only [mem_sdiff, mem_Icc, mem_insert, mem_singleton, mem_image, hψ_def]
    constructor
    · rintro ⟨hx, hxy⟩
      refine ⟨if x < y then x else x - 2, ?_, ?_⟩ <;> split_ifs <;> omega
    · rintro ⟨a, ha, rfl⟩
      split_ifs <;> omega
  rw [himage, pfaffian_image_strictMono hψ]
  -- "The `(φ(i), φ(j))` entry of the reduced matrix is then `∑_{J' ∋ φ(i), φ(j)} b_{J'}`."
  have hentry : ∀ i ∈ Icc 1 (n - 2), ∀ j ∈ Icc 1 (n - 2), i < j →
      (restrictedMatrix n T).submatrix ψ ψ i j = (intervalMatrix (n - 2)).map (aeval b) i j := by
    intro i hi j hj hij
    rw [mem_Icc] at hi hj
    simp only [Matrix.submatrix_apply, restrictedMatrix, intervalMatrix, Matrix.map_apply,
      Matrix.of_apply, map_sum, aeval_X, b]
    -- "For `i < j` in `[n] ∖ {y, y+1}`, `J` contains `i` and `j` iff `φ(J ∖ {y, y+1})` contains
    -- `φ(i)` and `φ(j)`": here with `ψ = φ⁻¹`, and `φ(J ∖ {y, y+1})` given by `collapse`.
    have key : ∀ J ∈ T, (ψ i ∈ Icc J.1.1 J.1.2 ∧ ψ j ∈ Icc J.1.1 J.1.2) ↔
        ∃ J' : intervals (n - 2),
          (i ∈ Icc J'.1.1 J'.1.2 ∧ j ∈ Icc J'.1.1 J'.1.2) ∧ collapse y J.1 = J'.1 := by
      intro J hJT
      have hJJ := hJ J
      have hunc := huncut J hJT
      constructor
      · intro h
        have hmem : collapse y J.1 ∈ intervals (n - 2) := by
          simp only [intervals, collapse, mem_filter, mem_product, mem_Icc]
          simp only [hψ_def, mem_Icc] at h
          split_ifs at h ⊢ <;> omega
        refine ⟨⟨collapse y J.1, hmem⟩, ?_, rfl⟩
        simp only [collapse, mem_Icc]
        simp only [hψ_def, mem_Icc] at h
        split_ifs at h ⊢ <;> omega
      · rintro ⟨J', hJ', hc⟩
        have hJ'2 := J'.2
        rw [← hc] at hJ'
        rw [← hc] at hJ'2
        simp only [intervals, collapse, mem_filter, mem_product, mem_Icc] at hJ' hJ'2 ⊢
        simp only [hψ_def]
        split_ifs at hJ' hJ'2 ⊢ <;> omega
    -- "intervals whose image has at most one point enter no entry": each `J ∈ S` enters through
    -- the single interval `φ(J ∖ {y, y+1})`, so we exchange the two sums.
    rw [sum_filter, sum_filter]
    have hinner : ∀ J' : intervals (n - 2),
        (if i ∈ Icc J'.1.1 J'.1.2 ∧ j ∈ Icc J'.1.1 J'.1.2 then
          ∑ J ∈ T with collapse y J.1 = J'.1, (X J : MvPolynomial (intervals n) ℤ) else 0) =
        ∑ J ∈ T, if (i ∈ Icc J'.1.1 J'.1.2 ∧ j ∈ Icc J'.1.1 J'.1.2) ∧ collapse y J.1 = J'.1 then
          X J else 0 := by
      intro J'
      rw [sum_filter]
      by_cases h : i ∈ Icc J'.1.1 J'.1.2 ∧ j ∈ Icc J'.1.1 J'.1.2
      · simp only [h, true_and, ite_true]
      · simp only [h, false_and, ite_false, sum_const_zero]
    rw [sum_congr rfl fun J' _ => hinner J', sum_comm]
    refine sum_congr rfl fun J hJT => ?_
    rw [Fintype.sum_ite_eq_ite_exists _ (fun J' J'' h' h'' => Subtype.ext (h'.2.symm.trans h''.2))]
    exact if_congr (key J hJT) rfl rfl
  rw [pfaffian_congr hentry]
  -- "so `Pf(A^S_{[n] ∖ {y, y+1}}) = F_{n−2}(b)`" (evaluation lemma).
  have heval := RingHom.map_pfaffian (aeval b).toRingHom (Icc 1 (n - 2)) (intervalMatrix (n - 2))
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at heval
  rw [intervalPfaffian, heval]

/-! ### Nonnegativity -/

/-- **Coefficient positivity**, nonnegativity: every coefficient of `F_n` is `≥ 0`. -/
theorem coeff_nonneg (n : ℕ) (m : intervals n →₀ ℕ) : 0 ≤ (intervalPfaffian n).coeff m := by
  -- "Nonnegativity, by induction on `n`."
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hm : (intervalPfaffian n).coeff m = 0
  · rw [hm]
  -- "Fix a monomial `a^μ` of degree `n/2` with support `S`. So `|S| ≤ n/2`."
  have hdeg : Finsupp.weight 1 m = n / 2 := intervalPfaffian_isHomogeneous n hm
  set T := m.support
  have hT : 2 * #T ≤ n := by
    have hle : #T ≤ Finsupp.weight 1 m := by
      rw [Finsupp.weight_apply, Finsupp.sum, card_eq_sum_ones]
      exact sum_le_sum fun J hJ => by
        simpa using Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hJ)
    omega
  -- "The coefficient of `a^μ` in `F_n` equals its coefficient in `F^S`."
  rw [coeff_intervalPfaffian_eq_restricted n T m subset_rfl]
  -- (i) "If some point `y` of `[n]` lies in no `J ∈ S` … `F^S = 0`."
  by_cases hcov : ∀ i ∈ Icc 1 n, ∃ J ∈ T, i ∈ Icc J.1.1 J.1.2
  swap
  · push Not at hcov
    obtain ⟨y, hy, hunc⟩ := hcov
    rw [restricted_eq_zero_of_uncovered n T hy hunc]
    simp
  -- `F_0 = 1`.
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [show (Icc 1 0 : Finset ℕ) = ∅ by decide, pfaffian_empty, coeff_one]
    split_ifs <;> norm_num
  -- (ii) "Otherwise … some gap `y` is cut by no `J ∈ S`" (`n = 1` is excluded by `|S| ≤ n/2`).
  have hn : 2 ≤ n := by
    by_contra h
    obtain ⟨J, hJT, -⟩ := hcov 1 (mem_Icc.2 ⟨le_rfl, hpos⟩)
    have : 1 ≤ #T := card_pos.2 ⟨J, hJT⟩
    omega
  obtain ⟨y, hy, huncut⟩ := exists_uncut_gap n hn T hT hcov
  -- "`F^S = s F_{n−2}(b)`" by the reduced Pfaffian.
  rw [restricted_eq_mul_aeval hn T hy huncut]
  -- "By the induction hypothesis `F_{n−2}` has nonnegative integer coefficients. Each `b_{J'}` is
  -- a sum of indeterminates `a_J` (or `0`), and `s` is a sum of indeterminates. So `F^S` is a
  -- polynomial in the `a_J` with nonnegative integer coefficients."
  refine mul_mem (sum_X_mem_nonnegCoeffs _) (aeval_mem_nonnegCoeffs
    (fun J' => sum_X_mem_nonnegCoeffs _) fun m' => ih (n - 2) (by omega) m') m

/-! ### The corner coefficient -/

/-- **Coefficient positivity**, corner coefficient: for even `n ≥ 2`, the coefficient of
`a_[1,n] ^ (n / 2)` in `F_n` is `1`. -/
theorem coeff_corner (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) :
    (intervalPfaffian n).coeff (Finsupp.single ⟨(1, n), corner_mem_intervals h2⟩ (n / 2)) = 1 := by
  set J₀ : intervals n := ⟨(1, n), corner_mem_intervals h2⟩
  -- "Setting `a_J = 0` for `J ≠ [1, n]` …"
  rw [coeff_intervalPfaffian_eq_restricted n {J₀} _ Finsupp.support_single_subset]
  -- "… gives `F_n = Pf(a_[1,n] 𝒯_n)`"
  have hmat : pfaffian (Icc 1 n) (restrictedMatrix n {J₀}) =
      pfaffian (Icc 1 n)
        ((X J₀ : MvPolynomial (intervals n) ℤ) •
          skewExtension (Matrix.of fun _ _ => (1 : MvPolynomial (intervals n) ℤ))) := by
    refine pfaffian_congr fun i hi j hj hij => ?_
    rw [mem_Icc] at hi hj
    have hJ : i ∈ Icc J₀.1.1 J₀.1.2 ∧ j ∈ Icc J₀.1.1 J₀.1.2 := by
      simp only [J₀, mem_Icc]
      omega
    simp only [restrictedMatrix, Matrix.of_apply, filter_singleton, ite_eq_left hJ, sum_singleton,
      Matrix.smul_apply, skewExtension, ite_eq_left hij, smul_eq_mul, mul_one]
  -- "This equals `a_[1,n]^{n/2} Pf(𝒯_n)`, and `Pf(𝒯_n) = 1`."
  rw [hmat, pfaffian_smul, Nat.card_Icc, add_tsub_cancel_right, pfaffian_skewOnes n hn, mul_one,
    X_pow_eq_monomial, coeff_monomial, ite_eq_left rfl]

/-! ### The `F_4` check -/

/-- **The `F_4` check**: `F_4 = a14² + a14 (a12 + a13 + a23 + a24 + a34) + a12 a34 + a12 a24 +
a13 a34`, nine monomials, each with coefficient `1`. Here `a p q` is the variable of `[p, q]`. -/
theorem intervalPfaffian_four :
    let a : ℕ → ℕ → MvPolynomial (intervals 4) ℤ := fun p q =>
      if h : (p, q) ∈ intervals 4 then X ⟨(p, q), h⟩ else 0
    intervalPfaffian 4 = a 1 4 ^ 2 + a 1 4 * (a 1 2 + a 1 3 + a 2 3 + a 2 4 + a 3 4) +
      a 1 2 * a 3 4 + a 1 2 * a 2 4 + a 1 3 * a 3 4 := by
  intro a
  -- Each entry is the sum of `a p q` over the intervals `[p, q] ∈ I_4` containing `i` and `j`.
  have hentry : ∀ i j, intervalMatrix 4 i j =
      ∑ J ∈ intervals 4 with i ∈ Icc J.1 J.2 ∧ j ∈ Icc J.1 J.2, a J.1 J.2 := by
    intro i j
    simp only [intervalMatrix, Matrix.of_apply]
    rw [sum_filter, sum_filter, ← sum_coe_sort (intervals 4)]
    refine sum_congr rfl fun J _ => ?_
    simp [a]
  have e12 : intervalMatrix 4 1 2 = a 1 2 + a 1 3 + a 1 4 := by
    rw [hentry, show ({J ∈ intervals 4 | 1 ∈ Icc J.1 J.2 ∧ 2 ∈ Icc J.1 J.2} : Finset (ℕ × ℕ)) =
      {(1, 2), (1, 3), (1, 4)} by decide]
    simp [add_assoc]
  have e13 : intervalMatrix 4 1 3 = a 1 3 + a 1 4 := by
    rw [hentry, show ({J ∈ intervals 4 | 1 ∈ Icc J.1 J.2 ∧ 3 ∈ Icc J.1 J.2} : Finset (ℕ × ℕ)) =
      {(1, 3), (1, 4)} by decide]
    simp
  have e14 : intervalMatrix 4 1 4 = a 1 4 := by
    rw [hentry, show ({J ∈ intervals 4 | 1 ∈ Icc J.1 J.2 ∧ 4 ∈ Icc J.1 J.2} : Finset (ℕ × ℕ)) =
      {(1, 4)} by decide]
    simp
  have e23 : intervalMatrix 4 2 3 = a 1 3 + a 1 4 + a 2 3 + a 2 4 := by
    rw [hentry, show ({J ∈ intervals 4 | 2 ∈ Icc J.1 J.2 ∧ 3 ∈ Icc J.1 J.2} : Finset (ℕ × ℕ)) =
      {(1, 3), (1, 4), (2, 3), (2, 4)} by decide]
    simp [add_assoc]
  have e24 : intervalMatrix 4 2 4 = a 1 4 + a 2 4 := by
    rw [hentry, show ({J ∈ intervals 4 | 2 ∈ Icc J.1 J.2 ∧ 4 ∈ Icc J.1 J.2} : Finset (ℕ × ℕ)) =
      {(1, 4), (2, 4)} by decide]
    simp
  have e34 : intervalMatrix 4 3 4 = a 1 4 + a 2 4 + a 3 4 := by
    rw [hentry, show ({J ∈ intervals 4 | 3 ∈ Icc J.1 J.2 ∧ 4 ∈ Icc J.1 J.2} : Finset (ℕ × ℕ)) =
      {(1, 4), (2, 4), (3, 4)} by decide]
    simp [add_assoc]
  -- `F_4 = Pf = A₁₂ A₃₄ - A₁₃ A₂₄ + A₁₄ A₂₃` (eq. (2), by the first-row expansion).
  have hpf4 : ∀ A : Matrix ℕ ℕ (MvPolynomial (intervals 4) ℤ),
      pfaffian (Icc 1 4) A = A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3 := by
    intro A
    rw [show (Icc 1 4 : Finset ℕ) = insert 1 (insert 2 (insert 3 {4})) by decide]
    simp [pfaffian_insert_of_forall_lt, pfaffian_empty, sum_insert, filter_insert,
      erase_insert_of_ne, filter_singleton]
    ring
  rw [intervalPfaffian, hpf4, e12, e13, e14, e23, e24, e34]
  ring
