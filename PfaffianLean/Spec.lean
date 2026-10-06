import PfaffianLean.Pfaffian
import PfaffianLean.Tests
import PfaffianLean.IntervalDecomposition
import PfaffianLean.ConvexKernel
import PfaffianLean.TwinRows
import PfaffianLean.CoeffPositivity
import PfaffianLean.LowerBounds
import PfaffianLean.PowerKernels
import PfaffianLean.Rainbow
import PfaffianLean.Sharpness

/-!
# Specification

The approved definitions and statements, frozen for audit.

* Each `spec_<name>` restates an approved statement in full and is proved by direct reference
  to the project theorem `<name>`.
* Each definition is pinned by a `#guard_msgs in #print` of its current form.
* Each theorem has a `#print axioms` guard expecting exactly `[propext, Classical.choice,
  Quot.sound]`; the guards of a stage are enabled at that stage's proof gate.

This file changes only at gates: new spec theorems and definition guards at a statement gate,
uncommented axiom guards at a proof gate.

The file also contains a final section, "Non-vacuity", showing that the hypotheses of
`convex_lower_bound` are satisfiable: for every even `n`, its examples apply the theorem at
concrete `f` and `x`, proving all the other hypotheses from Mathlib. Like everything else in the
file, it changes only at gates.
-/

set_option linter.style.longLine false

/-! ## Definitions (M0) -/

/--
info: def edges.{u_1} : {ι : Type u_1} → [LinearOrder ι] → Finset ι → Finset (ι × ι) :=
fun {ι} [LinearOrder ι] S ↦ {e ∈ S ×ˢ S | e.1 < e.2}
-/
#guard_msgs in
#print edges

/--
info: def perfectMatchings.{u_1} : {ι : Type u_1} → [LinearOrder ι] → Finset ι → Finset (Finset (ι × ι)) :=
fun {ι} [LinearOrder ι] S ↦ {M ∈ (edges S).powerset | ∀ s ∈ S, {e ∈ M | e.1 = s ∨ e.2 = s}.card = 1}
-/
#guard_msgs in
#print perfectMatchings

/--
info: def crossings.{u_1} : {ι : Type u_1} → [LinearOrder ι] → Finset (ι × ι) → ℕ :=
fun {ι} [LinearOrder ι] M ↦ {p ∈ M ×ˢ M | p.1.1 < p.2.1 ∧ p.2.1 < p.1.2 ∧ p.1.2 < p.2.2}.card
-/
#guard_msgs in
#print crossings

/--
info: def pfaffian.{u_1, u_2} : {ι : Type u_1} →
  [LinearOrder ι] → {R : Type u_2} → [CommRing R] → Finset ι → Matrix ι ι R → R :=
fun {ι} [LinearOrder ι] {R} [CommRing R] S A ↦ ∑ M ∈ perfectMatchings S, (-1) ^ crossings M * ∏ e ∈ M, A e.1 e.2
-/
#guard_msgs in
#print pfaffian

/--
info: def skewExtension.{u_1, u_2} : {ι : Type u_1} →
  [LinearOrder ι] → {R : Type u_2} → [CommRing R] → Matrix ι ι R → Matrix ι ι R :=
fun {ι} [LinearOrder ι] {R} [CommRing R] K ↦ Matrix.of fun i j ↦ if i < j then K i j else if j < i then -K j i else 0
-/
#guard_msgs in
#print skewExtension

open Finset

/-! ## M0 lemmas -/

theorem spec_pfaffian_empty {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]
    (A : Matrix ι ι R) : pfaffian ∅ A = 1 :=
  pfaffian_empty A

theorem spec_pfaffian_congr {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]
    {S : Finset ι} {A B : Matrix ι ι R}
    (h : ∀ a ∈ S, ∀ b ∈ S, a < b → A a b = B a b) : pfaffian S A = pfaffian S B :=
  pfaffian_congr h

theorem spec_pfaffian_skewExtension {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]
    (S : Finset ι) (K : Matrix ι ι R) :
    pfaffian S (skewExtension K) = pfaffian S K :=
  pfaffian_skewExtension S K

theorem spec_RingHom_map_pfaffian {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]
    {R' : Type*} [CommRing R'] (f : R →+* R') (S : Finset ι) (A : Matrix ι ι R) :
    f (pfaffian S A) = pfaffian S (A.map f) :=
  RingHom.map_pfaffian f S A

theorem spec_pfaffian_insert_of_forall_lt {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]
    {a : ι} {s : Finset ι} (h : ∀ x ∈ s, a < x) (A : Matrix ι ι R) :
    pfaffian (insert a s) A =
      ∑ l ∈ s, (-1) ^ #{x ∈ s | x < l} * A a l * pfaffian (s.erase l) A :=
  pfaffian_insert_of_forall_lt h A

/-! ## M0 tests

`PfaffianTests.skewOnes` is unfolded to `skewExtension (Matrix.of fun _ _ => 1)`, so these
statements do not depend on the test file's definitions. -/

theorem spec_pfaffian_Icc_two {R : Type*} [CommRing R] (A : Matrix ℕ ℕ R) :
    pfaffian (Icc 1 2) A = A 1 2 :=
  PfaffianTests.pfaffian_Icc_two A

theorem spec_pfaffian_Icc_four {R : Type*} [CommRing R] (A : Matrix ℕ ℕ R) :
    pfaffian (Icc 1 4) A = A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3 :=
  PfaffianTests.pfaffian_Icc_four A

theorem spec_pfaffian_skewOnes_two {R : Type*} [CommRing R] :
    pfaffian (Icc 1 2) (skewExtension (Matrix.of fun _ _ => 1) : Matrix ℕ ℕ R) = 1 :=
  PfaffianTests.pfaffian_skewOnes_two

theorem spec_pfaffian_skewOnes_four {R : Type*} [CommRing R] :
    pfaffian (Icc 1 4) (skewExtension (Matrix.of fun _ _ => 1) : Matrix ℕ ℕ R) = 1 :=
  PfaffianTests.pfaffian_skewOnes_four

theorem spec_pfaffian_skewOnes_six {R : Type*} [CommRing R] :
    pfaffian (Icc 1 6) (skewExtension (Matrix.of fun _ _ => 1) : Matrix ℕ ℕ R) = 1 :=
  PfaffianTests.pfaffian_skewOnes_six

/-! ## M0 axiom guards (enabled at the M0 proof gate) -/

/-- info: 'pfaffian_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pfaffian_empty

/-- info: 'pfaffian_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pfaffian_congr

/-- info: 'pfaffian_skewExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pfaffian_skewExtension

/-- info: 'RingHom.map_pfaffian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RingHom.map_pfaffian

/-- info: 'pfaffian_insert_of_forall_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pfaffian_insert_of_forall_lt

/-- info: 'PfaffianTests.pfaffian_Icc_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PfaffianTests.pfaffian_Icc_two

/-- info: 'PfaffianTests.pfaffian_Icc_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PfaffianTests.pfaffian_Icc_four

/-- info: 'PfaffianTests.pfaffian_skewOnes_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PfaffianTests.pfaffian_skewOnes_two

/-- info: 'PfaffianTests.pfaffian_skewOnes_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PfaffianTests.pfaffian_skewOnes_four

/-- info: 'PfaffianTests.pfaffian_skewOnes_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PfaffianTests.pfaffian_skewOnes_six

/-! ## Definitions (M1) -/

/--
info: def intervals : ℕ → Finset (ℕ × ℕ) :=
fun n ↦ {J ∈ Icc 1 n ×ˢ Icc 1 n | J.1 < J.2}
-/
#guard_msgs in
#print intervals

/--
info: def pad : ℕ → Matrix ℕ ℕ ℝ → ℕ → ℕ → ℝ :=
fun n K i j ↦ if i = 0 ∨ j = n + 1 then 0 else K i j
-/
#guard_msgs in
#print pad

/--
info: def alpha : ℕ → Matrix ℕ ℕ ℝ → ℕ × ℕ → ℝ :=
fun n K J ↦ pad n K J.1 J.2 - pad n K (J.1 - 1) J.2 - pad n K J.1 (J.2 + 1) + pad n K (J.1 - 1) (J.2 + 1)
-/
#guard_msgs in
#print alpha

/--
info: def additiveClass : ℕ → Set (Matrix ℕ ℕ ℝ) :=
fun n ↦ {K | ∀ J ∈ intervals n, 0 ≤ alpha n K J}
-/
#guard_msgs in
#print additiveClass

/--
info: def intervalMatrix : (n : ℕ) → Matrix ℕ ℕ (MvPolynomial ↥(intervals n) ℤ) :=
fun n ↦ Matrix.of fun i j ↦ ∑ J with i ∈ Icc (↑J).1 (↑J).2 ∧ j ∈ Icc (↑J).1 (↑J).2, MvPolynomial.X J
-/
#guard_msgs in
#print intervalMatrix

/--
info: def intervalPfaffian : (n : ℕ) → MvPolynomial ↥(intervals n) ℤ :=
fun n ↦ pfaffian (Icc 1 n) (intervalMatrix n)
-/
#guard_msgs in
#print intervalPfaffian

/--
info: def kernel : (ℝ → ℝ) → (ℕ → ℝ) → Matrix ℕ ℕ ℝ :=
fun f x ↦ Matrix.of fun i j ↦ f (x j - x i)
-/
#guard_msgs in
#print kernel

/-! ## M1 lemmas -/

theorem spec_interval_decomposition (n : ℕ) (K : Matrix ℕ ℕ ℝ) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i < j) (hj : j ≤ n) :
    K i j = ∑ J ∈ intervals n with i ∈ Icc J.1 J.2 ∧ j ∈ Icc J.1 J.2, alpha n K J :=
  interval_decomposition n K hi hij hj

theorem spec_interval_decomposition_pfaffian (n : ℕ) (K : Matrix ℕ ℕ ℝ) :
    pfaffian (Icc 1 n) K =
      MvPolynomial.aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) :=
  interval_decomposition_pfaffian n K

theorem spec_interval_decomposition_corner (n : ℕ) (K : Matrix ℕ ℕ ℝ) :
    alpha n K (1, n) = K 1 n :=
  interval_decomposition_corner n K

theorem spec_convex_kernel_additive (f : ℝ → ℝ) (hf : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    kernel f x ∈ additiveClass n ∧ alpha n (kernel f x) (1, n) = f (x n - x 1) :=
  convex_kernel_additive f hf hanti hconv n x hx

/-! ## M1 axiom guards (enabled at the M1 proof gate) -/

/-- info: 'interval_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interval_decomposition

/-- info: 'interval_decomposition_pfaffian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interval_decomposition_pfaffian

/-- info: 'interval_decomposition_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interval_decomposition_corner

/-- info: 'convex_kernel_additive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms convex_kernel_additive

/-! ## M2 lemmas -/

theorem spec_pf_twin_rows_consecutive {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]
    {S : Finset ι} (A : Matrix ι ι R) {y y' : ι} (hy : y ∈ S) (hy' : y' ∈ S) (hyy' : y < y')
    (hcons : ∀ z ∈ S, ¬(y < z ∧ z < y'))
    (htwin_right : ∀ z ∈ S, y' < z → A y z = A y' z)
    (htwin_left : ∀ z ∈ S, z < y → A z y = A z y') :
    pfaffian S A = A y y' * pfaffian (S \ {y, y'}) A :=
  pf_twin_rows_consecutive A hy hy' hyy' hcons htwin_right htwin_left

theorem spec_pf_twin_rows {R : Type*} [CommRing R] (n : ℕ) (A : Matrix ℕ ℕ R) {y : ℕ}
    (hy : 1 ≤ y) (hyn : y + 1 ≤ n)
    (htwin_right : ∀ z ∈ Icc 1 n, y + 1 < z → A y z = A (y + 1) z)
    (htwin_left : ∀ z ∈ Icc 1 n, z < y → A z y = A z (y + 1)) :
    pfaffian (Icc 1 n) A = A y (y + 1) * pfaffian (Icc 1 n \ {y, y + 1}) A :=
  pf_twin_rows n A hy hyn htwin_right htwin_left

/-! ## M2 axiom guards (enabled at the M2 proof gate) -/

/-- info: 'pf_twin_rows_consecutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pf_twin_rows_consecutive

/-- info: 'pf_twin_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pf_twin_rows

/-! ## M3 lemmas -/

theorem spec_pfaffian_skewOnes {R : Type*} [CommRing R] (n : ℕ) (hn : Even n) :
    pfaffian (Icc 1 n) (skewExtension (Matrix.of fun _ _ => (1 : R))) = 1 :=
  pfaffian_skewOnes n hn

theorem spec_corner_mem_intervals {n : ℕ} (hn : 2 ≤ n) : (1, n) ∈ intervals n :=
  corner_mem_intervals hn

theorem spec_coeff_nonneg (n : ℕ) (m : intervals n →₀ ℕ) :
    0 ≤ (intervalPfaffian n).coeff m :=
  coeff_nonneg n m

theorem spec_intervalPfaffian_isHomogeneous (n : ℕ) :
    (intervalPfaffian n).IsHomogeneous (n / 2) :=
  intervalPfaffian_isHomogeneous n

theorem spec_coeff_corner (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) :
    (intervalPfaffian n).coeff (Finsupp.single ⟨(1, n), corner_mem_intervals h2⟩ (n / 2)) = 1 :=
  coeff_corner n hn h2

theorem spec_intervalPfaffian_four :
    let a : ℕ → ℕ → MvPolynomial (intervals 4) ℤ := fun p q =>
      if h : (p, q) ∈ intervals 4 then MvPolynomial.X ⟨(p, q), h⟩ else 0
    intervalPfaffian 4 = a 1 4 ^ 2 + a 1 4 * (a 1 2 + a 1 3 + a 2 3 + a 2 4 + a 3 4) +
      a 1 2 * a 3 4 + a 1 2 * a 2 4 + a 1 3 * a 3 4 :=
  intervalPfaffian_four

/-! ## M3 axiom guards (enabled at the M3 proof gate) -/

/-- info: 'pfaffian_skewOnes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pfaffian_skewOnes

/-- info: 'corner_mem_intervals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corner_mem_intervals

/-- info: 'coeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coeff_nonneg

/-- info: 'intervalPfaffian_isHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intervalPfaffian_isHomogeneous

/-- info: 'coeff_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coeff_corner

/-- info: 'intervalPfaffian_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intervalPfaffian_four

/-! ## M4 lemmas -/

theorem spec_additive_lower_bound (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K =
        MvPolynomial.aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) ∧
      MvPolynomial.aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) ≥
        K 1 n ^ (n / 2) ∧
      K 1 n ^ (n / 2) ≥ 0 :=
  additive_lower_bound n hn h2 K hK

theorem spec_convex_lower_bound (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel f x) ≥ f (x n - x 1) ^ (n / 2) ∧ f (x n - x 1) ^ (n / 2) > 0 :=
  convex_lower_bound f hpos hanti hconv n hn x hx

/-! ## M4 axiom guards (enabled at the M4 proof gate) -/

/-- info: 'additive_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms additive_lower_bound

/-- info: 'convex_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms convex_lower_bound

/-! ## M5 lemmas -/

theorem spec_convex_lower_bound_skew (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (skewExtension (kernel f x)) ≥ f (x n - x 1) ^ (n / 2) ∧
      f (x n - x 1) ^ (n / 2) > 0 :=
  convex_lower_bound_skew f hpos hanti hconv n hn x hx

/-! ## M5 axiom guards -/

/-- info: 'convex_lower_bound_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms convex_lower_bound_skew

/-! ## M5 lemmas (power kernels) -/

theorem spec_power_kernel_lower_bound (p : ℝ) (hp : 0 < p) (n : ℕ) (hn : Even n) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel (fun r => r ^ (-p)) x) ≥ ((x n - x 1) ^ (-p)) ^ (n / 2) ∧
      ((x n - x 1) ^ (-p)) ^ (n / 2) > 0 :=
  power_kernel_lower_bound p hp n hn x hx

theorem spec_albouy_moeckel_pos (n : ℕ) (hn : Even n) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel (fun r => r ^ (-2 : ℝ)) x) > 0 :=
  albouy_moeckel_pos n hn x hx

/-- The conclusion of `power_kernel_lower_bound` is the conclusion of `convex_lower_bound` at
`f r = r ^ (-p)`, up to β-reduction. -/
example (p : ℝ) (n : ℕ) (x : ℕ → ℝ) :
    (pfaffian (Icc 1 n) (kernel (fun r => r ^ (-p)) x) ≥ ((x n - x 1) ^ (-p)) ^ (n / 2) ∧
      ((x n - x 1) ^ (-p)) ^ (n / 2) > 0) =
    (let f : ℝ → ℝ := fun r => r ^ (-p)
     pfaffian (Icc 1 n) (kernel f x) ≥ f (x n - x 1) ^ (n / 2) ∧ f (x n - x 1) ^ (n / 2) > 0) :=
  rfl

/-! ## M5 axiom guards (power kernels; enabled at the M5 proof gate) -/

/-- info: 'power_kernel_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms power_kernel_lower_bound

/-- info: 'albouy_moeckel_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms albouy_moeckel_pos

/-! ## M6 lemmas (the rainbow bound) -/

theorem spec_outer_pair_bound (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K ≥ K 1 n * pfaffian (Icc 2 (n - 1)) K :=
  outer_pair_bound n hn h2 K hK

theorem spec_additive_rainbow_bound (n : ℕ) (hn : Even n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K ≥ ∏ k ∈ Icc 1 (n / 2), K k (n + 1 - k) ∧
      ∏ k ∈ Icc 1 (n / 2), K k (n + 1 - k) ≥ K 1 n ^ (n / 2) :=
  additive_rainbow_bound n hn K hK

theorem spec_convex_rainbow_bound (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel f x) ≥ ∏ k ∈ Icc 1 (n / 2), f (x (n + 1 - k) - x k) ∧
      ∏ k ∈ Icc 1 (n / 2), f (x (n + 1 - k) - x k) > 0 :=
  convex_rainbow_bound f hpos hanti hconv n hn x hx

/-! ## M6 axiom guards (enabled at the M6 proof gate) -/

/-- info: 'outer_pair_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms outer_pair_bound

/-- info: 'additive_rainbow_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms additive_rainbow_bound

/-- info: 'convex_rainbow_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms convex_rainbow_bound

/-! ## Definitions (M7) -/

/--
info: def rainbow : ℕ → Finset (ℕ × ℕ) :=
fun n ↦ image (fun k ↦ (k, n + 1 - k)) (Icc 1 (n / 2))
-/
#guard_msgs in
#print rainbow

/-- Sanity check: the rainbow matching of `[4]`. -/
example : rainbow 4 = {(1, 4), (2, 3)} := by decide

/-! ## M7 lemmas (only the rainbow survives) -/

theorem spec_rainbow_mem_perfectMatchings (n : ℕ) (hn : Even n) :
    rainbow n ∈ perfectMatchings (Icc 1 n) :=
  rainbow_mem_perfectMatchings n hn

theorem spec_exists_pfaffian_lt_prod_of_ne_rainbow (n : ℕ) (hn : Even n) (M : Finset (ℕ × ℕ))
    (hM : M ∈ perfectMatchings (Icc 1 n)) (hMr : M ≠ rainbow n) :
    ∃ f : ℝ → ℝ, (∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t) ∧ AntitoneOn f (Set.Ioi 0) ∧
      ConvexOn ℝ (Set.Ioi 0) f ∧
      ∃ x : ℕ → ℝ, StrictMonoOn x (Set.Icc 1 n) ∧
        pfaffian (Icc 1 n) (kernel f x) < ∏ e ∈ M, f (x e.2 - x e.1) :=
  exists_pfaffian_lt_prod_of_ne_rainbow n hn M hM hMr

/-- Satisfiability check: the hypotheses of `exists_pfaffian_lt_prod_of_ne_rainbow` hold for
`n = 4` and `M = {(1, 2), (3, 4)}`. -/
example : ({(1, 2), (3, 4)} : Finset (ℕ × ℕ)) ∈ perfectMatchings (Icc 1 4) ∧
    ({(1, 2), (3, 4)} : Finset (ℕ × ℕ)) ≠ rainbow 4 := by decide

/-! ## M7 axiom guards (enabled at the M7 proof gate) -/

/-- info: 'rainbow_mem_perfectMatchings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rainbow_mem_perfectMatchings

/-- info: 'exists_pfaffian_lt_prod_of_ne_rainbow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_pfaffian_lt_prod_of_ne_rainbow

/-! ## Non-vacuity

The hypotheses of `convex_lower_bound` are satisfiable. Each example discharges all of them from
Mathlib for a concrete `f` and `x`, assuming only `Even n`. -/

/-- Satisfiability check: the hypotheses of `convex_lower_bound` hold for `f = 1`, `x k = k`. -/
example (n : ℕ) (hn : Even n) :
    pfaffian (Icc 1 n) (kernel (fun _ => (1 : ℝ)) (fun k => (k : ℝ))) ≥ (1 : ℝ) ^ (n / 2) ∧
      (1 : ℝ) ^ (n / 2) > 0 := by
  have hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < (fun _ : ℝ => (1 : ℝ)) t := fun _ _ => one_pos
  have hanti : AntitoneOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioi 0) := fun _ _ _ _ _ => le_rfl
  have hconv : ConvexOn ℝ (Set.Ioi 0) (fun _ : ℝ => (1 : ℝ)) := convexOn_const 1 (convex_Ioi 0)
  have hx : StrictMonoOn (fun k : ℕ => (k : ℝ)) (Set.Icc 1 n) := fun a _ b _ hab =>
    show (a : ℝ) < b from Nat.cast_lt.2 hab
  exact convex_lower_bound (fun _ => 1) hpos hanti hconv n hn (fun k => (k : ℝ)) hx

/-- Satisfiability check: the hypotheses of `convex_lower_bound` hold for `f t = t⁻¹`, which
blows up at `0`, and `x k = k`. -/
example (n : ℕ) (hn : Even n) :
    pfaffian (Icc 1 n) (kernel (fun t => t⁻¹) (fun k => (k : ℝ))) ≥ ((n : ℝ) - 1)⁻¹ ^ (n / 2) ∧
      ((n : ℝ) - 1)⁻¹ ^ (n / 2) > 0 := by
  have hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < (fun t : ℝ => t⁻¹) t := fun _ ht => inv_pos.2 ht
  have hanti : AntitoneOn (fun t : ℝ => t⁻¹) (Set.Ioi 0) := inv_antitoneOn_Ioi
  have hconv : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ => t⁻¹) := by
    simpa only [zpow_neg_one] using convexOn_zpow (𝕜 := ℝ) (-1)
  have hx : StrictMonoOn (fun k : ℕ => (k : ℝ)) (Set.Icc 1 n) := fun a _ b _ hab =>
    show (a : ℝ) < b from Nat.cast_lt.2 hab
  simpa only [Nat.cast_one] using
    convex_lower_bound (fun t => t⁻¹) hpos hanti hconv n hn (fun k => (k : ℝ)) hx
