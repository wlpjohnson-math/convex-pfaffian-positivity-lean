import PfaffianLean.Pfaffian
import PfaffianLean.Tests

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
