import Mathlib

/-!
# Pfaffians as signed sums over perfect matchings

Reference: `refs/pfaffian-convex.tex`, Section 1, equation (1).

We work with a finite index set `S : Finset ι` inside a linearly ordered type `ι` (in practice
`ι = ℕ` and `S = Finset.Icc 1 n`). The Pfaffian of a matrix `A` on `S` is the Pfaffian of the
principal submatrix of `A` on `S`, with `S` in increasing order:
$$\operatorname{Pf}_S A = \sum_{M} (-1)^{\operatorname{cr}(M)} \prod_{(a, b) \in M} A_{ab},$$
where `M` runs over the perfect matchings of `S`, each written as a set of pairs `(a, b)` with
`a < b`, and `cr(M)` is the number of crossings of `M`.

Deleting rows and columns is then deleting elements of `S`; no reindexing is needed.

Only the entries `A a b` with `a < b` (both in `S`) enter the definition, so the Pfaffian of a
family `K(i, j)`, `i < j`, is the Pfaffian of its skew extension (`pfaffian_skewExtension`).
For `|S|` odd there are no perfect matchings and the Pfaffian is `0`.
-/

open Finset

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

/-- The possible edges of a matching of `S`: pairs `(a, b)` with `a, b ∈ S` and `a < b`. -/
def edges (S : Finset ι) : Finset (ι × ι) :=
  {e ∈ S ×ˢ S | e.1 < e.2}

/-- The perfect matchings of `S`: sets `M` of pairs `(a, b)` with `a, b ∈ S` and `a < b`, such
that every `s ∈ S` lies in exactly one pair of `M`. -/
def perfectMatchings (S : Finset ι) : Finset (Finset (ι × ι)) :=
  {M ∈ (edges S).powerset | ∀ s ∈ S, #{e ∈ M | e.1 = s ∨ e.2 = s} = 1}

/-- The crossing number of `M`: the number of pairs of pairs `(a, b), (c, d)` of `M` with
`a < c < b < d`. -/
def crossings (M : Finset (ι × ι)) : ℕ :=
  #{p ∈ M ×ˢ M | p.1.1 < p.2.1 ∧ p.2.1 < p.1.2 ∧ p.1.2 < p.2.2}

/-- The Pfaffian of the principal submatrix of `A` on `S` (in increasing order):
`Pf_S A = ∑_M (-1)^cr(M) ∏_{(a,b) ∈ M} A a b`, over the perfect matchings `M` of `S`. -/
def pfaffian (S : Finset ι) (A : Matrix ι ι R) : R :=
  ∑ M ∈ perfectMatchings S, (-1) ^ crossings M * ∏ e ∈ M, A e.1 e.2

/-- The skew extension of a family `K`: the matrix with entry `K i j` for `i < j`,
`-K j i` for `i > j`, and `0` on the diagonal. -/
def skewExtension (K : Matrix ι ι R) : Matrix ι ι R :=
  Matrix.of fun i j => if i < j then K i j else if j < i then -K j i else 0

/-! ### Basic facts -/

/-- The Pfaffian of the empty matrix is `1`. -/
theorem pfaffian_empty (A : Matrix ι ι R) : pfaffian ∅ A = 1 := by
  sorry

/-- The Pfaffian only reads the entries `A a b` with `a < b` in `S`. -/
theorem pfaffian_congr {S : Finset ι} {A B : Matrix ι ι R}
    (h : ∀ a ∈ S, ∀ b ∈ S, a < b → A a b = B a b) : pfaffian S A = pfaffian S B := by
  sorry

/-- The Pfaffian of a family is the Pfaffian of its skew extension. -/
theorem pfaffian_skewExtension (S : Finset ι) (K : Matrix ι ι R) :
    pfaffian S (skewExtension K) = pfaffian S K := by
  sorry

/-- **Evaluation lemma.** The Pfaffian commutes with ring homomorphisms applied entrywise. -/
theorem RingHom.map_pfaffian {R' : Type*} [CommRing R'] (f : R →+* R') (S : Finset ι)
    (A : Matrix ι ι R) : f (pfaffian S A) = pfaffian S (A.map f) := by
  sorry

/-- **First-row expansion.** If `a` is smaller than every element of `s`, then
`Pf_{a ∪ s} A = ∑_{l ∈ s} (-1)^#{x ∈ s | x < l} A a l Pf_{s ∖ l} A`. -/
theorem pfaffian_insert_of_forall_lt {a : ι} {s : Finset ι} (h : ∀ x ∈ s, a < x)
    (A : Matrix ι ι R) :
    pfaffian (insert a s) A =
      ∑ l ∈ s, (-1) ^ #{x ∈ s | x < l} * A a l * pfaffian (s.erase l) A := by
  sorry
