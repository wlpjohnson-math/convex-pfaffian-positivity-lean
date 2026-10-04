import Mathlib

/-!
# Pfaffians as signed sums over perfect matchings

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

/-! ### Perfect matchings: basic API -/

section API

variable {S : Finset ι} {M : Finset (ι × ι)}

theorem mem_edges {e : ι × ι} : e ∈ edges S ↔ e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 < e.2 := by
  simp [edges, and_assoc]

theorem mem_perfectMatchings :
    M ∈ perfectMatchings S ↔ M ⊆ edges S ∧ ∀ s ∈ S, #{e ∈ M | e.1 = s ∨ e.2 = s} = 1 := by
  simp [perfectMatchings]

/-- An edge of a perfect matching of `S` has both endpoints in `S`, in increasing order. -/
theorem PerfectMatching.edge (hM : M ∈ perfectMatchings S) {e : ι × ι} (he : e ∈ M) :
    e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 < e.2 :=
  mem_edges.1 ((mem_perfectMatchings.1 hM).1 he)

/-- Two edges of a perfect matching of `S` through the same point of `S` are equal. -/
theorem PerfectMatching.eq_of_mem (hM : M ∈ perfectMatchings S) {t : ι} (ht : t ∈ S)
    {e f : ι × ι} (he : e ∈ M) (hf : f ∈ M) (het : e.1 = t ∨ e.2 = t)
    (hft : f.1 = t ∨ f.2 = t) : e = f :=
  card_le_one.1 ((mem_perfectMatchings.1 hM).2 t ht).le e (mem_filter.2 ⟨he, het⟩) f
    (mem_filter.2 ⟨hf, hft⟩)

/-- Summing over the points of `S` is summing over both endpoints of the edges of a perfect
matching of `S`. -/
theorem PerfectMatching.sum_eq {β : Type*} [AddCommMonoid β] (hM : M ∈ perfectMatchings S)
    (g : ι → β) : ∑ t ∈ S, g t = ∑ e ∈ M, (g e.1 + g e.2) := by
  have key : ∀ t ∈ S, g t = ∑ e ∈ M, if e.1 = t ∨ e.2 = t then g t else 0 := by
    intro t ht
    rw [← sum_filter, sum_const, (mem_perfectMatchings.1 hM).2 t ht, one_smul]
  rw [sum_congr rfl key, sum_comm]
  refine sum_congr rfl fun e he => ?_
  obtain ⟨h1, h2, h12⟩ := PerfectMatching.edge hM he
  have hpair : ({t ∈ S | e.1 = t ∨ e.2 = t} : Finset ι) = {e.1, e.2} := by
    ext t
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨-, h | h⟩ <;> simp [h]
    · rintro (h | h) <;> subst h <;> simp [h1, h2]
  rw [← sum_filter, hpair, sum_pair h12.ne]

/-- Parity of the points of `T` below `l`, read off a perfect matching of `T`. -/
theorem PerfectMatching.card_filter_lt {T : Finset ι} (hM : M ∈ perfectMatchings T) {l : ι}
    (hl : l ∉ T) :
    #{x ∈ T | x < l} = 2 * #{e ∈ M | e.2 < l} + #{e ∈ M | e.1 < l ∧ l < e.2} := by
  rw [card_filter, PerfectMatching.sum_eq hM, card_filter, card_filter, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun e he => ?_
  obtain ⟨-, h2, h12⟩ := PerfectMatching.edge hM he
  have h2l : e.2 ≠ l := fun h => hl (h ▸ h2)
  rcases lt_or_gt_of_ne h2l with h2l | h2l
  · simp [h12.trans h2l, h2l, h2l.not_gt]
  · by_cases h1l : e.1 < l <;> simp [h1l, h2l, h2l.not_gt]

end API

/-- `crossings` as a double sum over the edges of `M`. -/
theorem crossings_eq_sum (M : Finset (ι × ι)) :
    crossings M = ∑ e ∈ M, #{f ∈ M | e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2} := by
  rw [crossings, card_filter, sum_product]
  simp only [card_filter]

/-- Adding an edge `(a, l)` whose left end is to the left of every edge of `M`: the new
crossings are the edges `(c, d)` of `M` with `c < l < d`. -/
theorem crossings_insert {a l : ι} {M : Finset (ι × ι)} (hM : ∀ e ∈ M, a < e.1) :
    crossings (insert (a, l) M) = crossings M + #{e ∈ M | e.1 < l ∧ l < e.2} := by
  have hnot : (a, l) ∉ M := fun h => lt_irrefl a (hM _ h)
  rw [crossings_eq_sum, crossings_eq_sum, sum_insert hnot, add_comm]
  congr 1
  · refine sum_congr rfl fun e he => ?_
    rw [filter_insert, ite_eq_right (fun h => (hM e he).not_gt h.1)]
  · rw [filter_insert, ite_eq_right (fun h => lt_irrefl a h.1)]
    exact congrArg card (filter_congr fun e he => by simp [hM e he])

/-! ### Basic facts -/

/-- The Pfaffian of the empty matrix is `1`. -/
theorem pfaffian_empty (A : Matrix ι ι R) : pfaffian ∅ A = 1 := by
  simp [pfaffian, perfectMatchings, edges, crossings]

/-- The Pfaffian only reads the entries `A a b` with `a < b` in `S`. -/
theorem pfaffian_congr {S : Finset ι} {A B : Matrix ι ι R}
    (h : ∀ a ∈ S, ∀ b ∈ S, a < b → A a b = B a b) : pfaffian S A = pfaffian S B := by
  refine sum_congr rfl fun M hM => ?_
  congr 1
  refine prod_congr rfl fun e he => ?_
  obtain ⟨h1, h2, h12⟩ := PerfectMatching.edge hM he
  exact h _ h1 _ h2 h12

/-- The Pfaffian of a family is the Pfaffian of its skew extension. -/
theorem pfaffian_skewExtension (S : Finset ι) (K : Matrix ι ι R) :
    pfaffian S (skewExtension K) = pfaffian S K :=
  pfaffian_congr fun a _ b _ hab => by simp [skewExtension, hab]

/-- **Evaluation lemma.** The Pfaffian commutes with ring homomorphisms applied entrywise. -/
theorem RingHom.map_pfaffian {R' : Type*} [CommRing R'] (f : R →+* R') (S : Finset ι)
    (A : Matrix ι ι R) : f (pfaffian S A) = pfaffian S (A.map f) := by
  simp [pfaffian, map_sum, map_prod]

/-- **First-row expansion.** If `a` is smaller than every element of `s`, then
`Pf_{a ∪ s} A = ∑_{l ∈ s} (-1)^#{x ∈ s | x < l} A a l Pf_{s ∖ l} A`. -/
theorem pfaffian_insert_of_forall_lt {a : ι} {s : Finset ι} (h : ∀ x ∈ s, a < x)
    (A : Matrix ι ι R) :
    pfaffian (insert a s) A =
      ∑ l ∈ s, (-1) ^ #{x ∈ s | x < l} * A a l * pfaffian (s.erase l) A := by
  have ha : a ∉ s := fun ha => lt_irrefl a (h a ha)
  -- No edge of a perfect matching of `insert a s` ends at `a`.
  have hsnd : ∀ M ∈ perfectMatchings (insert a s), ∀ e ∈ M, e.2 ≠ a := by
    intro M hM e he h2
    obtain ⟨h1, -, h12⟩ := PerfectMatching.edge hM he
    rcases mem_insert.1 h1 with h1 | h1
    · exact h12.ne (h1.trans h2.symm)
    · exact (h _ h1).not_gt (h2 ▸ h12)
  -- Every perfect matching of `insert a s` contains exactly one edge `(a, l)`, and `l ∈ s`.
  have hpartner : ∀ M ∈ perfectMatchings (insert a s), #{l ∈ s | (a, l) ∈ M} = 1 := by
    intro M hM
    rw [← (mem_perfectMatchings.1 hM).2 a (mem_insert_self a s)]
    refine card_nbij' (fun l => (a, l)) Prod.snd ?_ ?_ ?_ ?_
    · intro l hl
      rw [mem_coe, mem_filter] at hl ⊢
      exact ⟨hl.2, Or.inl rfl⟩
    · intro e he
      rw [mem_coe, mem_filter] at he ⊢
      have h1 : e.1 = a := he.2.resolve_right (hsnd M hM e he.1)
      obtain ⟨-, h2, h12⟩ := PerfectMatching.edge hM he.1
      refine ⟨(mem_insert.1 h2).resolve_left fun h => h12.ne (h1.trans h.symm), ?_⟩
      rw [← h1]
      exact he.1
    · intro l _
      rfl
    · intro e he
      rw [mem_coe, mem_filter] at he
      exact Prod.ext (he.2.resolve_right (hsnd M hM e he.1)).symm rfl
  -- Group the matchings by the partner `l` of `a`.
  have hsplit : pfaffian (insert a s) A = ∑ l ∈ s,
      ∑ M ∈ perfectMatchings (insert a s) with (a, l) ∈ M,
        (-1) ^ crossings M * ∏ e ∈ M, A e.1 e.2 := by
    rw [pfaffian]
    simp_rw [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun M hM => ?_
    rw [← sum_filter, sum_const, hpartner M hM, one_smul]
  -- The matchings with partner `l` are `(a, l)` together with a matching of `s ∖ {l}`.
  have hbij : ∀ l ∈ s, ∑ M ∈ perfectMatchings (insert a s) with (a, l) ∈ M,
      (-1) ^ crossings M * ∏ e ∈ M, A e.1 e.2 =
      ∑ M ∈ perfectMatchings (s.erase l),
        (-1) ^ crossings (insert (a, l) M) * ∏ e ∈ insert (a, l) M, A e.1 e.2 := by
    intro l hl
    have hnot : ∀ M ∈ perfectMatchings (s.erase l), (a, l) ∉ M := fun M hM hM' =>
      ha (mem_of_mem_erase (PerfectMatching.edge hM hM').1)
    refine sum_nbij' (fun M => M.erase (a, l)) (fun M => insert (a, l) M) ?_ ?_ ?_ ?_ ?_
    · intro M hM
      rw [mem_filter] at hM
      obtain ⟨hM, hal⟩ := hM
      refine mem_perfectMatchings.2 ⟨fun e he => ?_, fun t ht => ?_⟩
      · obtain ⟨hne, he⟩ := mem_erase.1 he
        obtain ⟨h1, h2, h12⟩ := PerfectMatching.edge hM he
        have hthrough : ∀ t ∈ insert a s, (e.1 = t ∨ e.2 = t) → (a = t ∨ l = t) → False :=
          fun t ht het halt => hne (PerfectMatching.eq_of_mem hM ht he hal het halt)
        have h1a : e.1 ≠ a := fun h => hthrough a (mem_insert_self a s) (Or.inl h) (Or.inl rfl)
        have h2a : e.2 ≠ a := hsnd M hM e he
        have h1l : e.1 ≠ l := fun h =>
          hthrough l (mem_insert_of_mem hl) (Or.inl h) (Or.inr rfl)
        have h2l : e.2 ≠ l := fun h =>
          hthrough l (mem_insert_of_mem hl) (Or.inr h) (Or.inr rfl)
        exact mem_edges.2 ⟨mem_erase.2 ⟨h1l, (mem_insert.1 h1).resolve_left h1a⟩,
          mem_erase.2 ⟨h2l, (mem_insert.1 h2).resolve_left h2a⟩, h12⟩
      · obtain ⟨htl, hts⟩ := mem_erase.1 ht
        rw [filter_erase, erase_eq_of_notMem]
        · exact (mem_perfectMatchings.1 hM).2 t (mem_insert_of_mem hts)
        · simp only [mem_filter, not_and, not_or]
          exact fun _ => ⟨fun h => ha (h ▸ hts), fun h => htl h.symm⟩
    · intro M hM
      refine mem_filter.2 ⟨mem_perfectMatchings.2 ⟨fun e he => ?_, fun t ht => ?_⟩,
        mem_insert_self _ _⟩
      · rcases mem_insert.1 he with rfl | he
        · exact mem_edges.2 ⟨mem_insert_self a s, mem_insert_of_mem hl, h l hl⟩
        · obtain ⟨h1, h2, h12⟩ := PerfectMatching.edge hM he
          exact mem_edges.2 ⟨mem_insert_of_mem (mem_of_mem_erase h1),
            mem_insert_of_mem (mem_of_mem_erase h2), h12⟩
      · -- No edge of `M` passes through `a` or `l`.
        have hfree : ∀ u, (u = a ∨ u = l) → #{e ∈ M | e.1 = u ∨ e.2 = u} = 0 := by
          intro u hu
          refine card_eq_zero.2 (filter_eq_empty_iff.2 fun e he heu => ?_)
          obtain ⟨h1, h2, -⟩ := PerfectMatching.edge hM he
          have hu' : u ∉ s.erase l := by
            rcases hu with rfl | rfl
            · exact fun h' => ha (mem_of_mem_erase h')
            · exact notMem_erase u s
          rcases heu with h' | h' <;> exact hu' (h' ▸ ‹_›)
        rw [filter_insert]
        by_cases hat : a = t ∨ l = t
        · rw [ite_eq_left hat, card_insert_of_notMem, hfree t (hat.imp Eq.symm Eq.symm)]
          exact fun h' => hnot M hM (mem_filter.1 h').1
        · rw [ite_eq_right hat]
          push Not at hat
          exact (mem_perfectMatchings.1 hM).2 t (mem_erase.2 ⟨hat.2.symm,
            (mem_insert.1 ht).resolve_left hat.1.symm⟩)
    · intro M hM
      exact insert_erase (mem_filter.1 hM).2
    · intro M hM
      exact erase_insert (hnot M hM)
    · intro M hM
      rw [insert_erase (mem_filter.1 hM).2]
  -- The sign: the edge `(a, l)` crosses the edges `(c, d)` with `c < l < d`, and their number
  -- has the parity of `#{x ∈ s | x < l}`.
  have hsign : ∀ l ∈ s, ∀ M ∈ perfectMatchings (s.erase l),
      (-1) ^ crossings (insert (a, l) M) * ∏ e ∈ insert (a, l) M, A e.1 e.2 =
        (-1) ^ #{x ∈ s | x < l} * A a l * ((-1) ^ crossings M * ∏ e ∈ M, A e.1 e.2) := by
    intro l hl M hM
    have hleft : ∀ e ∈ M, a < e.1 := fun e he =>
      h _ (mem_of_mem_erase (PerfectMatching.edge hM he).1)
    have hcount : #{x ∈ s | x < l} = 2 * #{e ∈ M | e.2 < l} + #{e ∈ M | e.1 < l ∧ l < e.2} := by
      have hl' : l ∉ ({x ∈ s | x < l} : Finset ι) := by simp
      rw [← PerfectMatching.card_filter_lt hM (notMem_erase l s), filter_erase,
        erase_eq_of_notMem hl']
    rw [crossings_insert hleft, prod_insert (fun h' => lt_irrefl a (hleft _ h')), hcount,
      pow_add, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    ring
  rw [hsplit]
  refine sum_congr rfl fun l hl => ?_
  rw [hbij l hl, sum_congr rfl (hsign l hl), ← mul_sum]
  rfl
