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

The proof is the reference's: the partner swap `M ↦ M'` (exchange the partners of `y` and `y'`)
is a weight-preserving, fixed-point-free involution on the matchings not containing `(y, y')`
that changes the crossing number by an odd amount, so those terms cancel; the matchings
containing `(y, y')` give `A_{y y'} · Pf_{S ∖ {y, y'}} A`.
-/

open Finset

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

/-! ### Matchings containing a given edge -/

/-- The perfect matchings of `S` containing the edge `(y, y')` are `(y, y')` together with a
perfect matching of `S ∖ {y, y'}`. -/
theorem sum_perfectMatchings_filter_mem {β : Type*} [AddCommMonoid β] {S : Finset ι} {y y' : ι}
    (hy : y ∈ S) (hy' : y' ∈ S) (hyy' : y < y') (g : Finset (ι × ι) → β) :
    ∑ M ∈ perfectMatchings S with (y, y') ∈ M, g M =
      ∑ M ∈ perfectMatchings (S \ {y, y'}), g (insert (y, y') M) := by
  have hnot : ∀ M ∈ perfectMatchings (S \ {y, y'}), (y, y') ∉ M := fun M hM h =>
    (mem_sdiff.1 (PerfectMatching.edge hM h).1).2 (mem_insert_self _ _)
  refine sum_nbij' (fun M => M.erase (y, y')) (fun M => insert (y, y') M) ?_ ?_ ?_ ?_ ?_
  · intro M hM
    obtain ⟨hM, he₀⟩ := mem_filter.1 hM
    refine mem_perfectMatchings.2 ⟨fun e he => ?_, fun t ht => ?_⟩
    · obtain ⟨hne, he⟩ := mem_erase.1 he
      obtain ⟨h1, h2, h12⟩ := PerfectMatching.edge hM he
      have hthrough : ∀ t ∈ S, (e.1 = t ∨ e.2 = t) → (y = t ∨ y' = t) → False :=
        fun t ht het h0t => hne (PerfectMatching.eq_of_mem hM ht he he₀ het h0t)
      refine mem_edges.2 ⟨mem_sdiff.2 ⟨h1, ?_⟩, mem_sdiff.2 ⟨h2, ?_⟩, h12⟩
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨fun h => hthrough y hy (Or.inl h) (Or.inl rfl),
          fun h => hthrough y' hy' (Or.inl h) (Or.inr rfl)⟩
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨fun h => hthrough y hy (Or.inr h) (Or.inl rfl),
          fun h => hthrough y' hy' (Or.inr h) (Or.inr rfl)⟩
    · obtain ⟨htS, ht0⟩ := mem_sdiff.1 ht
      simp only [mem_insert, mem_singleton, not_or] at ht0
      rw [filter_erase, erase_eq_of_notMem]
      · exact (mem_perfectMatchings.1 hM).2 t htS
      · simp only [mem_filter, not_and, not_or]
        exact fun _ => ⟨fun h => ht0.1 h.symm, fun h => ht0.2 h.symm⟩
  · intro M hM
    refine mem_filter.2 ⟨mem_perfectMatchings.2 ⟨fun e he => ?_, fun t ht => ?_⟩,
      mem_insert_self _ _⟩
    · rcases mem_insert.1 he with rfl | he
      · exact mem_edges.2 ⟨hy, hy', hyy'⟩
      · obtain ⟨h1, h2, h12⟩ := PerfectMatching.edge hM he
        exact mem_edges.2 ⟨(mem_sdiff.1 h1).1, (mem_sdiff.1 h2).1, h12⟩
    · -- No edge of `M` passes through `y` or `y'`.
      have hfree : ∀ u, (u = y ∨ u = y') → #{e ∈ M | e.1 = u ∨ e.2 = u} = 0 := by
        intro u hu
        refine card_eq_zero.2 (filter_eq_empty_iff.2 fun e he heu => ?_)
        obtain ⟨h1, h2, -⟩ := PerfectMatching.edge hM he
        have hu' : u ∉ S \ {y, y'} := fun h =>
          (mem_sdiff.1 h).2 (by rcases hu with rfl | rfl <;> simp)
        rcases heu with h' | h' <;> exact hu' (h' ▸ ‹_›)
      rw [filter_insert]
      by_cases h0t : y = t ∨ y' = t
      · rw [ite_eq_left h0t, card_insert_of_notMem, hfree t (h0t.imp Eq.symm Eq.symm)]
        exact fun h' => hnot M hM (mem_filter.1 h').1
      · rw [ite_eq_right h0t]
        push Not at h0t
        refine (mem_perfectMatchings.1 hM).2 t (mem_sdiff.2 ⟨ht, ?_⟩)
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨fun h => h0t.1 h.symm, fun h => h0t.2 h.symm⟩
  · intro M hM
    exact insert_erase (mem_filter.1 hM).2
  · intro M hM
    exact erase_insert (hnot M hM)
  · intro M hM
    rw [insert_erase (mem_filter.1 hM).2]

/-! ### Crossings -/

/-- `crossings` as a double sum of indicators over the edges of `M`. -/
theorem crossings_eq_sum_sum (M : Finset (ι × ι)) :
    crossings M = ∑ e ∈ M, ∑ f ∈ M, if e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2 then 1 else 0 := by
  rw [crossings, card_filter, sum_product]

/-- An edge `(y, y')` with no endpoint of `M` in `[y, y']` crosses no edge of `M`. -/
theorem crossings_insert_of_forall_not_mem_Icc {y y' : ι} {M : Finset (ι × ι)}
    (hM : ∀ e ∈ M, (e.1 < y ∨ y' < e.1) ∧ (e.2 < y ∨ y' < e.2)) (hyy' : y < y') :
    crossings (insert (y, y') M) = crossings M := by
  have hnot : (y, y') ∉ M := fun h => by
    rcases (hM _ h).1 with h' | h'
    · exact lt_irrefl _ h'
    · exact lt_asymm hyy' h'
  rw [crossings_eq_sum_sum, crossings_eq_sum_sum, sum_insert hnot]
  simp_rw [sum_insert hnot]
  have h1 : ∑ f ∈ M, (if y < f.1 ∧ f.1 < y' ∧ y' < f.2 then 1 else 0 : ℕ) = 0 :=
    sum_eq_zero fun f hf => ite_eq_right fun h => by rcases (hM f hf).1 with h' | h' <;> order
  have h2 : ∀ e ∈ M, (if e.1 < y ∧ y < e.2 ∧ e.2 < y' then 1 else 0 : ℕ) = 0 :=
    fun e he => ite_eq_right fun h => by rcases (hM e he).2 with h' | h' <;> order
  rw [ite_eq_right (fun h => lt_irrefl y h.1), h1, sum_congr rfl fun e he => by rw [h2 e he]]
  simp

/-! ### The partner swap -/

section PartnerSwap

variable {S : Finset ι} {y y' : ι}

/-- The partner swap on edges: exchange `y` and `y'` in both endpoints. -/
def partnerSwap (y y' : ι) : ι × ι ≃ ι × ι :=
  Equiv.prodCongr (Equiv.swap y y') (Equiv.swap y y')

@[simp] theorem partnerSwap_apply (e : ι × ι) :
    partnerSwap y y' e = (Equiv.swap y y' e.1, Equiv.swap y y' e.2) :=
  rfl

/-- Since no point of `S` lies strictly between `y` and `y'`, exchanging `y` and `y'` preserves
the order of two points of `S`, unless the two points are `y` and `y'`. -/
theorem swap_lt_swap_iff (hyy' : y < y') (hcons : ∀ z ∈ S, ¬(y < z ∧ z < y')) {u v : ι}
    (hu : u ∈ S) (hv : v ∈ S) (h1 : ¬(u = y ∧ v = y')) (h2 : ¬(u = y' ∧ v = y)) :
    Equiv.swap y y' u < Equiv.swap y y' v ↔ u < v := by
  have hu' := hcons u hu
  have hv' := hcons v hv
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  grind

variable (hy : y ∈ S) (hy' : y' ∈ S) (hyy' : y < y') (hcons : ∀ z ∈ S, ¬(y < z ∧ z < y'))
include hy hy' hyy' hcons

/-- The partner swap of a perfect matching of `S` not containing `(y, y')` is again one. -/
theorem map_partnerSwap_mem {M : Finset (ι × ι)} (hM : M ∈ perfectMatchings S)
    (he₀ : (y, y') ∉ M) :
    M.map (partnerSwap y y').toEmbedding ∈ {M ∈ perfectMatchings S | (y, y') ∉ M} := by
  have hτS : ∀ z ∈ S, Equiv.swap y y' z ∈ S := fun z hz => by
    rw [Equiv.swap_apply_def]
    split_ifs <;> assumption
  refine mem_filter.2 ⟨mem_perfectMatchings.2 ⟨fun e he => ?_, fun t ht => ?_⟩, fun h => ?_⟩
  · obtain ⟨e, he', rfl⟩ := mem_map.1 he
    obtain ⟨h1, h2, h12⟩ := PerfectMatching.edge hM he'
    refine mem_edges.2 ⟨hτS _ h1, hτS _ h2, ?_⟩
    rw [Equiv.coe_toEmbedding, partnerSwap_apply,
      swap_lt_swap_iff hyy' hcons h1 h2 (fun h => he₀ (h.1 ▸ h.2 ▸ he')) (fun h => by order)]
    exact h12
  · rw [filter_map, card_map]
    convert (mem_perfectMatchings.1 hM).2 _ (hτS t ht) using 3 with e
    simp only [Function.comp_apply, Equiv.coe_toEmbedding, partnerSwap_apply]
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_eq_iff]
  · obtain ⟨e, he, hee⟩ := mem_map.1 h
    obtain ⟨-, -, h12⟩ := PerfectMatching.edge hM he
    simp only [Equiv.coe_toEmbedding, partnerSwap_apply, Prod.mk.injEq,
      Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, Equiv.swap_apply_right] at hee
    rw [hee.1, hee.2] at h12
    exact lt_asymm hyy' h12

omit [CommRing R] hy hy' in
/-- "The weight of an edge `{y, u}` equals the weight of the edge `{y', u}`": the partner swap
preserves the weight of every edge of a perfect matching of `S` not containing `(y, y')`. -/
theorem weight_partnerSwap (A : Matrix ι ι R) (htwin_right : ∀ z ∈ S, y' < z → A y z = A y' z)
    (htwin_left : ∀ z ∈ S, z < y → A z y = A z y') {M : Finset (ι × ι)}
    (hM : M ∈ perfectMatchings S) (he₀ : (y, y') ∉ M) {e : ι × ι} (he : e ∈ M) :
    A (partnerSwap y y' e).1 (partnerSwap y y' e).2 = A e.1 e.2 := by
  obtain ⟨h1, h2, h12⟩ := PerfectMatching.edge hM he
  have hne : ¬(e.1 = y ∧ e.2 = y') := fun h => he₀ (h.1 ▸ h.2 ▸ he)
  have hc1 := hcons e.1 h1
  have hc2 := hcons e.2 h2
  simp only [partnerSwap_apply]
  by_cases hy1 : e.1 = y
  · have : y' < e.2 := by grind
    rw [hy1, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (by order) (by order)]
    exact (htwin_right _ h2 this).symm
  by_cases hy'1 : e.1 = y'
  · have : y' < e.2 := hy'1 ▸ h12
    rw [hy'1, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by order) (by order)]
    exact htwin_right _ h2 this
  rw [Equiv.swap_apply_of_ne_of_ne hy1 hy'1]
  by_cases hy2 : e.2 = y
  · have : e.1 < y := hy2 ▸ h12
    rw [hy2, Equiv.swap_apply_left]
    exact (htwin_left _ h1 this).symm
  by_cases hy'2 : e.2 = y'
  · have : e.1 < y := by grind
    rw [hy'2, Equiv.swap_apply_right]
    exact htwin_left _ h1 this
  rw [Equiv.swap_apply_of_ne_of_ne hy2 hy'2]

/-- "It changes the crossing number by an odd amount": for a perfect matching `M` of `S` not
containing `(y, y')`, `cr(M) + cr(M')` is odd, where `M'` is the partner swap of `M`. -/
theorem odd_crossings_add_crossings_partnerSwap {M : Finset (ι × ι)}
    (hM : M ∈ perfectMatchings S) (he₀ : (y, y') ∉ M) :
    Odd (crossings M + crossings (M.map (partnerSwap y y').toEmbedding)) := by
  set σ := partnerSwap y y'
  set c : ι × ι → ι × ι → ℕ := fun e f => if e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2 then 1 else 0
    with hc
  -- The edges `a` and `b` of `M` through `y` and `y'`.
  obtain ⟨a, ha⟩ := card_eq_one.1 ((mem_perfectMatchings.1 hM).2 y hy)
  obtain ⟨b, hb⟩ := card_eq_one.1 ((mem_perfectMatchings.1 hM).2 y' hy')
  have haM : a ∈ M ∧ (a.1 = y ∨ a.2 = y) := mem_filter.1 (ha ▸ mem_singleton_self a)
  have hbM : b ∈ M ∧ (b.1 = y' ∨ b.2 = y') := mem_filter.1 (hb ▸ mem_singleton_self b)
  have ha_uniq : ∀ e ∈ M, (e.1 = y ∨ e.2 = y) → e = a := fun e he h =>
    mem_singleton.1 (ha ▸ mem_filter.2 ⟨he, h⟩)
  have hb_uniq : ∀ e ∈ M, (e.1 = y' ∨ e.2 = y') → e = b := fun e he h =>
    mem_singleton.1 (hb ▸ mem_filter.2 ⟨he, h⟩)
  obtain ⟨ha1, ha2, ha12⟩ := PerfectMatching.edge hM haM.1
  obtain ⟨hb1, hb2, hb12⟩ := PerfectMatching.edge hM hbM.1
  have hab : a ≠ b := by
    intro h
    have hy'a : a.1 = y' ∨ a.2 = y' := h ▸ hbM.2
    have : a = (y, y') := by
      rcases haM.2 with h1 | h1 <;> rcases hy'a with h2 | h2 <;>
        first | exact Prod.ext h1 h2 | (exfalso; order)
    exact he₀ (this ▸ haM.1)
  -- Edges other than `a`, `b`, and their crossings, are unchanged by the swap.
  have hsep : ∀ e ∈ M, ∀ f ∈ M, (e, f) ≠ (a, b) → (e, f) ≠ (b, a) →
      ∀ u v, (u = e.1 ∨ u = e.2) → (v = f.1 ∨ v = f.2) → ¬(u = y ∧ v = y') ∧ ¬(u = y' ∧ v = y) := by
    intro e he f hf hab' hba' u v hu hv
    refine ⟨fun h => hab' ?_, fun h => hba' ?_⟩
    · rw [ha_uniq e he (by rcases hu with rfl | rfl <;> simp [h.1]),
        hb_uniq f hf (by rcases hv with rfl | rfl <;> simp [h.2])]
    · rw [hb_uniq e he (by rcases hu with rfl | rfl <;> simp [h.1]),
        ha_uniq f hf (by rcases hv with rfl | rfl <;> simp [h.2])]
  have hsame : ∀ e ∈ M, ∀ f ∈ M, (e, f) ≠ (a, b) → (e, f) ≠ (b, a) → c (σ e) (σ f) = c e f := by
    intro e he f hf hab' hba'
    obtain ⟨he1, he2, -⟩ := PerfectMatching.edge hM he
    obtain ⟨hf1, hf2, -⟩ := PerfectMatching.edge hM hf
    have hfe := hsep f hf e he (fun h => hba' (by simp_all)) (fun h => hab' (by simp_all))
    have hef := hsep e he f hf hab' hba'
    have i1 := swap_lt_swap_iff hyy' hcons he1 hf1 (hef _ _ (Or.inl rfl) (Or.inl rfl)).1
      (hef _ _ (Or.inl rfl) (Or.inl rfl)).2
    have i2 := swap_lt_swap_iff hyy' hcons hf1 he2 (hfe _ _ (Or.inl rfl) (Or.inr rfl)).1
      (hfe _ _ (Or.inl rfl) (Or.inr rfl)).2
    have i3 := swap_lt_swap_iff hyy' hcons he2 hf2 (hef _ _ (Or.inr rfl) (Or.inr rfl)).1
      (hef _ _ (Or.inr rfl) (Or.inr rfl)).2
    simp only [hc, σ, partnerSwap_apply, i1, i2, i3]
  -- "Between the two edges themselves, exactly one of `M`, `M'` has a crossing."
  have hpair : c a b + c (σ a) (σ b) + (c b a + c (σ b) (σ a)) = 1 := by
    have hay' : a.1 ≠ y' ∧ a.2 ≠ y' := ⟨fun h => hab (hb_uniq a haM.1 (Or.inl h)),
      fun h => hab (hb_uniq a haM.1 (Or.inr h))⟩
    have hby : b.1 ≠ y ∧ b.2 ≠ y := ⟨fun h => hab (ha_uniq b hbM.1 (Or.inl h)).symm,
      fun h => hab (ha_uniq b hbM.1 (Or.inr h)).symm⟩
    have hdisj : ∀ u v, (u = a.1 ∨ u = a.2) → (v = b.1 ∨ v = b.2) → u ≠ v := by
      intro u v hu hv huv
      have hu' : u ∈ S := by rcases hu with rfl | rfl <;> assumption
      exact hab (PerfectMatching.eq_of_mem hM hu' haM.1 hbM.1 (by rcases hu with rfl | rfl <;> simp)
        (by rcases hv with rfl | rfl <;> simp [huv]))
    have h11 := hdisj _ _ (Or.inl rfl) (Or.inl rfl)
    have h12 := hdisj _ _ (Or.inl rfl) (Or.inr rfl)
    have h21 := hdisj _ _ (Or.inr rfl) (Or.inl rfl)
    have h22 := hdisj _ _ (Or.inr rfl) (Or.inr rfl)
    have hca1 := hcons a.1 ha1
    have hca2 := hcons a.2 ha2
    have hcb1 := hcons b.1 hb1
    have hcb2 := hcons b.2 hb2
    have hya := haM.2
    have hy'b := hbM.2
    simp only [hc, σ, partnerSwap_apply, Equiv.swap_apply_def]
    grind
  -- Sum over all pairs of edges: all pairs other than `(a, b)`, `(b, a)` contribute evenly.
  have hsum : crossings M + crossings (M.map σ.toEmbedding) =
      ∑ p ∈ M ×ˢ M, (c p.1 p.2 + c (σ p.1) (σ p.2)) := by
    rw [crossings_eq_sum_sum, crossings_eq_sum_sum, sum_product]
    simp only [sum_map, Equiv.coe_toEmbedding, ← sum_add_distrib]
    rfl
  have hab_mem : (a, b) ∈ M ×ˢ M := mem_product.2 ⟨haM.1, hbM.1⟩
  have hba_mem : (b, a) ∈ (M ×ˢ M).erase (a, b) :=
    mem_erase.2 ⟨fun h => hab (Prod.mk.inj h).1.symm, mem_product.2 ⟨hbM.1, haM.1⟩⟩
  rw [hsum, ← add_sum_erase _ _ hab_mem, ← add_sum_erase _ _ hba_mem, ← add_assoc]
  simp only
  rw [show c a b + c (σ a) (σ b) + (c b a + c (σ b) (σ a)) = 1 from hpair]
  refine Even.one_add (even_sum _ fun p hp => ?_)
  obtain ⟨hpba, hp⟩ := mem_erase.1 hp
  obtain ⟨hpab, hp⟩ := mem_erase.1 hp
  obtain ⟨hp1, hp2⟩ := mem_product.1 hp
  rw [hsame p.1 hp1 p.2 hp2 hpab hpba]
  exact ⟨_, rfl⟩

end PartnerSwap

/-! ### The Twin rows lemma -/

/-- **Twin rows**, for two consecutive elements `y < y'` of an arbitrary finite index set `S`. -/
theorem pf_twin_rows_consecutive {S : Finset ι} (A : Matrix ι ι R) {y y' : ι} (hy : y ∈ S)
    (hy' : y' ∈ S) (hyy' : y < y') (hcons : ∀ z ∈ S, ¬(y < z ∧ z < y'))
    (htwin_right : ∀ z ∈ S, y' < z → A y z = A y' z)
    (htwin_left : ∀ z ∈ S, z < y → A z y = A z y') :
    pfaffian S A = A y y' * pfaffian (S \ {y, y'}) A := by
  set σ := partnerSwap y y'
  -- Split the matchings according to whether they contain the edge `(y, y')`.
  rw [pfaffian, ← sum_filter_add_sum_filter_not _ (fun M => (y, y') ∈ M)]
  -- "Matchings not containing `{y, y+1}`": the partner swap `M ↦ M'` is an involution without
  -- fixed points on them, it preserves the weight and changes the crossing number by an odd
  -- amount, "so the terms of `M` and `M'` cancel".
  have hcancel : ∑ M ∈ perfectMatchings S with (y, y') ∉ M,
      (-1) ^ crossings M * ∏ e ∈ M, A e.1 e.2 = 0 := by
    refine sum_involution (fun M _ => M.map σ.toEmbedding) (fun M hM => ?_) (fun M hM _ => ?_)
      (fun M hM => ?_) (fun M hM => ?_)
    · obtain ⟨hM, he₀⟩ := mem_filter.1 hM
      have hodd := odd_crossings_add_crossings_partnerSwap hy hy' hyy' hcons hM he₀
      have hsign : ((-1 : R) ^ crossings (M.map σ.toEmbedding)) = -(-1) ^ crossings M := by
        have h : (-1 : R) ^ (crossings M + crossings (M.map σ.toEmbedding)) = -1 :=
          hodd.neg_one_pow
        rw [pow_add] at h
        calc (-1 : R) ^ crossings (M.map σ.toEmbedding)
            = ((-1) ^ crossings M * (-1) ^ crossings M) *
                (-1) ^ crossings (M.map σ.toEmbedding) := by
              rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
          _ = -(-1) ^ crossings M := by rw [mul_assoc, h, mul_neg_one]
      have hweight : ∏ e ∈ M.map σ.toEmbedding, A e.1 e.2 = ∏ e ∈ M, A e.1 e.2 := by
        rw [prod_map]
        exact prod_congr rfl fun e he =>
          weight_partnerSwap hyy' hcons A htwin_right htwin_left hM he₀ he
      rw [hsign, hweight]
      ring
    · obtain ⟨hM, he₀⟩ := mem_filter.1 hM
      intro h
      have hodd := odd_crossings_add_crossings_partnerSwap hy hy' hyy' hcons hM he₀
      rw [h, ← two_mul] at hodd
      exact Nat.not_even_iff_odd.2 hodd (even_two_mul _)
    · obtain ⟨hM, he₀⟩ := mem_filter.1 hM
      exact map_partnerSwap_mem hy hy' hyy' hcons hM he₀
    · rw [map_map]
      convert map_refl (s := M)
      ext e : 1
      simp [σ]
  -- "Matchings containing `{y, y+1}`": the edge `(y, y')` crosses no other edge, "and these terms
  -- sum to `A_{y,y+1} Pf(A_{[n] ∖ {y,y+1}})`".
  have hcontain : ∑ M ∈ perfectMatchings S with (y, y') ∈ M,
      (-1) ^ crossings M * ∏ e ∈ M, A e.1 e.2 = A y y' * pfaffian (S \ {y, y'}) A := by
    rw [sum_perfectMatchings_filter_mem hy hy' hyy', pfaffian, mul_sum]
    refine sum_congr rfl fun M hM => ?_
    have hout : ∀ e ∈ M, (e.1 < y ∨ y' < e.1) ∧ (e.2 < y ∨ y' < e.2) := by
      intro e he
      obtain ⟨h1, h2, -⟩ := PerfectMatching.edge hM he
      have hS : ∀ z ∈ S \ {y, y'}, z < y ∨ y' < z := by
        intro z hz
        obtain ⟨hz, hz'⟩ := mem_sdiff.1 hz
        simp only [mem_insert, mem_singleton, not_or] at hz'
        have := hcons z hz
        grind
      exact ⟨hS _ h1, hS _ h2⟩
    have hnot : (y, y') ∉ M := fun h => by
      rcases (hout _ h).1 with h' | h'
      · exact lt_irrefl _ h'
      · exact lt_asymm hyy' h'
    rw [crossings_insert_of_forall_not_mem_Icc hout hyy', prod_insert hnot]
    ring
  rw [hcancel, hcontain, add_zero]

/-- **Twin rows**, the reference's form: rows `y` and `y + 1` of `[n]`. -/
theorem pf_twin_rows (n : ℕ) (A : Matrix ℕ ℕ R) {y : ℕ} (hy : 1 ≤ y) (hyn : y + 1 ≤ n)
    (htwin_right : ∀ z ∈ Icc 1 n, y + 1 < z → A y z = A (y + 1) z)
    (htwin_left : ∀ z ∈ Icc 1 n, z < y → A z y = A z (y + 1)) :
    pfaffian (Icc 1 n) A = A y (y + 1) * pfaffian (Icc 1 n \ {y, y + 1}) A :=
  pf_twin_rows_consecutive A (mem_Icc.2 ⟨hy, by omega⟩) (mem_Icc.2 ⟨by omega, hyn⟩)
    (Nat.lt_succ_self y) (fun z _ h => by omega) htwin_right htwin_left
