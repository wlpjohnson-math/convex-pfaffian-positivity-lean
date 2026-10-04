import PfaffianLean.TwinRows

/-!
# Further facts about Pfaffians

* `PerfectMatching.two_mul_card`: a perfect matching of `S` has `#S / 2` edges.
* `pfaffian_smul`: `Pf(c A) = c ^ (#S / 2) Pf A`.
* `pfaffian_image_strictMono`: the Pfaffian is unchanged under a strictly monotone change of
  index (used for the map `φ` in Coefficient positivity).
* `pfaffian_eq_zero_of_row`: a zero row (on the upper entries) makes the Pfaffian vanish.
* `pfaffian_skewOnes`: the skew matrix `𝒯` with all upper entries `1` has Pfaffian `1`, proved
  by the first-row expansion.
-/

open Finset

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

/-- A perfect matching of `S` has `#S / 2` edges: `2 * #M = #S`. -/
theorem PerfectMatching.two_mul_card {S : Finset ι} {M : Finset (ι × ι)}
    (hM : M ∈ perfectMatchings S) : 2 * #M = #S := by
  have h := PerfectMatching.sum_eq hM (fun _ => (1 : ℕ))
  simp only [sum_const, smul_eq_mul, mul_one] at h
  omega

/-- `Pf(c A) = c ^ (#S / 2) Pf A`. -/
theorem pfaffian_smul (S : Finset ι) (c : R) (A : Matrix ι ι R) :
    pfaffian S (c • A) = c ^ (#S / 2) * pfaffian S A := by
  rw [pfaffian, pfaffian, mul_sum]
  refine sum_congr rfl fun M hM => ?_
  have hcard : #M = #S / 2 := by
    have := PerfectMatching.two_mul_card hM
    omega
  simp only [Matrix.smul_apply, smul_eq_mul, prod_mul_distrib, prod_const, hcard]
  ring

/-- **Reindexing.** The Pfaffian is unchanged under a strictly monotone change of index: the
Pfaffian of `A` on `ψ(S)` is the Pfaffian on `S` of `A` read through `ψ`. -/
theorem pfaffian_image_strictMono {κ : Type*} [LinearOrder κ] {ψ : ι → κ} (hψ : StrictMono ψ)
    (S : Finset ι) (A : Matrix κ κ R) :
    pfaffian (S.image ψ) A = pfaffian S (A.submatrix ψ ψ) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Finset.eq_empty_of_isEmpty S, pfaffian_empty]
  -- `ψ` on edges, and a left inverse `G` of it.
  set Ψ : ι × ι → κ × κ := Prod.map ψ ψ with hΨ_def
  set g := Function.invFun ψ
  have hg : ∀ i, g (ψ i) = i := Function.leftInverse_invFun hψ.injective
  set G : κ × κ → ι × ι := Prod.map g g with hG_def
  have hΨinj : Function.Injective Ψ := hψ.injective.prodMap hψ.injective
  have hGΨ : ∀ e, G (Ψ e) = e := fun e => Prod.ext (hg e.1) (hg e.2)
  -- `ψ` preserves edges, matchings and crossings.
  have hedge : ∀ e : ι × ι, Ψ e ∈ edges (S.image ψ) ↔ e ∈ edges S := by
    intro e
    simp only [mem_edges, hΨ_def, Prod.map_fst, Prod.map_snd, mem_image,
      hψ.injective.eq_iff, exists_eq_right, hψ.lt_iff_lt]
  have hcount : ∀ (M : Finset (ι × ι)) (t : ι),
      #{e ∈ M.image Ψ | e.1 = ψ t ∨ e.2 = ψ t} = #{e ∈ M | e.1 = t ∨ e.2 = t} := by
    intro M t
    rw [filter_image, card_image_of_injective _ hΨinj]
    simp only [hΨ_def, Prod.map_fst, Prod.map_snd, hψ.injective.eq_iff]
  have hcross : ∀ M : Finset (ι × ι), crossings (M.image Ψ) = crossings M := by
    intro M
    rw [crossings_eq_sum_sum, crossings_eq_sum_sum, sum_image fun _ _ _ _ h => hΨinj h]
    refine sum_congr rfl fun e _ => ?_
    rw [sum_image fun _ _ _ _ h => hΨinj h]
    simp only [hΨ_def, Prod.map_fst, Prod.map_snd, hψ.lt_iff_lt]
  have hmatch : ∀ M ∈ perfectMatchings S, M.image Ψ ∈ perfectMatchings (S.image ψ) := by
    intro M hM
    refine mem_perfectMatchings.2 ⟨fun e' he' => ?_, fun t' ht' => ?_⟩
    · obtain ⟨e, he, rfl⟩ := mem_image.1 he'
      exact (hedge e).2 ((mem_perfectMatchings.1 hM).1 he)
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 ht'
      rw [hcount]
      exact (mem_perfectMatchings.1 hM).2 t ht
  -- Every edge of a matching of `ψ(S)` comes from an edge of `S`.
  have hrange : ∀ M' ∈ perfectMatchings (S.image ψ), ∀ e' ∈ M', Ψ (G e') = e' := by
    intro M' hM' e' he'
    obtain ⟨h1, h2, -⟩ := PerfectMatching.edge hM' he'
    obtain ⟨a, -, ha⟩ := mem_image.1 h1
    obtain ⟨b, -, hb⟩ := mem_image.1 h2
    refine Prod.ext ?_ ?_
    · change ψ (g e'.1) = e'.1
      rw [← ha, hg]
    · change ψ (g e'.2) = e'.2
      rw [← hb, hg]
  have himage : ∀ M' ∈ perfectMatchings (S.image ψ), (M'.image G).image Ψ = M' := by
    intro M' hM'
    rw [image_image]
    conv_rhs => rw [← image_id (s := M')]
    exact image_congr fun e' he' => hrange M' hM' e' he'
  symm
  refine sum_nbij' (fun M => M.image Ψ) (fun M' => M'.image G) (fun M hM => hmatch M hM)
    (fun M' hM' => ?_) (fun M _ => ?_) (fun M' hM' => himage M' hM') (fun M hM => ?_)
  · -- the preimage of a matching of `ψ(S)` is a matching of `S`
    have hM'' := hM'
    rw [← himage M' hM'] at hM''
    refine mem_perfectMatchings.2 ⟨fun e he => ?_, fun t ht => ?_⟩
    · obtain ⟨e', he', rfl⟩ := mem_image.1 he
      rw [← hedge, hrange M' hM' e' he']
      exact (mem_perfectMatchings.1 hM').1 he'
    · rw [← hcount, himage M' hM']
      exact (mem_perfectMatchings.1 hM').2 _ (mem_image_of_mem ψ ht)
  · rw [image_image]
    conv_rhs => rw [← image_id (s := M)]
    exact image_congr fun e _ => hGΨ e
  · rw [hcross, prod_image fun _ _ _ _ h => hΨinj h]
    rfl

/-- A zero row: if every entry of row and column `y ∈ S` that the Pfaffian reads is `0`, then
`Pf_S A = 0`. -/
theorem pfaffian_eq_zero_of_row {S : Finset ι} {A : Matrix ι ι R} {y : ι} (hy : y ∈ S)
    (hrow : ∀ z ∈ S, y < z → A y z = 0) (hcol : ∀ z ∈ S, z < y → A z y = 0) :
    pfaffian S A = 0 := by
  refine sum_eq_zero fun M hM => ?_
  -- Every perfect matching uses an entry of row (or column) `y`.
  obtain ⟨e, he⟩ := card_eq_one.1 ((mem_perfectMatchings.1 hM).2 y hy)
  have heM : e ∈ M ∧ (e.1 = y ∨ e.2 = y) := mem_filter.1 (he ▸ mem_singleton_self e)
  obtain ⟨h1, h2, h12⟩ := PerfectMatching.edge hM heM.1
  have h0 : A e.1 e.2 = 0 := by
    rcases heM.2 with h | h
    · rw [h] at h12 ⊢
      exact hrow _ h2 h12
    · rw [h] at h12 ⊢
      exact hcol _ h1 h12
  rw [prod_eq_zero heM.1 h0, mul_zero]

/-- `Pf(𝒯) = 1` on every index set of even size. -/
theorem pfaffian_skewExtension_ones_of_even_card {S : Finset ι} (hS : Even #S) :
    pfaffian S (skewExtension (Matrix.of fun _ _ => (1 : R))) = 1 := by
  -- By the first-row expansion and induction, the Pfaffian is `∑_{l=2}^{2p} (-1)^l = 1`.
  -- The alternating sum: `∑_{l ∈ s} (-1)^(rank of l in s)` is `1` for `#s` odd and `0` for `#s`
  -- even (induction on `s`, adding a new largest element).
  have halt : ∀ s : Finset ι,
      ∑ l ∈ s, (-1 : R) ^ #{x ∈ s | x < l} = if Even #s then 0 else 1 := by
    intro s
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert m s hm ih =>
      have hms : m ∉ s := fun h => lt_irrefl m (hm m h)
      rw [sum_insert hms, card_insert_of_notMem hms]
      have hm_rank : ({x ∈ insert m s | x < m} : Finset ι) = s := by
        ext x
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hx, hxm⟩
          · exact absurd hxm (lt_irrefl _)
          · exact hx
        · exact fun hx => ⟨Or.inr hx, hm x hx⟩
      have hl_rank : ∀ l ∈ s, ({x ∈ insert m s | x < l} : Finset ι) = {x ∈ s | x < l} := by
        intro l hl
        rw [filter_insert, ite_eq_right (fun h => lt_asymm h (hm l hl))]
      rw [hm_rank, sum_congr rfl fun l hl => by rw [hl_rank l hl], ih]
      rcases Nat.even_or_odd #s with h | h
      · rw [ite_eq_left h, h.neg_one_pow, ite_eq_right (Nat.not_even_iff_odd.2 h.add_one),
          add_zero]
      · rw [ite_eq_right (Nat.not_even_iff_odd.2 h), h.neg_one_pow, ite_eq_left h.add_one,
          neg_add_cancel]
  induction hn : #S using Nat.strong_induction_on generalizing S with
  | _ k ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact pfaffian_empty _
    obtain ⟨r, hr⟩ := hS
    -- First-row expansion along the minimum `m` of `S`.
    set m := S.min' hne
    have hSm : S = insert m (S.erase m) := (insert_erase (S.min'_mem hne)).symm
    have hlt : ∀ x ∈ S.erase m, m < x := fun x hx =>
      S.min'_lt_of_mem_erase_min' hne hx
    have hcard : #(S.erase m) + 1 = #S := card_erase_add_one (S.min'_mem hne)
    rw [hSm, pfaffian_insert_of_forall_lt hlt]
    -- By induction, each `Pf(𝒯)` on `S ∖ {m, l}` is `1`; every entry `𝒯_{m l}` is `1`.
    have hrest : ∀ l ∈ S.erase m, (-1 : R) ^ #{x ∈ S.erase m | x < l} *
        skewExtension (Matrix.of fun _ _ => (1 : R)) m l *
          pfaffian ((S.erase m).erase l) (skewExtension (Matrix.of fun _ _ => (1 : R))) =
        (-1) ^ #{x ∈ S.erase m | x < l} := by
      intro l hl
      have hcl : #((S.erase m).erase l) + 1 = #(S.erase m) := card_erase_add_one hl
      rw [ih #((S.erase m).erase l) (by omega) ⟨r - 1, by omega⟩ rfl, mul_one]
      simp [skewExtension, hlt l hl]
    -- What remains is an alternating sum of odd length, which is `1`.
    rw [sum_congr rfl hrest, halt, ite_eq_right (Nat.not_even_iff_odd.2 ⟨r - 1, by omega⟩)]

/-- **`Pf(𝒯_n) = 1`** for every even `n`, where `𝒯_n` is the skew matrix with all upper entries
`1`. -/
theorem pfaffian_skewOnes (n : ℕ) (hn : Even n) :
    pfaffian (Icc 1 n) (skewExtension (Matrix.of fun _ _ => (1 : R))) = 1 :=
  pfaffian_skewExtension_ones_of_even_card (by simpa using hn)
