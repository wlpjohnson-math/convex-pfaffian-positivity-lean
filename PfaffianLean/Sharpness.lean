import PfaffianLean.Rainbow

/-!
# Only the rainbow survives

For even `n`, the rainbow matching `{(k, n + 1 - k) : 1 ≤ k ≤ n/2}` is the only perfect matching
`M` of `[n]` whose product `∏_{(a,b) ∈ M} f(x_b - x_a)` is a lower bound for `Pf A_f(x)` over all
positive, nonincreasing, convex `f` and all `x_1 < ⋯ < x_n`: for every other `M` some `(f, x)`
has `Pf A_f(x) < ∏_M f`.

The construction, for a matching `M` that first departs from the rainbow at the pair
`(k + 1, n - k)`, uses `f(r) = max(9 - r, 1)` and these points:
* `1, …, k + 1` at `-8(k + 1 - i) - 4` and `n - k, …, n` at `8(i - (n - k)) + 4`; any two of these
  are at distance `≥ 8`, where `f = 1`;
* the inner points `k + 2, …, n - k - 1` at `ε i`.

At `ε = 0` the inner points coincide, so Twin rows peels them off in pairs with factor `f(0) = 9`,
and what is left has all entries `1`: `Pf = 9^(n/2 - k - 1)`. The product over `M` is at least
`(25/9) · 9^(n/2 - k - 1)`, since `M` pairs `k + 1` and `n - k` with inner points (`f(4) = 5`).
Both sides are continuous in `ε`, so the strict inequality persists for small `ε > 0`, where the
points are strictly increasing.
-/

open Finset

/-! ### The rainbow matching -/

/-- The rainbow matching of `[n]`: the pairs `(k, n + 1 - k)`, `1 ≤ k ≤ n / 2`. -/
def rainbow (n : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 (n / 2)).image fun k => (k, n + 1 - k)

/-- For even `n`, the rainbow matching is a perfect matching of `[n]`. -/
theorem rainbow_mem_perfectMatchings (n : ℕ) (hn : Even n) :
    rainbow n ∈ perfectMatchings (Icc 1 n) := by
  obtain ⟨m, rfl⟩ := hn
  refine mem_perfectMatchings.2 ⟨fun e he => ?_, fun s hs => ?_⟩
  · -- Each pair `(k, n + 1 - k)`, `1 ≤ k ≤ n/2`, has `k < n + 1 - k` in `[n]`.
    obtain ⟨k, hk, rfl⟩ := mem_image.1 he
    simp only [mem_Icc] at hk
    exact mem_edges.2 ⟨mem_Icc.2 ⟨hk.1, by omega⟩, mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
  · -- The pair through `s` is `(s, n + 1 - s)` if `s ≤ n/2` and `(n + 1 - s, s)` otherwise.
    simp only [mem_Icc] at hs
    rw [card_eq_one]
    by_cases hs2 : s ≤ m
    · refine ⟨(s, m + m + 1 - s), ?_⟩
      ext ⟨a, b⟩
      simp only [rainbow, mem_filter, mem_image, mem_Icc, Prod.mk.injEq, mem_singleton]
      constructor
      · rintro ⟨⟨k, hk, hka, hkb⟩, h⟩
        omega
      · rintro ⟨ha, hb⟩
        exact ⟨⟨a, ⟨by omega, by omega⟩, rfl, by omega⟩, Or.inl ha⟩
    · refine ⟨(m + m + 1 - s, s), ?_⟩
      ext ⟨a, b⟩
      simp only [rainbow, mem_filter, mem_image, mem_Icc, Prod.mk.injEq, mem_singleton]
      constructor
      · rintro ⟨⟨k, hk, hka, hkb⟩, h⟩
        omega
      · rintro ⟨ha, hb⟩
        exact ⟨⟨a, ⟨by omega, by omega⟩, rfl, by omega⟩, Or.inr hb⟩

/-- **First departure from the rainbow.** A perfect matching `M ≠` rainbow contains the
rainbow pairs `(i, n + 1 - i)` for `i ≤ k` but not `(k + 1, n - k)`, for some `k < n / 2`. -/
theorem exists_first_departure {n : ℕ} {M : Finset (ℕ × ℕ)}
    (hM : M ∈ perfectMatchings (Icc 1 n)) (hMr : M ≠ rainbow n) :
    ∃ k, k + 1 ≤ n / 2 ∧ (∀ i ∈ Icc 1 k, (i, n + 1 - i) ∈ M) ∧ (k + 1, n - k) ∉ M := by
  by_contra hcon
  push Not at hcon
  -- Otherwise, by induction, `M` contains every rainbow pair,
  have hall : ∀ k, k ≤ n / 2 → ∀ i ∈ Icc 1 k, (i, n + 1 - i) ∈ M := by
    intro k
    induction k with
    | zero => intro _ i hi; simp at hi
    | succ k ih =>
      intro hk i hi
      simp only [mem_Icc] at hi
      rcases (show i ≤ k ∨ i = k + 1 by omega) with hik | rfl
      · exact ih (by omega) i (mem_Icc.2 ⟨hi.1, hik⟩)
      · simpa [show n + 1 - (k + 1) = n - k by omega] using hcon k hk (ih (by omega))
  -- so the rainbow is contained in `M`; both have `n/2` pairs, so they are equal.
  have hsub : rainbow n ⊆ M := fun e he => by
    obtain ⟨k, hk, rfl⟩ := mem_image.1 he
    exact hall (n / 2) le_rfl k hk
  have hcardM : #M = n / 2 := by
    have := PerfectMatching.two_mul_card hM
    rw [Nat.card_Icc] at this
    omega
  have hcardR : #(rainbow n) = n / 2 := by
    rw [rainbow, card_image_of_injOn fun a _ b _ hab => (Prod.mk.inj hab).1, Nat.card_Icc]
    omega
  exact hMr (eq_of_subset_of_card_le hsub (by omega)).symm

/-! ### General facts -/

/-- A product over the points of `S` is the product over the edges of a perfect matching of `S`
of the products over their two endpoints. -/
theorem PerfectMatching.prod_eq {ι : Type*} [LinearOrder ι] {S : Finset ι}
    {M : Finset (ι × ι)} (hM : M ∈ perfectMatchings S) (h : ι → ℝ) :
    ∏ t ∈ S, h t = ∏ e ∈ M, (h e.1 * h e.2) := by
  -- `PerfectMatching.sum_eq` in `Additive ℝ`.
  have key := congrArg Additive.toMul
    (PerfectMatching.sum_eq (β := Additive ℝ) hM fun t => Additive.ofMul (h t))
  simpa only [toMul_sum, toMul_add, toMul_ofMul] using key

/-- The Pfaffian is continuous in the entries. -/
theorem continuous_pfaffian {ι : Type*} [LinearOrder ι] {X : Type*} [TopologicalSpace X]
    (S : Finset ι) {A : X → Matrix ι ι ℝ} (hA : ∀ i j, Continuous fun x => A x i j) :
    Continuous fun x => pfaffian S (A x) := by
  unfold pfaffian
  exact continuous_finsetSum _ fun M _ =>
    continuous_const.mul (continuous_finsetProd _ fun e _ => hA _ _)

/-! ### The construction -/

/-- The kernel of the construction: `f(r) = max(9 - r, 1)`. -/
noncomputable def sharpKernel (r : ℝ) : ℝ :=
  max (9 - r) 1

/-- The points of the construction, for a departure at `(k + 1, n - k)`: `i ≤ k + 1` at
`8i - 8k - 12`, `i ≥ n - k` at `8i + 8k - 8n + 4`, and the inner points at `ε i`. -/
noncomputable def sharpPoints (n k : ℕ) (ε : ℝ) (i : ℕ) : ℝ :=
  if i ≤ k + 1 then 8 * (i : ℝ) - 8 * k - 12
  else if n - k ≤ i then 8 * (i : ℝ) + 8 * k - 8 * n + 4
  else ε * i

theorem sharpKernel_pos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < sharpKernel t := fun _ _ =>
  lt_of_lt_of_le one_pos (le_max_right _ _)

theorem sharpKernel_antitoneOn : AntitoneOn sharpKernel (Set.Ioi 0) := fun _ _ _ _ hab =>
  max_le_max (by linarith) le_rfl

/-- `max(9 - r, 1)` is a maximum of two affine functions, hence convex. -/
theorem sharpKernel_convexOn : ConvexOn ℝ (Set.Ioi 0) sharpKernel := by
  have haff : ConvexOn ℝ (Set.Ioi 0) fun r : ℝ => 9 - r :=
    ⟨convex_Ioi 0, fun x _ y _ a b _ _ hab => le_of_eq (by
      simp only [smul_eq_mul]
      linear_combination (-9 : ℝ) * hab)⟩
  exact haff.sup (convexOn_const 1 (convex_Ioi 0))

theorem continuous_sharpKernel : Continuous sharpKernel :=
  (continuous_const.sub continuous_id).max continuous_const

theorem sharpKernel_eq_one {r : ℝ} (hr : 8 ≤ r) : sharpKernel r = 1 :=
  max_eq_right (by linarith)

theorem one_le_sharpKernel (r : ℝ) : 1 ≤ sharpKernel r :=
  le_max_right _ _

/-- The three pieces of `sharpPoints`. -/
theorem sharpPoints_of_le {n k : ℕ} {ε : ℝ} {i : ℕ} (hi : i ≤ k + 1) :
    sharpPoints n k ε i = 8 * (i : ℝ) - 8 * k - 12 := by
  simp [sharpPoints, hi]

theorem sharpPoints_of_mid {n k : ℕ} {ε : ℝ} {i : ℕ} (h1 : k + 1 < i) (h2 : i < n - k) :
    sharpPoints n k ε i = ε * i := by
  simp [sharpPoints, not_le.2 h1, not_le.2 h2]

theorem sharpPoints_of_ge {n k : ℕ} {ε : ℝ} {i : ℕ} (h1 : k + 1 < i) (h2 : n - k ≤ i) :
    sharpPoints n k ε i = 8 * (i : ℝ) + 8 * k - 8 * n + 4 := by
  simp [sharpPoints, not_le.2 h1, h2]

/-- For `0 < ε` and `ε n < 4`, the points are strictly increasing on `[n]`. -/
theorem sharpPoints_strictMonoOn {n k : ℕ} {ε : ℝ} (hε : 0 < ε) (hεn : ε * n < 4) :
    StrictMonoOn (sharpPoints n k ε) (Set.Icc 1 n) := by
  intro a ha b hb hab
  simp only [Set.mem_Icc] at ha hb
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
  have hbn : (b : ℝ) ≤ n := by exact_mod_cast hb.2
  -- The inner points lie in `(0, 4)`, the left points at `≤ -4` and the right points at `≥ 4`.
  have hmid_pos : 0 < ε * a := mul_pos hε (by linarith)
  have hmid_lt : ε * b < 4 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hbn hε.le) hεn
  have hεab : ε * a < ε * b := mul_lt_mul_of_pos_left hab' hε
  have hleft : ∀ i : ℕ, i ≤ k + 1 → 8 * (i : ℝ) - 8 * k - 12 ≤ -4 := fun i hi => by
    have : (i : ℝ) ≤ k + 1 := by exact_mod_cast hi
    linarith
  have hright : ∀ i : ℕ, n - k ≤ i → 4 ≤ 8 * (i : ℝ) + 8 * k - 8 * n + 4 := fun i hi => by
    have : (n : ℝ) ≤ i + k := by exact_mod_cast (by omega : n ≤ i + k)
    linarith
  rcases (show a ≤ k + 1 ∨ (k + 1 < a ∧ a < n - k) ∨ (k + 1 < a ∧ n - k ≤ a) by omega)
    with ha' | ⟨ha1', ha2'⟩ | ⟨ha1', ha2'⟩ <;>
  rcases (show b ≤ k + 1 ∨ (k + 1 < b ∧ b < n - k) ∨ (k + 1 < b ∧ n - k ≤ b) by omega)
    with hb' | ⟨hb1', hb2'⟩ | ⟨hb1', hb2'⟩
  · rw [sharpPoints_of_le ha', sharpPoints_of_le hb']; linarith
  · rw [sharpPoints_of_le ha', sharpPoints_of_mid hb1' hb2']; linarith [hleft a ha']
  · rw [sharpPoints_of_le ha', sharpPoints_of_ge hb1' hb2']
    linarith [hleft a ha', hright b hb2']
  · omega
  · rw [sharpPoints_of_mid ha1' ha2', sharpPoints_of_mid hb1' hb2']; exact hεab
  · rw [sharpPoints_of_mid ha1' ha2', sharpPoints_of_ge hb1' hb2']
    linarith [hright b hb2']
  · omega
  · omega
  · rw [sharpPoints_of_ge ha1' ha2', sharpPoints_of_ge hb1' hb2']; linarith

/-- **The Pfaffian at `ε = 0`.** The inner points coincide; Twin rows peels them off in pairs
(`f(0) = 9`), and the remaining `2k + 2` points have all entries `f(≥ 8) = 1`. -/
theorem pfaffian_sharp_zero {n k : ℕ} (hn : Even n) (hk : k + 1 ≤ n / 2) :
    pfaffian (Icc 1 n) (kernel sharpKernel (sharpPoints n k 0)) = 9 ^ (n / 2 - k - 1) := by
  set K := kernel sharpKernel (sharpPoints n k 0)
  set c := n / 2 - k - 1
  have hc : n = 2 * c + 2 * k + 2 := by
    obtain ⟨m, rfl⟩ := hn
    omega
  -- After `r` peeling steps the set is `S r = [1, k+1] ∪ [k+2+2r, n]`.
  set S : ℕ → Finset ℕ := fun r => Icc 1 (k + 1) ∪ Icc (k + 2 + 2 * r) n
  -- At `ε = 0` the inner points sit at `0`.
  have hmid : ∀ i, k + 1 < i → i < n - k → sharpPoints n k 0 i = 0 := fun i h1 h2 => by
    rw [sharpPoints_of_mid h1 h2, zero_mul]
  -- Twin rows: two consecutive inner points `y, y+1` have the same row, so
  -- `Pf(S r) = f(0) Pf(S (r+1)) = 9 Pf(S (r+1))`.
  have hstep : ∀ r, r < c → pfaffian (S r) K = 9 * pfaffian (S (r + 1)) K := by
    intro r hr
    have hy0 : sharpPoints n k 0 (k + 2 + 2 * r) = 0 := hmid _ (by omega) (by omega)
    have hy1 : sharpPoints n k 0 (k + 2 + 2 * r + 1) = 0 := hmid _ (by omega) (by omega)
    have hyS : k + 2 + 2 * r ∈ S r := by simp only [S, mem_union, mem_Icc]; omega
    have hy1S : k + 2 + 2 * r + 1 ∈ S r := by simp only [S, mem_union, mem_Icc]; omega
    rw [pf_twin_rows_consecutive K hyS hy1S (by omega) (fun z _ => by omega)
      (fun z _ _ => by simp only [K, kernel, Matrix.of_apply, hy0, hy1])
      (fun z _ _ => by simp only [K, kernel, Matrix.of_apply, hy0, hy1])]
    have hK : K (k + 2 + 2 * r) (k + 2 + 2 * r + 1) = 9 := by
      simp only [K, kernel, Matrix.of_apply, hy0, hy1, sharpKernel]
      norm_num
    have hS : S r \ {k + 2 + 2 * r, k + 2 + 2 * r + 1} = S (r + 1) := by
      ext z
      simp only [S, mem_sdiff, mem_union, mem_Icc, mem_insert, mem_singleton]
      omega
    rw [hK, hS]
  have hiter : ∀ j, j ≤ c → pfaffian (S (c - j)) K = 9 ^ j * pfaffian (S c) K := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [hstep _ (by omega), show c - (j + 1) + 1 = c - j by omega, ih (by omega)]
      ring
  -- `S 0 = [n]`, and on `S c = [1, k+1] ∪ [n-k, n]` every entry is `f(≥ 8) = 1`, so its
  -- Pfaffian is `Pf(𝒯_{2k+2}) = 1`.
  have hS0 : S 0 = Icc 1 n := by
    ext z
    simp only [S, mem_union, mem_Icc]
    omega
  have hSc : pfaffian (S c) K = 1 := by
    have hcS : S c = Icc 1 (k + 1) ∪ Icc (n - k) n := by
      simp only [S]
      congr 2
      omega
    rw [pfaffian_congr (B := skewExtension (Matrix.of fun _ _ => (1 : ℝ))) ?_]
    · apply pfaffian_skewExtension_ones_of_even_card
      rw [hcS, card_union_of_disjoint (disjoint_left.2 fun z hz hz' => by
        simp only [mem_Icc] at hz hz'
        omega), Nat.card_Icc, Nat.card_Icc]
      exact ⟨k + 1, by omega⟩
    · intro a ha b hb hab
      rw [hcS] at ha hb
      simp only [mem_union, mem_Icc] at ha hb
      simp only [skewExtension, Matrix.of_apply, hab, ↓reduceIte, K, kernel]
      apply sharpKernel_eq_one
      have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [sharpPoints_of_le ha.2, sharpPoints_of_le hb.2]; linarith
      · rw [sharpPoints_of_le ha.2, sharpPoints_of_ge (by omega) hb.1]
        have h1 : (a : ℝ) ≤ k + 1 := by exact_mod_cast ha.2
        have h2 : (n : ℝ) ≤ b + k := by exact_mod_cast (by omega : n ≤ b + k)
        linarith
      · omega
      · rw [sharpPoints_of_ge (by omega) ha.1, sharpPoints_of_ge (by omega) hb.1]; linarith
  rw [← hS0, show (0 : ℕ) = c - c by simp, hiter c le_rfl, hSc, mul_one]

/-- **The product at `ε = 0`.** If `M` contains the rainbow pairs `(i, n + 1 - i)`, `i ≤ k`, but
not `(k + 1, n - k)`, its product is at least `(25/9) · 9^(n/2 - k - 1)`. -/
theorem prod_sharp_zero {n k : ℕ} (hn : Even n) (hk : k + 1 ≤ n / 2) {M : Finset (ℕ × ℕ)}
    (hM : M ∈ perfectMatchings (Icc 1 n)) (hout : ∀ i ∈ Icc 1 k, (i, n + 1 - i) ∈ M)
    (hdep : (k + 1, n - k) ∉ M) :
    25 / 9 * 9 ^ (n / 2 - k - 1) ≤
      ∏ e ∈ M, sharpKernel (sharpPoints n k 0 e.2 - sharpPoints n k 0 e.1) := by
  set x := sharpPoints n k 0
  have hn2 : n = 2 * (n / 2) := by
    obtain ⟨m, rfl⟩ := hn
    omega
  have hk2 : 2 * k + 2 ≤ n := by omega
  -- Positions at `ε = 0`: `x(k+1) = -4`, `x(n-k) = 4`, and the inner points at `0`.
  have hx_mid : ∀ i, k + 1 < i → i < n - k → x i = 0 := fun i h1 h2 => by
    simp only [x]
    rw [sharpPoints_of_mid h1 h2, zero_mul]
  have hx_L : x (k + 1) = -4 := by
    simp only [x]
    rw [sharpPoints_of_le le_rfl]
    push_cast
    ring
  have hx_R : x (n - k) = 4 := by
    simp only [x]
    rw [sharpPoints_of_ge (by omega) le_rfl, Nat.cast_sub (by omega : k ≤ n)]
    ring
  have hf0 : sharpKernel 0 = 9 := by norm_num [sharpKernel]
  have hf4 : sharpKernel 4 = 5 := by norm_num [sharpKernel]
  -- Point weights: `3` on the inner points, `5/3` on `k+1` and `n-k`, `1` elsewhere.
  set h : ℕ → ℝ := fun p =>
    if k + 1 < p ∧ p < n - k then 3 else if p = k + 1 ∨ p = n - k then 5 / 3 else 1
  have h_mid : ∀ p, k + 1 < p → p < n - k → h p = 3 := fun p h1 h2 => by
    simp only [h, h1, h2, and_self, ↓reduceIte]
  have h_end : ∀ p, p = k + 1 ∨ p = n - k → h p = 5 / 3 := fun p hp => by
    simp only [h]
    split_ifs <;> first | rfl | (exfalso; omega)
  have h_out : ∀ p, p ≤ k ∨ n - k < p → h p = 1 := fun p hp => by
    simp only [h]
    split_ifs <;> first | rfl | (exfalso; omega)
  have h_nonneg : ∀ p, 0 ≤ h p := fun p => by
    simp only [h]
    split_ifs <;> norm_num
  -- Every edge of `M` is at least the product of the weights of its endpoints.
  have hedge : ∀ e ∈ M, h e.1 * h e.2 ≤ sharpKernel (x e.2 - x e.1) := by
    rintro ⟨a, b⟩ he
    obtain ⟨ha, hb, hab⟩ := PerfectMatching.edge hM he
    simp only [mem_Icc] at ha hb
    dsimp only at hab ⊢
    by_cases hL : a ≤ k
    · -- An edge at an outer left point is the rainbow pair `(a, n + 1 - a)`.
      have heq : (a, b) = (a, n + 1 - a) := PerfectMatching.eq_of_mem hM (mem_Icc.2 ha) he
        (hout a (mem_Icc.2 ⟨ha.1, hL⟩)) (Or.inl rfl) (Or.inl rfl)
      have hb' : b = n + 1 - a := congrArg Prod.snd heq
      rw [h_out a (Or.inl hL), h_out b (Or.inr (by omega)), one_mul]
      exact one_le_sharpKernel _
    by_cases hR : n - k < b
    · -- An edge at an outer right point is the rainbow pair `(n + 1 - b, b)`.
      have heq : (a, b) = (n + 1 - b, n + 1 - (n + 1 - b)) := PerfectMatching.eq_of_mem hM
        (mem_Icc.2 hb) he (hout (n + 1 - b) (mem_Icc.2 ⟨by omega, by omega⟩)) (Or.inr rfl)
        (Or.inr (by omega))
      have ha' : a = n + 1 - b := congrArg Prod.fst heq
      rw [h_out a (Or.inl (by omega)), h_out b (Or.inr hR), one_mul]
      exact one_le_sharpKernel _
    -- Otherwise `k + 1 ≤ a < b ≤ n - k`, and `(a, b) ≠ (k + 1, n - k)`.
    rcases (show a = k + 1 ∨ k + 1 < a by omega) with rfl | ha1
    · have hb1 : b ≠ n - k := fun hb1 => hdep (hb1 ▸ he)
      rw [h_end _ (Or.inl rfl), h_mid b (by omega) (by omega), hx_L,
        hx_mid b (by omega) (by omega)]
      norm_num [hf4]
    · rcases (show b < n - k ∨ b = n - k by omega) with hb1 | rfl
      · rw [h_mid a ha1 (by omega), h_mid b (by omega) hb1, hx_mid a ha1 (by omega),
          hx_mid b (by omega) hb1]
        norm_num [hf0]
      · rw [h_mid a ha1 (by omega), h_end _ (Or.inr rfl), hx_mid a ha1 (by omega), hx_R]
        norm_num [hf4]
  -- So `∏_M f ≥ ∏_M h(a) h(b) = ∏_{p ∈ [n]} h(p) = 3^(n-2k-2) (5/3)^2`.
  have hprod : ∏ p ∈ Icc 1 n, h p = 3 ^ (n - 2 * k - 2) * (5 / 3) ^ 2 := by
    simp only [h]
    rw [prod_ite, prod_const, prod_ite, prod_const, prod_const_one, mul_one]
    have hc1 : #{p ∈ Icc 1 n | k + 1 < p ∧ p < n - k} = n - 2 * k - 2 := by
      rw [show {p ∈ Icc 1 n | k + 1 < p ∧ p < n - k} = Ioo (k + 1) (n - k) by
        ext p; simp only [mem_filter, mem_Icc, mem_Ioo]; omega, Nat.card_Ioo]
      omega
    have hc2 : #{p ∈ {p ∈ Icc 1 n | ¬(k + 1 < p ∧ p < n - k)} | p = k + 1 ∨ p = n - k} = 2 := by
      rw [show {p ∈ {p ∈ Icc 1 n | ¬(k + 1 < p ∧ p < n - k)} | p = k + 1 ∨ p = n - k} =
          {k + 1, n - k} by
        ext p; simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]; omega,
        card_pair (by omega)]
    rw [hc1, hc2]
  calc 25 / 9 * 9 ^ (n / 2 - k - 1)
      = ∏ p ∈ Icc 1 n, h p := by
        rw [hprod, show n - 2 * k - 2 = 2 * (n / 2 - k - 1) by omega, pow_mul]
        norm_num
        ring
    _ = ∏ e ∈ M, (h e.1 * h e.2) := PerfectMatching.prod_eq hM h
    _ ≤ ∏ e ∈ M, sharpKernel (x e.2 - x e.1) :=
        prod_le_prod₀ (fun e _ => mul_nonneg (h_nonneg _) (h_nonneg _)) hedge

/-! ### Only the rainbow survives -/

/-- **Only the rainbow survives.** For even `n` and every perfect matching `M` of `[n]` other than
the rainbow, there are `f`, positive, nonincreasing and convex on `(0, ∞)`, and
`x_1 < ⋯ < x_n` with `Pf A_f(x) < ∏_{(a,b) ∈ M} f(x_b - x_a)`. -/
theorem exists_pfaffian_lt_prod_of_ne_rainbow (n : ℕ) (hn : Even n) (M : Finset (ℕ × ℕ))
    (hM : M ∈ perfectMatchings (Icc 1 n)) (hMr : M ≠ rainbow n) :
    ∃ f : ℝ → ℝ, (∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t) ∧ AntitoneOn f (Set.Ioi 0) ∧
      ConvexOn ℝ (Set.Ioi 0) f ∧
      ∃ x : ℕ → ℝ, StrictMonoOn x (Set.Icc 1 n) ∧
        pfaffian (Icc 1 n) (kernel f x) < ∏ e ∈ M, f (x e.2 - x e.1) := by
  -- `M` first departs from the rainbow at `(k + 1, n - k)`.
  obtain ⟨k, hk, hout, hdep⟩ := exists_first_departure hM hMr
  -- `G(ε) = ∏_M f - Pf`, for the points `sharpPoints n k ε`.
  set G : ℝ → ℝ := fun ε =>
    ∏ e ∈ M, sharpKernel (sharpPoints n k ε e.2 - sharpPoints n k ε e.1) -
      pfaffian (Icc 1 n) (kernel sharpKernel (sharpPoints n k ε))
  -- At `ε = 0`: `G(0) ≥ (25/9 - 1) 9^(n/2 - k - 1) > 0`.
  have hG0 : 0 < G 0 := by
    have h1 := pfaffian_sharp_zero hn hk
    have h2 := prod_sharp_zero hn hk hM hout hdep
    have h3 : (0 : ℝ) < 9 ^ (n / 2 - k - 1) := by positivity
    simp only [G, h1]
    linarith
  -- `G` is continuous: every point depends continuously on `ε`, and so do `f`, the product
  -- and the Pfaffian.
  have hx : ∀ i, Continuous fun ε => sharpPoints n k ε i := fun i => by
    by_cases h1 : i ≤ k + 1
    · simp only [sharpPoints, h1, ↓reduceIte]
      exact continuous_const
    · by_cases h2 : n - k ≤ i
      · simp only [sharpPoints, h1, h2, ↓reduceIte]
        exact continuous_const
      · simp only [sharpPoints, h1, h2, ↓reduceIte]
        exact continuous_id.mul continuous_const
  have hG : Continuous G :=
    (continuous_finsetProd _ fun e _ => continuous_sharpKernel.comp ((hx _).sub (hx _))).sub
      (continuous_pfaffian _ fun i j => continuous_sharpKernel.comp ((hx j).sub (hx i)))
  -- So `G(ε) > 0` and `ε n < 4` for all small `ε`; pick one with `ε > 0`.
  have hev : ∀ᶠ ε in nhds (0 : ℝ), 0 < G ε ∧ ε * n < 4 :=
    (hG.continuousAt.eventually (lt_mem_nhds hG0)).and
      ((continuous_id.mul continuous_const).continuousAt.eventually_lt continuousAt_const
        (by simp))
  obtain ⟨ε, ⟨hGε, hεn⟩, hε⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi 0))).exists
  -- `f = max(9 - r, 1)` and `x = sharpPoints n k ε` work.
  refine ⟨sharpKernel, sharpKernel_pos, sharpKernel_antitoneOn, sharpKernel_convexOn,
    sharpPoints n k ε, sharpPoints_strictMonoOn hε hεn, ?_⟩
  simp only [G] at hGε
  linarith
