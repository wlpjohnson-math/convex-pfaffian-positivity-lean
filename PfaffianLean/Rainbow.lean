import PfaffianLean.LowerBounds

/-!
# The rainbow bound

* Outer-pair bound: for even `n ≥ 2` and `K ∈ 𝒜_n`, `Pf(K) ≥ K(1, n) · Pf(K_{[2, n-1]})`.
* Additive rainbow bound: for even `n` and `K ∈ 𝒜_n`,
  `Pf(K) ≥ ∏_{k=1}^{n/2} K(k, n+1-k) ≥ K(1, n)^(n/2)`.
* Convex rainbow bound: for `f` positive, nonincreasing and convex on `(0, ∞)`, even `n` and
  `x_1 < ⋯ < x_n`, `Pf A_f(x) ≥ ∏_{k=1}^{n/2} f(x_{n+1-k} - x_k) > 0`.

The outer-pair bound goes through the first-row expansion. For a family `K` on `[n]`, let
`L = K_{[2,n]}`, read on `[n - 1]` (`K.submatrix (· + 1) (· + 1)`). The partial first-row sums
`T_m = ∑_{j=2}^{m} (-1)^j K(1, j) Pf([n] \ {1, j})` are rewritten by Abel summation in terms of
the prefix sums `Z_q(L)` of the bordered-Pfaffian cofactors of `L`, which are `≥ 0` on `𝒜_{n-1}`.
The prefix sums are shown `≥ 0` with a one-border family: a new first point whose row is a step.
The rainbow bound then follows by peeling outer pairs, using that `𝒜_n` is closed under deleting
the first or the last point.
-/

open Finset

/-! ### Restriction -/

/-- Below the padding column, the padded families on `[n]` and `[n + 1]` agree. -/
theorem pad_succ_of_le {n : ℕ} (K : Matrix ℕ ℕ ℝ) (i : ℕ) {j : ℕ} (hj : j ≤ n) :
    pad (n + 1) K i j = pad n K i j := by
  have h1 : j ≠ n + 1 + 1 := by omega
  have h2 : j ≠ n + 1 := by omega
  simp [pad, h1, h2]

/-- Away from row `0`, the padded family of `K_{[2, n+1]}` (read on `[n]`) is the padded family
of `K` on `[n + 1]`, shifted by one. -/
theorem pad_submatrix_succ {n : ℕ} (K : Matrix ℕ ℕ ℝ) {i : ℕ} (hi : i ≠ 0) (j : ℕ) :
    pad n (K.submatrix (· + 1) (· + 1)) i j = pad (n + 1) K (i + 1) (j + 1) := by
  simp [pad, hi]

/-- Deleting the last point keeps a family additive: `K ∈ 𝒜_{n+1}` implies `K ∈ 𝒜_n`. -/
theorem mem_additiveClass_of_succ {n : ℕ} {K : Matrix ℕ ℕ ℝ} (hK : K ∈ additiveClass (n + 1)) :
    K ∈ additiveClass n := by
  rintro ⟨p, r⟩ hJ
  simp only [intervals, mem_filter, mem_product, mem_Icc] at hJ
  have hmem : ∀ r', p < r' → r' ≤ n + 1 → (p, r') ∈ intervals (n + 1) := fun r' h1 h2 => by
    simp only [intervals, mem_filter, mem_product, mem_Icc]
    omega
  rcases (show r < n ∨ r = n by omega) with hr | hr
  · -- For `r < n`, the mixed difference `α_[p,r]` is the same on `[n]` and on `[n + 1]`.
    have h := hK _ (hmem r (by omega) (by omega))
    simp only [alpha] at h ⊢
    rwa [pad_succ_of_le K _ hr.le, pad_succ_of_le K _ hr.le, pad_succ_of_le K _ (by omega),
      pad_succ_of_le K _ (by omega)] at h
  · -- For `r = n`, `α_[p,n]` on `[n]` is `α_[p,n] + α_[p,n+1]` on `[n + 1]`.
    rw [hr]
    have h1 := hK _ (hmem n (by omega) (by omega))
    have h2 := hK _ (hmem (n + 1) (by omega) le_rfl)
    simp only [alpha, pad_succ_right] at h1 h2 ⊢
    rw [pad_succ_of_le K _ le_rfl, pad_succ_of_le K _ le_rfl] at h1
    linarith

/-- Deleting the first point keeps a family additive: if `K ∈ 𝒜_{n+1}`, then `K_{[2, n+1]}`,
read on `[n]`, is in `𝒜_n`. -/
theorem submatrix_succ_mem_additiveClass {n : ℕ} {K : Matrix ℕ ℕ ℝ}
    (hK : K ∈ additiveClass (n + 1)) :
    K.submatrix (· + 1) (· + 1) ∈ additiveClass n := by
  rintro ⟨p, r⟩ hJ
  simp only [intervals, mem_filter, mem_product, mem_Icc] at hJ
  have hmem : ∀ p' r', 1 ≤ p' → p' < r' → r' ≤ n + 1 → (p', r') ∈ intervals (n + 1) :=
    fun p' r' h0 h1 h2 => by
      simp only [intervals, mem_filter, mem_product, mem_Icc]
      omega
  rcases (show p = 1 ∨ 2 ≤ p by omega) with rfl | hp
  · -- For `p = 1`, `α_[1,r]` of the restriction is `α_[1,r+1] + α_[2,r+1]` of `K`.
    have h1 := hK _ (hmem 1 (r + 1) le_rfl (by omega) (by omega))
    have h2 := hK _ (hmem 2 (r + 1) (by omega) (by omega) (by omega))
    simp only [alpha, Nat.sub_self, pad_zero_left, pad_submatrix_succ K one_ne_zero] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    linarith
  · -- For `p ≥ 2`, `α_[p,r]` of the restriction is `α_[p+1,r+1]` of `K`.
    have h := hK _ (hmem (p + 1) (r + 1) (by omega) (by omega) (by omega))
    simp only [alpha] at h ⊢
    rw [pad_submatrix_succ K (by omega), pad_submatrix_succ K (by omega),
      pad_submatrix_succ K (by omega), pad_submatrix_succ K (by omega),
      Nat.sub_add_cancel (by omega : 1 ≤ p)]
    simpa only [Nat.add_sub_cancel] using h

/-- Shifting the index set by one: `Pf(A_{[a+1, b+1]}) = Pf(A'_{[a, b]})`, with
`A'(i, j) = A(i + 1, j + 1)`. -/
theorem pfaffian_Icc_succ {R : Type*} [CommRing R] (a b : ℕ) (A : Matrix ℕ ℕ R) :
    pfaffian (Icc (a + 1) (b + 1)) A = pfaffian (Icc a b) (A.submatrix (· + 1) (· + 1)) := by
  rw [← image_add_right_Icc]
  exact pfaffian_image_strictMono (fun _ _ h => Nat.succ_lt_succ h) _ _

/-- Deleting `1` and `j` from `[n]`: `Pf([n] \ {1, j})` of `A` is `Pf([n - 1] \ {j - 1})` of
`A_{[2, n]}`, read on `[n - 1]`. -/
theorem pfaffian_Icc_two_sdiff {R : Type*} [CommRing R] {n j : ℕ} (hj2 : 2 ≤ j) (hjn : j ≤ n)
    (A : Matrix ℕ ℕ R) :
    pfaffian (Icc 2 n \ {j}) A =
      pfaffian (Icc 1 (n - 1) \ {j - 1}) (A.submatrix (· + 1) (· + 1)) := by
  have himg : Icc 2 n \ {j} = (Icc 1 (n - 1) \ {j - 1}).image (· + 1) := by
    ext x
    simp only [mem_sdiff, mem_Icc, mem_singleton, mem_image]
    constructor
    · intro hx
      exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩
      omega
  rw [himg]
  exact pfaffian_image_strictMono (fun _ _ h => Nat.succ_lt_succ h) _ _

/-- First-row expansion on `[n]`, `n ≥ 1`:
`Pf(A) = ∑_{j=2}^{n} (-1)^j A(1, j) Pf([n] \ {1, j})`. -/
theorem pfaffian_Icc_one_eq_sum {R : Type*} [CommRing R] {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix ℕ ℕ R) :
    pfaffian (Icc 1 n) A = ∑ j ∈ Icc 2 n, (-1) ^ j * A 1 j * pfaffian (Icc 2 n \ {j}) A := by
  have hins : Icc 1 n = insert 1 (Icc 2 n) := by
    ext x
    simp only [mem_insert, mem_Icc]
    omega
  rw [hins, pfaffian_insert_of_forall_lt (fun x hx => by simp only [mem_Icc] at hx; omega)]
  refine sum_congr rfl fun j hj => ?_
  simp only [mem_Icc] at hj
  -- The number of points of `[2, n]` below `j` is `j - 2`, and `(-1)^(j-2) = (-1)^j`.
  have hcard : #{x ∈ Icc 2 n | x < j} = j - 2 := by
    rw [show {x ∈ Icc 2 n | x < j} = Ico 2 j by
      ext x; simp only [mem_filter, mem_Icc, mem_Ico]; omega, Nat.card_Ico]
  rw [hcard, sdiff_singleton_eq_erase]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  simp [pow_add]

/-! ### Prefix sums of the bordered-Pfaffian cofactors -/

/-- The prefix sum `Z_q(L) = c'_1(L) + ⋯ + c'_{q-1}(L)` of the bordered-Pfaffian cofactors
`c'_t(L) = (-1)^(t+1) Pf(L_{[N] \ {t}})` of a family `L` on `[N]`. -/
def prefixSum (N : ℕ) (L : Matrix ℕ ℕ ℝ) (q : ℕ) : ℝ :=
  ∑ t ∈ Ico 1 q, (-1) ^ (t + 1) * pfaffian (Icc 1 N \ {t}) L

/-- The one-border family of `L` at `q` with height `h`, a family on `[N + 1]` when `L` is on
`[N]`: a new first point is added and the points of `L` move up by one. The new point is joined
to each `j ≤ q` with weight `h` and to each `j > q` with weight `0` (a step row), and `h` is added
to every entry of `L` between two points of `[1, q - 1]` (old numbering). -/
def oneBorder (L : Matrix ℕ ℕ ℝ) (q : ℕ) (h : ℝ) : Matrix ℕ ℕ ℝ :=
  Matrix.of fun i j => (if i = 1 then 0 else L (i - 1) (j - 1)) + if j ≤ q then h else 0

/-- **One-border identity.** The Pfaffian of the one-border family is `h · Z_q` of `L` with `h`
added on `[1, q - 1]`. -/
theorem pfaffian_oneBorder (N : ℕ) (L : Matrix ℕ ℕ ℝ) {q : ℕ} (hq : q ≤ N + 1) (h : ℝ) :
    pfaffian (Icc 1 (N + 1)) (oneBorder L q h) =
      h * prefixSum N (Matrix.of fun i j => L i j + if j < q then h else 0) q := by
  set L' : Matrix ℕ ℕ ℝ := Matrix.of fun i j => L i j + if j < q then h else 0
  -- First-row expansion, reindexed by `j = t + 1`:
  -- `Pf = ∑_{t=1}^{N} (-1)^(t+1) B(1, t+1) Pf([N+1] \ {1, t+1})`.
  have hre : ∀ g : ℕ → ℝ, ∑ j ∈ Icc 2 (N + 1), g j = ∑ t ∈ Icc 1 N, g (t + 1) := fun g => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, ← image_add_right_Icc, sum_image fun a _ b _ hab => by omega]
  rw [pfaffian_Icc_one_eq_sum (by omega), hre]
  -- The prefix sum over `t < q` is the sum over `[N]` of the terms with `t < q`.
  rw [prefixSum, mul_sum,
    show Ico 1 q = {t ∈ Icc 1 N | t < q} by ext t; simp only [mem_Ico, mem_filter, mem_Icc]; omega,
    sum_filter]
  refine sum_congr rfl fun t ht => ?_
  simp only [mem_Icc] at ht
  -- Deleting `1` and `t + 1` from `[N + 1]` leaves `[N] \ {t}` shifted by one, where the
  -- one-border family reads `L'`.
  rw [pfaffian_Icc_two_sdiff (by omega) (by omega), Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hcongr : pfaffian (Icc 1 N \ {t}) ((oneBorder L q h).submatrix (· + 1) (· + 1)) =
      pfaffian (Icc 1 N \ {t}) L' := by
    refine pfaffian_congr fun a ha b _ _ => ?_
    simp only [mem_sdiff, mem_Icc] at ha
    have ha1 : a + 1 ≠ 1 := by omega
    simp only [oneBorder, L', Matrix.submatrix_apply, Matrix.of_apply, ha1, ite_false,
      Nat.add_sub_cancel, Nat.add_one_le_iff]
  rw [hcongr]
  -- The new row is the step `B(1, t+1) = h [t + 1 ≤ q]`.
  simp only [oneBorder, Matrix.of_apply, ite_true, zero_add, Nat.add_one_le_iff]
  split_ifs <;> ring

/-- **One-border additivity.** For `L ∈ 𝒜_N`, every `q` and `h ≥ 0`, the one-border family is in
`𝒜_{N+1}`. -/
theorem oneBorder_mem_additiveClass {N : ℕ} {L : Matrix ℕ ℕ ℝ} (hL : L ∈ additiveClass N)
    (q : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    oneBorder L q h ∈ additiveClass (N + 1) := by
  -- Away from row `0`, the padded one-border family is the padded `L`, shifted by one, plus the
  -- step `h [j ≤ q]` (cut off at the padding column `N + 2`).
  have hpad : ∀ i j, 1 ≤ i → 1 ≤ j → pad (N + 1) (oneBorder L q h) i j =
      pad N L (i - 1) (j - 1) + if j = N + 1 + 1 then 0 else if j ≤ q then h else 0 := by
    intro i j hi hj
    have hj' : j - 1 = N + 1 ↔ j = N + 1 + 1 := by omega
    by_cases hi1 : i = 1
    · subst hi1
      by_cases hjN : j = N + 1 + 1 <;> simp [pad, oneBorder, hjN]
    · have hi0 : i ≠ 0 := by omega
      have hi0' : i - 1 ≠ 0 := by omega
      by_cases hjN : j = N + 1 + 1
      · simp [pad, hjN]
      · simp [pad, oneBorder, hi0, hi0', hi1, hjN, hj']
  rintro ⟨p, r⟩ hJ
  simp only [intervals, mem_filter, mem_product, mem_Icc] at hJ
  obtain ⟨⟨⟨hp1, -⟩, -, hrN⟩, hpr⟩ := hJ
  simp only [alpha]
  rcases (show p = 1 ∨ 2 ≤ p by omega) with rfl | hp2
  · -- `p = 1`: `α_[1,r] = h [r ≤ q] - h [r + 1 ≤ q] ≥ 0` (the step).
    rw [Nat.sub_self, pad_zero_left, pad_zero_left, hpad 1 r le_rfl (by omega),
      hpad 1 (r + 1) le_rfl (by omega)]
    simp only [Nat.sub_self, pad_zero_left, zero_add]
    split_ifs <;> first | omega | linarith
  · -- `p ≥ 2`: the steps cancel and `α_[p,r] = α_[p-1,r-1](L) ≥ 0`.
    have hα := hL (p - 1, r - 1) (by
      simp only [intervals, mem_filter, mem_product, mem_Icc]
      omega)
    simp only [alpha] at hα
    rw [hpad p r (by omega) (by omega), hpad (p - 1) r (by omega) (by omega),
      hpad p (r + 1) (by omega) (by omega), hpad (p - 1) (r + 1) (by omega) (by omega),
      Nat.add_sub_cancel]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at hα
    linarith

/-- **Prefix sums are nonnegative.** For odd `N`, `L ∈ 𝒜_N` and `q ≤ N + 1`: `Z_q(L) ≥ 0`. -/
theorem prefixSum_nonneg {N : ℕ} (hN : Odd N) {L : Matrix ℕ ℕ ℝ} (hL : L ∈ additiveClass N)
    {q : ℕ} (hq : q ≤ N + 1) : 0 ≤ prefixSum N L q := by
  -- Write `g(h) = Z_q(L + h [j < q])`.
  set M : ℝ → Matrix ℕ ℕ ℝ := fun h => Matrix.of fun i j => L i j + if j < q then h else 0
  set g : ℝ → ℝ := fun h => prefixSum N (M h) q
  -- For `h > 0`: `h · g(h) = Pf(oneBorder L q h) ≥ 0`, since the one-border family is additive
  -- on the even set `[N + 1]` (Additive lower bound).
  have hpos : ∀ h > 0, 0 ≤ g h := by
    intro h hh
    have hB := oneBorder_mem_additiveClass hL q hh.le
    obtain ⟨hpf, hge, hnn⟩ :=
      additive_lower_bound (N + 1) hN.add_one (by obtain ⟨k, rfl⟩ := hN; omega) _ hB
    have hPf : 0 ≤ pfaffian (Icc 1 (N + 1)) (oneBorder L q h) := by
      rw [hpf]
      linarith
    rw [pfaffian_oneBorder N L hq h] at hPf
    exact (mul_nonneg_iff_of_pos_left hh).1 hPf
  -- `g` is a polynomial in `h`, hence continuous, and `g(0) = Z_q(L)`.
  have hcont : Continuous g := by
    have hentry : ∀ i j, Continuous fun h => M h i j := fun i j =>
      continuous_const.add
        (continuous_if_const _ (fun _ => continuous_id) fun _ => continuous_const)
    refine continuous_finsetSum _ fun t _ => continuous_const.mul ?_
    exact continuous_finsetSum _ fun P _ =>
      continuous_const.mul (continuous_finsetProd _ fun e _ => hentry _ _)
  have hg0 : g 0 = prefixSum N L q := by
    simp only [g, M, ite_self, add_zero]
    rfl
  -- Let `h → 0⁺`.
  rw [← hg0]
  exact ge_of_tendsto (x := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun h hh => hpos h hh)

/-! ### The outer-pair bound -/

/-- **Abel summation for `T_m`.** For a family `K` on `[n]` and `2 ≤ m ≤ n`, with
`L = K_{[2, n]}` read on `[n - 1]`:
`T_m = ∑_{q=2}^{m-1} α_[1,q](K) Z_q(L) + K(1, m) Z_m(L)`. -/
theorem firstRowPartial_eq_abel (n : ℕ) (K : Matrix ℕ ℕ ℝ) {m : ℕ} (hm2 : 2 ≤ m)
    (hmn : m ≤ n) :
    ∑ j ∈ Icc 2 m, (-1) ^ j * K 1 j * pfaffian (Icc 2 n \ {j}) K =
      ∑ q ∈ Ico 2 m, alpha n K (1, q) * prefixSum (n - 1) (K.submatrix (· + 1) (· + 1)) q +
        K 1 m * prefixSum (n - 1) (K.submatrix (· + 1) (· + 1)) m := by
  set Z := prefixSum (n - 1) (K.submatrix (· + 1) (· + 1))
  -- `(-1)^j Pf([n] \ {1, j}) = c'_{j-1}(L) = Z_j - Z_{j-1}`.
  have hc : ∀ t, 1 ≤ t → t + 1 ≤ n →
      (-1) ^ (t + 1) * pfaffian (Icc 2 n \ {t + 1}) K = Z (t + 1) - Z t := by
    intro t ht1 htn
    simp only [Z, prefixSum]
    rw [sum_Ico_succ_top ht1, add_sub_cancel_left, pfaffian_Icc_two_sdiff (by omega) htn,
      Nat.add_sub_cancel]
  have hZ1 : Z 1 = 0 := by simp [Z, prefixSum]
  -- Induction on `m`: each step is one step of Abel summation, with
  -- `α_[1,m] = K(1,m) - K(1,m+1)` for `m < n`.
  revert hmn
  induction m, hm2 using Nat.le_induction with
  | base =>
    intro hmn
    have h2 := hc 1 le_rfl hmn
    rw [hZ1, sub_zero] at h2
    rw [Icc_self, sum_singleton, Ico_self, sum_empty, zero_add]
    linear_combination K 1 2 * h2
  | succ m hm ih =>
    intro hmn
    have hα : alpha n K (1, m) = K 1 m - K 1 (m + 1) := by
      simp only [alpha, Nat.sub_self, pad_zero_left, sub_zero, add_zero]
      rw [pad_of_ne n K one_ne_zero (by omega), pad_of_ne n K one_ne_zero (by omega)]
    rw [sum_Icc_succ_top (by omega), ih (by omega), sum_Ico_succ_top hm, hα]
    linear_combination K 1 (m + 1) * hc m (by omega) hmn

/-- **`T_{n-1}`.** For even `n ≥ 2`: `T_{n-1} = Pf(K) - K(1, n) Pf(K_{[2, n-1]})`. -/
theorem firstRowPartial_eq_sub (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) (K : Matrix ℕ ℕ ℝ) :
    ∑ j ∈ Icc 2 (n - 1), (-1) ^ j * K 1 j * pfaffian (Icc 2 n \ {j}) K =
      pfaffian (Icc 1 n) K - K 1 n * pfaffian (Icc 2 (n - 1)) K := by
  -- By the first-row expansion `Pf(K) = T_n`, and `T_n = T_{n-1} + (-1)^n K(1,n) Pf([2, n-1])`.
  have hsd : Icc 2 n \ {n} = Icc 2 (n - 1) := by
    ext x
    simp only [mem_sdiff, mem_Icc, mem_singleton]
    omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [pfaffian_Icc_one_eq_sum (by omega), sum_Icc_succ_top (by omega), hsd,
    (show Even (k + 1) from hn).neg_one_pow, Nat.add_sub_cancel]
  ring

/-- **Outer-pair bound.** For even `n ≥ 2` and `K ∈ 𝒜_n`: `Pf(K) ≥ K(1, n) · Pf(K_{[2, n-1]})`. -/
theorem outer_pair_bound (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K ≥ K 1 n * pfaffian (Icc 2 (n - 1)) K := by
  -- `Pf(K) - K(1,n) Pf(K_{[2,n-1]}) = T_{n-1}`; it suffices to show `T_{n-1} ≥ 0`.
  have hT := firstRowPartial_eq_sub n hn h2 K
  suffices 0 ≤ ∑ j ∈ Icc 2 (n - 1), (-1) ^ j * K 1 j * pfaffian (Icc 2 n \ {j}) K by linarith
  -- For `n = 2`, `T_1` is the empty sum.
  rcases (show n = 2 ∨ 4 ≤ n by obtain ⟨k, rfl⟩ := hn; omega) with rfl | h4
  · simp
  -- For `n ≥ 4`: `T_{n-1} = ∑_{q=2}^{n-2} α_[1,q](K) Z_q(L) + K(1, n-1) Z_{n-1}(L)` with
  -- `L = K_{[2,n]} ∈ 𝒜_{n-1}`, and every factor is `≥ 0`.
  rw [firstRowPartial_eq_abel n K (by omega : 2 ≤ n - 1) (by omega)]
  have hL : K.submatrix (· + 1) (· + 1) ∈ additiveClass (n - 1) :=
    submatrix_succ_mem_additiveClass (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)])
  have hodd : Odd (n - 1) := by
    obtain ⟨k, rfl⟩ := hn
    exact ⟨k - 1, by omega⟩
  -- `Z_q(L) ≥ 0` (prefix sums are nonnegative).
  have hZ : ∀ q, q ≤ n - 1 → 0 ≤ prefixSum (n - 1) (K.submatrix (· + 1) (· + 1)) q :=
    fun q hq => prefixSum_nonneg hodd hL (by omega)
  -- `α_[1,q](K) ≥ 0` (`K ∈ 𝒜_n`).
  have hα : ∀ q ∈ Ico 2 (n - 1), 0 ≤ alpha n K (1, q) := fun q hq => by
    simp only [mem_Ico] at hq
    exact hK (1, q) (by simp only [intervals, mem_filter, mem_product, mem_Icc]; omega)
  -- `K(1, n-1) = ∑_{J ∋ 1, n-1} α_J(K) ≥ 0` (Interval decomposition).
  have hK1 : 0 ≤ K 1 (n - 1) := by
    rw [interval_decomposition n K le_rfl (by omega : 1 < n - 1) (by omega)]
    exact sum_nonneg fun J hJ => hK J (mem_filter.1 hJ).1
  refine add_nonneg (sum_nonneg fun q hq => mul_nonneg (hα q hq) (hZ q ?_))
    (mul_nonneg hK1 (hZ _ le_rfl))
  simp only [mem_Ico] at hq
  omega

/-! ### The rainbow bound -/

/-- On `𝒜_n`, every entry `K(i, j)`, `1 ≤ i < j ≤ n`, is at least the corner `K(1, n)`: both are
sums of mixed differences `α_J ≥ 0`, and `[1, n]` contains `i` and `j`. -/
theorem corner_le_of_mem_additiveClass {n : ℕ} {K : Matrix ℕ ℕ ℝ} (hK : K ∈ additiveClass n)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n) : K 1 n ≤ K i j := by
  rw [interval_decomposition n K hi hij hj, ← interval_decomposition_corner n K]
  refine single_le_sum (f := fun J => alpha n K J) (fun J hJ => hK J (mem_filter.1 hJ).1) ?_
  simp only [mem_filter, intervals, mem_product, mem_Icc]
  omega

/-- On `𝒜_n`, `n ≥ 2`, the corner `K(1, n) = α_[1,n](K)` is `≥ 0`. -/
theorem corner_nonneg_of_mem_additiveClass {n : ℕ} {K : Matrix ℕ ℕ ℝ}
    (hK : K ∈ additiveClass n) (h2 : 2 ≤ n) : 0 ≤ K 1 n := by
  rw [← interval_decomposition_corner n K]
  exact hK _ (corner_mem_intervals h2)

/-- Peeling the first factor of a product over `[1, m + 1]`. -/
theorem prod_Icc_one_succ (m : ℕ) (g : ℕ → ℝ) :
    ∏ k ∈ Icc 1 (m + 1), g k = g 1 * ∏ k ∈ Icc 1 m, g (k + 1) := by
  rw [show Icc 1 (m + 1) = insert 1 ((Icc 1 m).image (· + 1)) by
      rw [image_add_right_Icc]; ext x; simp only [mem_insert, mem_Icc]; omega,
    prod_insert (by simp), prod_image fun a _ b _ hab => by omega]

/-- **Additive rainbow bound.** For even `n` and `K ∈ 𝒜_n`:
`Pf(K) ≥ ∏_{k=1}^{n/2} K(k, n+1-k) ≥ K(1, n)^(n/2)`. -/
theorem additive_rainbow_bound (n : ℕ) (hn : Even n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K ≥ ∏ k ∈ Icc 1 (n / 2), K k (n + 1 - k) ∧
      ∏ k ∈ Icc 1 (n / 2), K k (n + 1 - k) ≥ K 1 n ^ (n / 2) := by
  obtain ⟨m, rfl⟩ := hn
  rw [show (m + m) / 2 = m by omega]
  refine ⟨?_, ?_⟩
  · -- Peel the outer pair: induction on `m`, with `K_{[2, 2m+1]}` read on `[2m]` at each step.
    induction m generalizing K with
    | zero => simp [pfaffian_empty]
    | succ m ih =>
      set n := m + 1 + (m + 1)
      -- `K_{[2, n-1]}`, read on `[2m]`, is in `𝒜_{2m}`.
      have hK' : K.submatrix (· + 1) (· + 1) ∈ additiveClass (m + m) :=
        submatrix_succ_mem_additiveClass (mem_additiveClass_of_succ (n := m + m + 1)
          (by rwa [show m + m + 1 + 1 = n by omega]))
      -- Outer-pair bound, then the induction hypothesis on the inner family (with `K(1,n) ≥ 0`).
      have hout := outer_pair_bound n ⟨m + 1, rfl⟩ (by omega) K hK
      rw [show Icc 2 (n - 1) = Icc (1 + 1) (m + m + 1) by congr 1; omega,
        pfaffian_Icc_succ] at hout
      have hc := corner_nonneg_of_mem_additiveClass hK (by omega : 2 ≤ n)
      have hprod : ∏ k ∈ Icc 1 (m + 1), K k (n + 1 - k) =
          K 1 n * ∏ k ∈ Icc 1 m, K.submatrix (· + 1) (· + 1) k (m + m + 1 - k) := by
        rw [prod_Icc_one_succ]
        congr 1
        refine prod_congr rfl fun k hk => ?_
        simp only [mem_Icc] at hk
        simp only [Matrix.submatrix_apply]
        congr 1
        omega
      rw [hprod]
      exact le_trans (mul_le_mul_of_nonneg_left (ih _ hK') hc) hout
  · -- Every factor is `K(k, n+1-k) ≥ K(1, n) ≥ 0`.
    calc K 1 (m + m) ^ m = ∏ _k ∈ Icc 1 m, K 1 (m + m) := by simp
      _ ≤ ∏ k ∈ Icc 1 m, K k (m + m + 1 - k) := by
        refine prod_le_prod₀ (fun k hk => ?_) fun k hk => ?_ <;> simp only [mem_Icc] at hk
        · exact corner_nonneg_of_mem_additiveClass hK (by omega)
        · exact corner_le_of_mem_additiveClass hK hk.1 (by omega) (by omega)

/-- **Convex rainbow bound.** For every positive, nonincreasing, convex `f` on `(0, ∞)`, every
even `n` and every `x_1 < ⋯ < x_n`: `Pf A_f(x) ≥ ∏_{k=1}^{n/2} f(x_{n+1-k} - x_k) > 0`. -/
theorem convex_rainbow_bound (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel f x) ≥ ∏ k ∈ Icc 1 (n / 2), f (x (n + 1 - k) - x k) ∧
      ∏ k ∈ Icc 1 (n / 2), f (x (n + 1 - k) - x k) > 0 := by
  -- `K_{f,x} ∈ 𝒜_n` (Additivity of convex kernels), and `K_{f,x}(k, n+1-k) = f(x_{n+1-k} - x_k)`.
  obtain ⟨hK, -⟩ := convex_kernel_additive f (fun t ht => (hpos t ht).le) hanti hconv n x hx
  refine ⟨(additive_rainbow_bound n hn (kernel f x) hK).1, prod_pos fun k hk => hpos _ ?_⟩
  -- Each factor is `f` at a positive gap: `k < n + 1 - k` for `k ≤ n/2`.
  simp only [mem_Icc] at hk
  exact sub_pos.2 (hx ⟨hk.1, by omega⟩ ⟨by omega, by omega⟩ (by omega))
