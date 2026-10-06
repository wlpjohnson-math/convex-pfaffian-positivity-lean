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
  sorry

/-- **First departure from the rainbow.** A perfect matching `M ≠` rainbow contains the
rainbow pairs `(i, n + 1 - i)` for `i ≤ k` but not `(k + 1, n - k)`, for some `k < n / 2`. -/
theorem exists_first_departure {n : ℕ} {M : Finset (ℕ × ℕ)}
    (hM : M ∈ perfectMatchings (Icc 1 n)) (hMr : M ≠ rainbow n) :
    ∃ k, k + 1 ≤ n / 2 ∧ (∀ i ∈ Icc 1 k, (i, n + 1 - i) ∈ M) ∧ (k + 1, n - k) ∉ M := by
  sorry

/-! ### General facts -/

/-- A product over the points of `S` is the product over the edges of a perfect matching of `S`
of the products over their two endpoints. -/
theorem PerfectMatching.prod_eq {ι : Type*} [LinearOrder ι] {S : Finset ι}
    {M : Finset (ι × ι)} (hM : M ∈ perfectMatchings S) (h : ι → ℝ) :
    ∏ t ∈ S, h t = ∏ e ∈ M, (h e.1 * h e.2) := by
  sorry

/-- The Pfaffian is continuous in the entries. -/
theorem continuous_pfaffian {ι : Type*} [LinearOrder ι] {X : Type*} [TopologicalSpace X]
    (S : Finset ι) {A : X → Matrix ι ι ℝ} (hA : ∀ i j, Continuous fun x => A x i j) :
    Continuous fun x => pfaffian S (A x) := by
  sorry

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

theorem sharpKernel_pos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < sharpKernel t := by
  sorry

theorem sharpKernel_antitoneOn : AntitoneOn sharpKernel (Set.Ioi 0) := by
  sorry

theorem sharpKernel_convexOn : ConvexOn ℝ (Set.Ioi 0) sharpKernel := by
  sorry

/-- For `0 < ε` and `ε n < 4`, the points are strictly increasing on `[n]`. -/
theorem sharpPoints_strictMonoOn {n k : ℕ} (hk : k + 1 ≤ n / 2) {ε : ℝ} (hε : 0 < ε)
    (hεn : ε * n < 4) : StrictMonoOn (sharpPoints n k ε) (Set.Icc 1 n) := by
  sorry

/-- **The Pfaffian at `ε = 0`.** The inner points coincide; Twin rows peels them off in pairs
(`f(0) = 9`), and the remaining `2k + 2` points have all entries `f(≥ 8) = 1`. -/
theorem pfaffian_sharp_zero {n k : ℕ} (hn : Even n) (hk : k + 1 ≤ n / 2) :
    pfaffian (Icc 1 n) (kernel sharpKernel (sharpPoints n k 0)) = 9 ^ (n / 2 - k - 1) := by
  sorry

/-- **The product at `ε = 0`.** If `M` contains the rainbow pairs `(i, n + 1 - i)`, `i ≤ k`, but
not `(k + 1, n - k)`, its product is at least `(25/9) · 9^(n/2 - k - 1)`. -/
theorem prod_sharp_zero {n k : ℕ} (hn : Even n) (hk : k + 1 ≤ n / 2) {M : Finset (ℕ × ℕ)}
    (hM : M ∈ perfectMatchings (Icc 1 n)) (hout : ∀ i ∈ Icc 1 k, (i, n + 1 - i) ∈ M)
    (hdep : (k + 1, n - k) ∉ M) :
    25 / 9 * 9 ^ (n / 2 - k - 1) ≤
      ∏ e ∈ M, sharpKernel (sharpPoints n k 0 e.2 - sharpPoints n k 0 e.1) := by
  sorry

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
  sorry
