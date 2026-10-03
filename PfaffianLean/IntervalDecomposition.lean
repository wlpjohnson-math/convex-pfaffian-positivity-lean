import PfaffianLean.Families

/-!
# The Interval decomposition lemma

Reference: `refs/pfaffian-convex.tex`, Section 3, Lemma (Interval decomposition).

For every family `K` on `[n]` and all `1 ≤ i < j ≤ n`,
`K(i, j) = ∑_{J ∈ I_n, J ∋ i, j} α_J(K)`. Hence `Pf(K) = F_n(α(K))` (via the evaluation lemma
`RingHom.map_pfaffian`), and `α_[1,n](K) = K(1, n)`.
-/

open Finset MvPolynomial

/-- **Interval decomposition.** `K(i, j)` is the sum of `α_J(K)` over the intervals `J ∈ I_n`
containing `i` and `j`. -/
theorem interval_decomposition (n : ℕ) (K : Matrix ℕ ℕ ℝ) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (hj : j ≤ n) :
    K i j = ∑ J ∈ intervals n with i ∈ Icc J.1 J.2 ∧ j ∈ Icc J.1 J.2, alpha n K J := by
  -- "For fixed `q` the sum over `p = 1, …, i` telescopes":
  -- `∑_{p=1}^{i} α_[p,q] = K(i, q) − K(i, q + 1)` (in the padded family, `K(0, ·) = 0`).
  have htel_p : ∀ m q, ∑ p ∈ Icc 1 m, alpha n K (p, q) = pad n K m q - pad n K m (q + 1) := by
    intro m q
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_Icc_succ_top (by omega), ih]
      simp only [alpha, Nat.add_sub_cancel]
      ring
  -- "Summing over `q = j, …, n` telescopes again, to `K(i, j) − K(i, n + 1) = K(i, j)`."
  have htel_q : ∑ q ∈ Icc j n, (pad n K i q - pad n K i (q + 1)) = K i j := by
    have hneg : ∑ q ∈ Icc j n, (pad n K i q - pad n K i (q + 1)) =
        -∑ q ∈ Icc j n, (pad n K i (q + 1) - pad n K i q) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun q _ => (neg_sub _ _).symm
    rw [hneg, sum_Icc_sub hj (fun q => pad n K i q), pad_succ_right,
      pad_of_ne n K (by omega) (by omega), zero_sub, neg_neg]
  -- "The pairs `(p, q)` involved satisfy `p ≤ i < j ≤ q`, so every `[p, q]` is in `I_n`, and
  -- `[p, q]` contains `i` and `j` iff `p ≤ i` and `q ≥ j`."
  have hpairs : ({J ∈ intervals n | i ∈ Icc J.1 J.2 ∧ j ∈ Icc J.1 J.2} : Finset (ℕ × ℕ)) =
      Icc 1 i ×ˢ Icc j n := by
    ext ⟨p, q⟩
    simp only [intervals, mem_filter, mem_product, mem_Icc]
    omega
  rw [hpairs, sum_product_right, sum_congr rfl fun q _ => htel_p i q, htel_q]

/-- **Interval decomposition**, Pfaffian form: `Pf(K) = F_n(α(K))`. -/
theorem interval_decomposition_pfaffian (n : ℕ) (K : Matrix ℕ ℕ ℝ) :
    pfaffian (Icc 1 n) K = aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) := by
  -- "Hence `A_K` is the matrix of Definition 2.2(c) at `a = α(K)`": the two agree on the
  -- entries `i < j` of `[n]`, which are the only entries the Pfaffian reads.
  have hentry : ∀ i ∈ Icc 1 n, ∀ j ∈ Icc 1 n, i < j →
      K i j = (intervalMatrix n).map (aeval fun J : intervals n => alpha n K J) i j := by
    intro i hi j hj hij
    rw [mem_Icc] at hi hj
    rw [interval_decomposition n K hi.1 hij hj.2, Matrix.map_apply, intervalMatrix,
      Matrix.of_apply, map_sum]
    simp only [aeval_X]
    rw [sum_filter, sum_filter]
    exact (sum_coe_sort (intervals n) fun J =>
      if i ∈ Icc J.1 J.2 ∧ j ∈ Icc J.1 J.2 then alpha n K J else 0).symm
  -- "`Pf(K) = F_n(α(K))`": the evaluation lemma for the ring hom `aeval α(K)`.
  have heval := RingHom.map_pfaffian (aeval fun J : intervals n => alpha n K J).toRingHom
    (Icc 1 n) (intervalMatrix n)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at heval
  rw [pfaffian_congr hentry, intervalPfaffian, heval]

/-- **Interval decomposition**, corner: `α_[1,n](K) = K(1, n)`. -/
theorem interval_decomposition_corner (n : ℕ) (K : Matrix ℕ ℕ ℝ) : alpha n K (1, n) = K 1 n := by
  -- "`α_[1,n] = K(1,n) − K(0,n) − K(1,n+1) + K(0,n+1) = K(1,n)`."
  simp [alpha, pad_of_ne n K one_ne_zero (Nat.succ_ne_self n).symm]
