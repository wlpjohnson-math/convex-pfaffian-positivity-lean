import PfaffianLean.Pfaffian

/-!
# Families, mixed differences, the additive class and the interval model

A family of reals on `[n] = {1, …, n}` is a matrix `K : Matrix ℕ ℕ ℝ`, of which only the entries
`K i j` with `1 ≤ i < j ≤ n` matter: its Pfaffian is `pfaffian (Icc 1 n) K`, the Pfaffian of
its skew extension on `[n]` (`pfaffian_skewExtension`). Entries outside `[n]` are genuine entries
of the matrix, so the mixed differences `alpha n K` insert the padding convention `K(0, j) = 0`,
`K(i, n + 1) = 0` explicitly (`pad`) instead of reading them.

An interval `[p, q]` is written as the pair `(p, q)`. The polynomial `F_n` is
`intervalPfaffian n`, with one variable for each interval `J ∈ I_n` (the variable type is the
subtype of `intervals n`).
-/

open Finset MvPolynomial

/-- `I_n`: the intervals `[p, q]` with `1 ≤ p < q ≤ n`, written as pairs `(p, q)`. -/
def intervals (n : ℕ) : Finset (ℕ × ℕ) :=
  {J ∈ Icc 1 n ×ˢ Icc 1 n | J.1 < J.2}

/-- The family `K` with the padding convention `K(0, j) = 0` and `K(i, n + 1) = 0`;
all other entries are those of `K`. -/
def pad (n : ℕ) (K : Matrix ℕ ℕ ℝ) (i j : ℕ) : ℝ :=
  if i = 0 ∨ j = n + 1 then 0 else K i j

/-- The mixed difference `α_[p,q](K) = K(p,q) - K(p-1,q) - K(p,q+1) + K(p-1,q+1)`, read in the
padded family `pad n K`. For `(p, q) ∈ I_n` we have `p ≥ 1`, so `p - 1` is the true predecessor. -/
def alpha (n : ℕ) (K : Matrix ℕ ℕ ℝ) (J : ℕ × ℕ) : ℝ :=
  pad n K J.1 J.2 - pad n K (J.1 - 1) J.2 - pad n K J.1 (J.2 + 1) + pad n K (J.1 - 1) (J.2 + 1)

/-- The additive class `𝒜_n`: the families with `α_J(K) ≥ 0` for every `J ∈ I_n`. -/
def additiveClass (n : ℕ) : Set (Matrix ℕ ℕ ℝ) :=
  {K | ∀ J ∈ intervals n, 0 ≤ alpha n K J}

/-- The matrix of `F_n`: its `(i, j)` entry is the sum of the variables `a_J` over the intervals
`J ∈ I_n` containing `i` and `j`. -/
noncomputable def intervalMatrix (n : ℕ) : Matrix ℕ ℕ (MvPolynomial (intervals n) ℤ) :=
  Matrix.of fun i j => ∑ J : intervals n with i ∈ Icc J.1.1 J.1.2 ∧ j ∈ Icc J.1.1 J.1.2, X J

/-- `F_n(a)`: the Pfaffian on `[n]` of `intervalMatrix n`, a polynomial over `ℤ` in the variables
`a_J`, `J ∈ I_n`. For `n = 0` it is the empty Pfaffian `1`. -/
noncomputable def intervalPfaffian (n : ℕ) : MvPolynomial (intervals n) ℤ :=
  pfaffian (Icc 1 n) (intervalMatrix n)

/-- The kernel family `K_{f,x}(i, j) = f(x_j - x_i)`. -/
def kernel (f : ℝ → ℝ) (x : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  Matrix.of fun i j => f (x j - x i)

/-! ### The padding -/

@[simp] theorem pad_zero_left (n : ℕ) (K : Matrix ℕ ℕ ℝ) (j : ℕ) : pad n K 0 j = 0 := by
  simp [pad]

@[simp] theorem pad_succ_right (n : ℕ) (K : Matrix ℕ ℕ ℝ) (i : ℕ) : pad n K i (n + 1) = 0 := by
  simp [pad]

theorem pad_of_ne (n : ℕ) (K : Matrix ℕ ℕ ℝ) {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ n + 1) :
    pad n K i j = K i j := by
  simp [pad, hi, hj]
