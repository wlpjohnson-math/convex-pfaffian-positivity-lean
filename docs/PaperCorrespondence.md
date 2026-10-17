# Correspondence with the paper

This document compares the Lean formalization with the manuscript *Pfaffian Positivity for Convex
Kernels and Optimal Matching Bounds* (W. Johnson), result by result. For the landing page, see the
[README](../README.md); for provenance, `Spec.lean` and the trusted base, see
[Auditing.md](Auditing.md).

- [How to read this document](#how-to-read-this-document)
- [Summary table](#summary-table)
- [Result-by-result notes](#result-by-result-notes)
- [Power kernels](#power-kernels)
- [Results in Lean that are not results of the paper](#results-in-lean-that-are-not-results-of-the-paper)
- [Conventions](#conventions)
- [Terminology](#terminology)

## How to read this document

Each manuscript result is identified by its name, its LaTeX label, and its number in the current
draft (`convex_pfaffian_positivity.tex`, October 2026). Numbers may change; names and labels are
more stable.

Status:

- **Formalized**: a Lean theorem implies the paper's statement, after the translation described
  in [Conventions](#conventions).
- **Partial**: Lean proves part of the statement, or a weaker statement.
- **Not formalized**: nothing in the repository states it. A related lemma may exist; it is
  listed in the notes, but it does not prove the paper's result.

In the summary table, Lean names marked † are internal: they are not restated in
[`Spec.lean`](../PfaffianLean/Spec.lean), and their statements were not part of the author's
statement review (see [Auditing.md](Auditing.md#how-this-formalization-was-produced)). They are
proved, and their axioms are covered by the axiom guard of the `Spec.lean` theorem that uses them
(`outer_pair_bound`). To check what they say, read their statements in the source file.

## Summary table

| Paper | Status | Lean |
|---|---|---|
| [Definitions](#definitions) (§2–3): `I_n`, `a_J(A)`, `A_n(a)`, `Π_n`, `cr`, `Pf`, `A(S)`, `Pf_n(a)`, `A_f(x)` | Formalized | `intervals`, `alpha` (with `pad`), `intervalMatrix`, `perfectMatchings`, `crossings`, `pfaffian`, `pfaffian S A`, `intervalPfaffian`, `skewExtension (kernel f x)` |
| `Pf(A) = Pf_n(a(A))` (§3, before Lemma 3.1) | Formalized | `interval_decomposition_pfaffian` |
| [Interval Decomposition](#interval-decomposition) (Lemma 2.1) | Formalized | `interval_decomposition`, `interval_decomposition_corner` |
| [Twin Rows](#twin-rows) (Lemma 3.1) | Formalized (more general) | `pf_twin_rows`, `pf_twin_rows_consecutive` |
| [Coefficient Positivity](#coefficient-positivity) (Theorem 3.2) | Formalized | `coeff_nonneg`, `intervalPfaffian_isHomogeneous`, `coeff_corner`; `pfaffian_skewOnes` for `Pf(𝟙̃_n) = 1` |
| [Nonnegativity of Interval Coefficients](#nonnegativity-of-interval-coefficients) (Lemma 3.4) | Formalized, except the conjunct `f(x_n − x_1) > 0` | `convex_kernel_additive` |
| [Pfaffian Diameter Bound](#pfaffian-diameter-bound) (Theorem 3.5) | Formalized | `convex_lower_bound`, `convex_lower_bound_skew`; the general step is `additive_lower_bound` |
| [Rainbow Bound](#rainbow-bound) (Theorem 1.1) | Formalized | `additive_rainbow_bound`, `convex_rainbow_bound` |
| [Alternating Prefix Sums](#alternating-prefix-sums) (Lemma 4.1) | Partial: the real inequality `Z_q(A) ≥ 0` only | `prefixSum_nonneg`†; `pfaffian_oneBorder`† |
| [Endpoint Inequality](#endpoint-inequality) (Proposition 4.2) | Partial: the real inequality for `S = [n]` only | `outer_pair_bound`; `firstRowPartial_eq_abel`†, `firstRowPartial_eq_sub`† |
| [Singly Bordered Pfaffian](#bordered-pfaffians) (Corollary 5.1) | Not formalized | — |
| [Doubly Bordered Pfaffian](#bordered-pfaffians) (Corollary 5.2) | Not formalized | — |
| Albouy–Moeckel normalizations of `K_{2m}`, `K^L_{2m+1}`, `K^{xL}_{2m}` (before Corollary 5.3) | Not formalized | — |
| [Albouy–Moeckel](#albouy-moeckel-corollary) (Corollary 5.3) | Partial: the ordinary even-order Pfaffian only | `albouy_moeckel_pos` |
| [Optimality of the Rainbow Bound](#optimality-of-the-rainbow-bound) (Theorem 1.2) | Partial: a weaker conclusion, by a different construction | `exists_pfaffian_lt_prod_of_ne_rainbow` |
| Affine Kernel Pfaffian (Lemma 6.1) | Not formalized | — |
| Constant Outer Layer (Lemma 6.2) | Not formalized | — |

The paper also uses, without stating them as numbered results, `Pf(P A Pᵀ) = det(P) Pf(A)`, the
Pfaffian–determinant identity for block matrices, the matrix determinant lemma, and that a
Pfaffian is alternating in two bordering vectors. None of these is in the repository; they are
used only in the results marked "Not formalized" above.

## Result-by-result notes

Lean statements are quoted from `Spec.lean` (or, for † names, from the source file named).

### Definitions

Manuscript §2 (`sec:interval-decomposition`) and §3 (`sec:pfaffian-positivity`).

`pfaffian S A` is the paper's definition: the sum over perfect matchings `M` of `S` of
`(−1)^{cr(M)} ∏_{(i,j) ∈ M} A_ij`, each `M` a set of pairs `(i, j)` with `i < j`.
`crossings M` counts the ordered pairs `((a, b), (c, d))` of edges of `M` with
`a < c < b < d`; each crossing pair of the paper is counted exactly once, by its ordering with
`a < c`. `pfaffian ∅ A = 1` (`spec_pfaffian_empty`), as in the paper. The paper's `A(S)`, the
principal submatrix on `S` in increasing order, is `pfaffian S A` itself: the Pfaffian is defined
on any finite subset of a linear order, so no reindexing is needed. The paper's interval
coefficient `a_J(A)` is `alpha n A J`, and "nonnegative interval coefficients" is
`A ∈ additiveClass n`. `A_n(a)` is `intervalMatrix n` and `Pf_n(a)` is `intervalPfaffian n`.
See [Conventions](#conventions) for the differences in skew-symmetry and indexing.

The definitions are pinned verbatim in `Spec.lean`; see
[Auditing.md](Auditing.md#definition-guards).

### Interval Decomposition

Manuscript Lemma 2.1, `lem:interval-decomposition`.

```lean
theorem interval_decomposition (n : ℕ) (K : Matrix ℕ ℕ ℝ) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i < j) (hj : j ≤ n) :
    K i j = ∑ J ∈ intervals n with i ∈ Icc J.1 J.2 ∧ j ∈ Icc J.1 J.2, alpha n K J

theorem interval_decomposition_corner (n : ℕ) (K : Matrix ℕ ℕ ℝ) :
    alpha n K (1, n) = K 1 n

theorem interval_decomposition_pfaffian (n : ℕ) (K : Matrix ℕ ℕ ℝ) :
    pfaffian (Icc 1 n) K =
      MvPolynomial.aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n)
```

`interval_decomposition` is the displayed identity, for `1 ≤ i < j ≤ n`, and
`interval_decomposition_corner` is `a_[1,n](A) = A_1n`. The Lean statements are for real families
`K : Matrix ℕ ℕ ℝ` with no skew-symmetry hypothesis; the paper does not specify the ring. The
paper's last clause, `A_n(a(A)) = A` for skew-symmetric `A`, is not stated as a matrix identity.
Its content for the upper entries is `interval_decomposition` (since `intervalMatrix n i j` is by
definition the sum of `a_J` over `J ∋ i, j`), and its Pfaffian consequence `Pf(A) = Pf_n(a(A))`
(stated in §3 of the paper) is `interval_decomposition_pfaffian`.

### Twin Rows

Manuscript Lemma 3.1, `lem:twin-rows`.

```lean
theorem pf_twin_rows {R : Type*} [CommRing R] (n : ℕ) (A : Matrix ℕ ℕ R) {y : ℕ}
    (hy : 1 ≤ y) (hyn : y + 1 ≤ n)
    (htwin_right : ∀ z ∈ Icc 1 n, y + 1 < z → A y z = A (y + 1) z)
    (htwin_left : ∀ z ∈ Icc 1 n, z < y → A z y = A z (y + 1)) :
    pfaffian (Icc 1 n) A = A y (y + 1) * pfaffian (Icc 1 n \ {y, y + 1}) A
```

`pf_twin_rows` states the lemma for `S = [n]` and `pf_twin_rows_consecutive` for two consecutive
elements of any finite subset of a linear order, both over any commutative ring. The Lean
versions assume neither skew-symmetry nor that `n` is even (for odd `n` both sides are `0`). The
twin hypothesis is stated on upper entries: `A y z = A (y+1) z` for `z > y + 1` and
`A z y = A z (y+1)` for `z < y`. For a skew-symmetric matrix this is the paper's hypothesis
`A_ij = A_{i+1,j}` for `j ∉ {i, i+1}`, so the Lean statement implies the paper's.

### Coefficient Positivity

Manuscript Theorem 3.2, `thm:coefficientwise-positive`.

```lean
theorem coeff_nonneg (n : ℕ) (m : intervals n →₀ ℕ) :
    0 ≤ (intervalPfaffian n).coeff m

theorem intervalPfaffian_isHomogeneous (n : ℕ) :
    (intervalPfaffian n).IsHomogeneous (n / 2)

theorem coeff_corner (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) :
    (intervalPfaffian n).coeff (Finsupp.single ⟨(1, n), corner_mem_intervals h2⟩ (n / 2)) = 1
```

`intervalPfaffian n` lives in `MvPolynomial (intervals n) ℤ`, one variable for each `J ∈ I_n`, so
integrality of the coefficients is part of the type. `coeff_nonneg` (every coefficient is `≥ 0`)
and `intervalPfaffian_isHomogeneous` (degree `n / 2`) hold for every `n`; for odd `n` the
polynomial is `0`. `coeff_corner` is the corner coefficient, for even `n ≥ 2`. `Pf(𝟙̃_n) = 1`
(`pfaffian_skewOnes`) is proved by the first-row expansion, not by repeated Twin Rows as in the
paper. The induction step follows the paper: `exists_uncut_gap` is the gap-counting argument and
`restricted_eq_mul_aeval` is `Pf_n^K(a) = s · Pf_{n−2}(b)`, with `collapse` giving the map
`J ↦ φ(J ∩ S_g)` (all in `CoeffPositivity.lean`).

**Example 3.3** (the `n = 4` example after the theorem). `intervalPfaffian_four` is the displayed
nine-monomial expansion of `Pf(A_4(a))`. The second identity,
`Pf(A_4(a)) − A_14 A_23 = a_[1,2] A_34 + a_[3,4] A_13`, giving the rainbow bound at `n = 4`, is not
stated.

### Nonnegativity of Interval Coefficients

Manuscript Lemma 3.4, `nonnegative-interval-coefficient`. ("Additivity of convex kernels" in the
Lean sources.)

```lean
theorem convex_kernel_additive (f : ℝ → ℝ) (hf : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    kernel f x ∈ additiveClass n ∧ alpha n (kernel f x) (1, n) = f (x n - x 1)
```

`convex_kernel_additive` assumes only `f ≥ 0` on `(0, ∞)` (not `f > 0`) and no lower bound on `n`.
It concludes `a_J(A_f(x)) ≥ 0` for all `J ∈ I_n` and `a_[1,n](A_f(x)) = f(x_n − x_1)`. The
remaining conjunct `f(x_n − x_1) > 0` is not part of the Lean statement, since it does not hold
under `f ≥ 0`. Under the paper's hypothesis it is immediate, and it is proved inside
`convex_lower_bound`.

### Pfaffian Diameter Bound

Manuscript Theorem 3.5, `thm:pfaffian-positive-diameter`. ("Convex lower bound" in the Lean
sources.)

```lean
theorem convex_lower_bound (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel f x) ≥ f (x n - x 1) ^ (n / 2) ∧ f (x n - x 1) ^ (n / 2) > 0

theorem convex_lower_bound_skew (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (skewExtension (kernel f x)) ≥ f (x n - x 1) ^ (n / 2) ∧
      f (x n - x 1) ^ (n / 2) > 0

theorem additive_lower_bound (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K =
        MvPolynomial.aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) ∧
      MvPolynomial.aeval (fun J : intervals n => alpha n K J) (intervalPfaffian n) ≥
        K 1 n ^ (n / 2) ∧
      K 1 n ^ (n / 2) ≥ 0
```

`convex_lower_bound` is the theorem, with `n = 0` included (both sides equal `1`).
`kernel f x` is the family `f(x_j − x_i)` over all `i, j`, and is not itself skew-symmetric; since
`pfaffian` reads only the entries with `i < j`, the statement is about `Pf A_f(x)`.
`convex_lower_bound_skew` states it for the skew-symmetric matrix `skewExtension (kernel f x)`,
which is the paper's `A_f(x)` entry for entry. The function `f` may blow up at `0`. The paper's
proof passes through `Pf(A) = Pf_n(a(A)) ≥ a_[1,n](A)^{n/2}` for any `A` with nonnegative interval
coefficients; that step is `additive_lower_bound`, which the paper does not state separately.

### Rainbow Bound

Manuscript Theorem 1.1, `thm:rainbow-bound`.

```lean
theorem additive_rainbow_bound (n : ℕ) (hn : Even n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K ≥ ∏ k ∈ Icc 1 (n / 2), K k (n + 1 - k) ∧
      ∏ k ∈ Icc 1 (n / 2), K k (n + 1 - k) ≥ K 1 n ^ (n / 2)

theorem convex_rainbow_bound (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel f x) ≥ ∏ k ∈ Icc 1 (n / 2), f (x (n + 1 - k) - x k) ∧
      ∏ k ∈ Icc 1 (n / 2), f (x (n + 1 - k) - x k) > 0
```

`additive_rainbow_bound` is the chain `Pf(A) ≥ ∏ A_{k,n+1−k} ≥ A_{1,n}^{n/2}` for
`A ∈ additiveClass n`, and `convex_rainbow_bound` is the kernel case, together with positivity of
the product. Both include `n = 0`. `convex_rainbow_bound` has exactly the hypotheses of
`convex_lower_bound`, and its bound is the stronger one: applied to `K = kernel f x`, the second
part of `additive_rainbow_bound` shows that the product is at least `f(x_n − x_1)^{n/2}`.

The proof peels outer pairs with `outer_pair_bound` (the real form of the
[Endpoint Inequality](#endpoint-inequality) for `S = [n]`) and uses only the restrictions to the
intervals `[k, n+1−k]`: deleting the first or the last point preserves nonnegative interval
coefficients (`mem_additiveClass_of_succ`, `submatrix_succ_mem_additiveClass`).

### Alternating Prefix Sums

Manuscript Lemma 4.1, `lem:alternating-prefix-sum`. **Partial.**

The paper states (i) that each `Z_q(A_n(a))` has nonnegative integer coefficients, and (ii) the
consequence `Z_q(A) ≥ 0` for real `A` with nonnegative interval coefficients. Only (ii) is
formalized. From `Rainbow.lean` (internal, not in `Spec.lean`):

```lean
def prefixSum (N : ℕ) (L : Matrix ℕ ℕ ℝ) (q : ℕ) : ℝ :=
  ∑ t ∈ Ico 1 q, (-1) ^ (t + 1) * pfaffian (Icc 1 N \ {t}) L

theorem prefixSum_nonneg {N : ℕ} (hN : Odd N) {L : Matrix ℕ ℕ ℝ} (hL : L ∈ additiveClass N)
    {q : ℕ} (hq : q ≤ N + 1) : 0 ≤ prefixSum N L q
```

`prefixSum N L q` is the paper's `Z_q(L)`, with the same sign `(−1)^{t+1}`; it holds for odd `N`
including `N = 1`. The Lean proof uses the same bordered family as the paper (`oneBorder L q h` is
the paper's `B(h)`, with the new point numbered `1` instead of `0`, and `pfaffian_oneBorder` is
the paper's row-`0` expansion), but instead of extracting the coefficient of `t` from a polynomial
identity it applies the real Additive lower bound for `h > 0` and lets `h → 0⁺`.

Because `prefixSum` and `oneBorder` are internal definitions, they are not pinned by a definition
guard in `Spec.lean`. `prefixSum_nonneg` enters the reviewed statements only through
`outer_pair_bound`.

### Endpoint Inequality

Manuscript Proposition 4.2, `prop:endpoint-inequality`. ("Outer-pair bound" in the Lean
sources.) **Partial.**

```lean
theorem outer_pair_bound (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) (K : Matrix ℕ ℕ ℝ)
    (hK : K ∈ additiveClass n) :
    pfaffian (Icc 1 n) K ≥ K 1 n * pfaffian (Icc 2 (n - 1)) K
```

The paper states (i) a coefficientwise statement for
`Pf_n(a) − A_n(a)_1n Pf(A_n(a)([n] ∖ {1, n}))`, (ii) `Pf(A) ≥ A_1n Pf(A([n] ∖ {1, n}))` for real
`A` with nonnegative interval coefficients, and (iii) the same inequality for `A(S)`, every
`S ⊆ [n]` of even size `≥ 2`. Only (ii) is formalized, as `outer_pair_bound`
(`Icc 2 (n − 1)` is `[n] ∖ {1, n}`). The paper's observation that restriction to any `S`
preserves the interval structure (`A_n(a)(S) = A_k(b)`) is not formalized; Lean proves only that
deleting the first or the last point preserves nonnegative interval coefficients, which is enough
for the rainbow bound.

The proof goes through the first-row expansion. `firstRowPartial_eq_sub`† identifies the
partial first-row sum `T_{n−1}` with `Pf(K) − K(1, n) Pf(K_{[2,n−1]})`, and Abel summation
(`firstRowPartial_eq_abel`†, for real families rather than polynomials) writes it as a sum of the
alternating prefix sums `Z_q` of `K_{[2,n]}`, with coefficients `a_[1,q](K) ≥ 0` and
`K(1, n−1) ≥ 0`. Each `Z_q` is `≥ 0` by `prefixSum_nonneg`.

### Bordered Pfaffians

Manuscript Corollary 5.1, `cor:single-border`, and Corollary 5.2, `cor:double-border`. **Not
formalized.**

`prefixSum_nonneg` with `q = N + 1` gives `Z_{n+1}(A) ≥ 0`, but the identity between `Z_{n+1}(A)`
and the singly bordered Pfaffian is not stated, and neither is the lower bound `A_{1,n}^m`, so not
even the nonvanishing of the singly bordered Pfaffian follows from the repository. Nothing about
doubly bordered Pfaffians is formalized.

### Albouy-Moeckel corollary

Manuscript Corollary 5.3 (no label), in the section *Bordered Pfaffians and Albouy–Moeckel*.
**Partial.**

```lean
theorem albouy_moeckel_pos (n : ℕ) (hn : Even n) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel (fun r => r ^ (-2 : ℝ)) x) > 0
```

Of the three nonvanishing assertions, only the first is formalized: `albouy_moeckel_pos` states
`Pf A_f(x) > 0` for `f(r) = r^{−2}`, every even `n` and `x_1 < ⋯ < x_n`, for the Pfaffian in the
normalization used here. The bordered assertions are not formalized (see
[Bordered Pfaffians](#bordered-pfaffians)). Neither are the normalizations relating the
Albouy–Moeckel Pfaffians `K_{2m}`, `K^L_{2m+1}`, `K^{xL}_{2m}` to the Pfaffians here (including the
sign `(−1)^m` and the factorials), nor the consequence `dim S(x) = 2`. **The repository therefore
does not formalize the Albouy–Moeckel conjecture.**

### Optimality of the Rainbow Bound

Manuscript Theorem 1.2, `thm:rainbow-bound-optimal`, proved in §6 (`sec:optimal-bound`).
("Only the rainbow survives" in the Lean sources.) **Partial.**

```lean
theorem exists_pfaffian_lt_prod_of_ne_rainbow (n : ℕ) (hn : Even n) (M : Finset (ℕ × ℕ))
    (hM : M ∈ perfectMatchings (Icc 1 n)) (hMr : M ≠ rainbow n) :
    ∃ f : ℝ → ℝ, (∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t) ∧ AntitoneOn f (Set.Ioi 0) ∧
      ConvexOn ℝ (Set.Ioi 0) f ∧
      ∃ x : ℕ → ℝ, StrictMonoOn x (Set.Icc 1 n) ∧
        pfaffian (Icc 1 n) (kernel f x) < ∏ e ∈ M, f (x e.2 - x e.1)
```

`rainbow n` is the matching `{(k, n+1−k) : 1 ≤ k ≤ n/2}`, a perfect matching of `[n]` for even `n`
(`rainbow_mem_perfectMatchings`).

**Infimum zero versus non-universality.** The paper proves that for every perfect matching
`M ≠ R` the infimum of `Pf(A_f(x)) / ∏_M f(x_j − x_i)` over `f` and `x` is `0`.
`exists_pfaffian_lt_prod_of_ne_rainbow` proves that the ratio is `< 1` for some `f` and `x`: the
product over `M` is not a lower bound. This is weaker than the infimum being `0`, and the paper's
statement cannot be recovered from it by rescaling, since the ratio is unchanged when `f` is
multiplied by a positive constant. The Lean statement covers every even `n`; for `n = 0` and
`n = 2` it is vacuous, since `R` is the only perfect matching, so it has content for `n ≥ 4`.

**A different construction.** The Lean proof uses `f(r) = max(9 − r, 1)`. If `M` first departs
from the rainbow at the pair `(k+1, n−k)` (`exists_first_departure`), the points
`k+2, …, n−k−1` are placed at `ε·i`, and the other points at least `8` apart from each other,
where `f = 1`. At `ε = 0` the inner points coincide: Twin Rows removes them in pairs, each
contributing `f(0) = 9`, so `Pf = 9^{n/2−k−1}` (`pfaffian_sharp_zero`), while the product over `M`
is at least `(25/9)·9^{n/2−k−1}` (`prod_sharp_zero`). Both sides are continuous in `ε`
(`continuous_pfaffian`), so the strict inequality holds for some small `ε > 0`, where the points
are strictly increasing. This is not the paper's construction, which uses
`f_T(r) = 1 + (D − r)_+`, the Affine Kernel Pfaffian (Lemma 6.1, `lem:affine-kernel-pfaffian`) and
the Constant Outer Layer lemma (Lemma 6.2, `lem:constant-outer-layer`), and lets `T → ∞`. Neither
lemma is formalized.

## Power kernels

Not a separate result of the paper, which mentions only the case `p = 2`. For `p > 0`, the
function `f(r) = r^(−p)` is positive, nonincreasing and convex on `(0, ∞)`, so the Diameter Bound
applies to it. The exponent is real (`Real.rpow`).

```lean
theorem power_kernel_lower_bound (p : ℝ) (hp : 0 < p) (n : ℕ) (hn : Even n) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel (fun r => r ^ (-p)) x) ≥ ((x n - x 1) ^ (-p)) ^ (n / 2) ∧
      ((x n - x 1) ^ (-p)) ^ (n / 2) > 0
```

`albouy_moeckel_pos` is the case `p = 2`; see the
[Albouy–Moeckel corollary](#albouy-moeckel-corollary) for what it does and does not establish.

For `i ≥ j`, `kernel` evaluates `Real.rpow` at `r ≤ 0`, where its value is a convention. This has
no effect, since `pfaffian` reads only the entries with `i < j`, where `r > 0`.

Mathlib proves convexity of `r ↦ r^p` only for `p ≥ 1`, concavity only for `0 ≤ p ≤ 1`, and
convexity for integer exponents. Convexity for negative real exponents (`convexOn_rpow_neg`) is
proved here by composing with `r ↦ r⁻¹`.

## Results in Lean that are not results of the paper

| Result | Lean | File |
|---|---|---|
| First-row expansion (used in the paper, not stated) | `pfaffian_insert_of_forall_lt`, `pfaffian_Icc_one_eq_sum` | `Pfaffian.lean`, `Rainbow.lean` |
| Evaluation lemma: `Pf` commutes with ring homs | `RingHom.map_pfaffian` | `Pfaffian.lean` |
| `Pf` reads only the upper entries; `Pf` of a skew extension | `pfaffian_congr`, `pfaffian_skewExtension` | `Pfaffian.lean` |
| `Pf(cA) = c^{n/2} Pf(A)`, reindexing, zero rows | `pfaffian_smul`, `pfaffian_image_strictMono`, `pfaffian_eq_zero_of_row` | `PfaffianFacts.lean` |
| Additive lower bound (a step in the paper's proof of Theorem 3.5) | `additive_lower_bound` | `LowerBounds.lean` |
| Lower bound for power kernels `r^{−p}`, `p > 0` | `power_kernel_lower_bound`, `convexOn_rpow_neg` | `PowerKernels.lean` |
| Restriction: deleting the first or the last point | `mem_additiveClass_of_succ`, `submatrix_succ_mem_additiveClass` | `Rainbow.lean` |
| The rainbow is a perfect matching | `rainbow`, `rainbow_mem_perfectMatchings` | `Sharpness.lean` |
| First departure from the rainbow; the `ε = 0` construction | `exists_first_departure`, `pfaffian_sharp_zero`, `prod_sharp_zero` | `Sharpness.lean` |
| Continuity of the Pfaffian in its entries | `continuous_pfaffian` | `Sharpness.lean` |
| Sanity tests (`n = 2, 4` formulas, a numerical value, `Pf(𝟙̃_n) = 1` at `n = 2, 4, 6`) | `PfaffianTests.*` | `Tests.lean` |

All files are in [`PfaffianLean/`](../PfaffianLean).

## Conventions

The statements use the following conventions. Each is a point where a Lean statement must be
translated to compare it with the paper.

- **Ambient types and indexing.** The paper works with `n × n` matrices indexed by
  `[n] = {1, …, n}`, points `x ∈ ℝⁿ`, and `f : (0, ∞) → (0, ∞)`. The Lean statements use
  matrices `Matrix ℕ ℕ R`, indexed by all of `ℕ`, sequences `x : ℕ → ℝ`, and functions
  `f : ℝ → ℝ`. Only finitely many entries and values are ever read: the Pfaffian is
  `pfaffian (Icc 1 n) A`, where `Icc 1 n` is `[n]`; `x` is required to be strictly increasing on
  `Icc 1 n` only; and every hypothesis on `f` is restricted to `Set.Ioi 0`. Indices start at
  `1`, as in the paper. Nothing in the repository uses `Fin n` or states a result for a
  `Matrix (Fin n) (Fin n) R`; a reader who wants that form can transport along `i ↦ i + 1` with
  `pfaffian_image_strictMono`.
- **Pfaffians on subsets.** `pfaffian S A` is defined for any finite set `S` in a linearly
  ordered type, and is the Pfaffian of the principal submatrix of `A` on `S` in increasing order
  (the paper's `Pf(A(S))`). Deleting rows and columns is set difference, so no reindexing is
  needed. Where a proof does reindex (the map `φ` in Coefficient Positivity), it uses
  `pfaffian_image_strictMono`.
- **Skew-symmetry.** The paper's matrices are skew-symmetric. The Lean statements take arbitrary
  families: `pfaffian` reads only the entries `A a b` with `a < b`. For a skew-symmetric matrix
  this is the paper's Pfaffian; for a family `K` it is the Pfaffian of the skew extension
  (`pfaffian_skewExtension`). In particular `kernel f x` and `intervalMatrix n` are not
  skew-symmetric (the latter is symmetric with nonzero diagonal), but their Pfaffians are those
  of `A_f(x)` and `A_n(a)`. For odd `|S|` there are no perfect matchings and the Pfaffian is `0`.
- **Definition of the Pfaffian, and signs.** `pfaffian` is the matching sum with sign
  `(−1)^{cr(M)}`, which is the paper's definition. It is not proved equal to the permutation
  formula, and `Pf² = det` is not proved; the identity `Pf(P A Pᵀ) = det(P) Pf(A)` used in §6 of
  the paper is not in the repository. The sign convention is pinned by tests:
  `Pf = A_12` for `n = 2` and `Pf = A_12 A_34 − A_13 A_24 + A_14 A_23` for `n = 4`
  (`spec_pfaffian_Icc_two`, `spec_pfaffian_Icc_four`), and by the first-row expansion
  `Pf(A) = ∑_{j=2}^{n} (−1)^j A_1j Pf(A([n] ∖ {1, j}))` (`pfaffian_Icc_one_eq_sum`), the sign
  used in the paper's `T_m`. `Z_q` uses the paper's sign `(−1)^{i+1}`. The Albouy–Moeckel
  normalization signs `(−1)^m` are not formalized. See also
  [Checking the Pfaffian definition](Auditing.md#checking-the-pfaffian-definition).
- **Twin rows.** The twin hypothesis is stated on upper entries: `A y z = A y' z` for `z > y'`
  and `A z y = A z y'` for `z < y`. For a skew-symmetric matrix this says that rows `y` and `y'`
  agree outside columns `y` and `y'`.
- **Padding.** The paper sets `A_ij = 0` when an index lies outside `[n]`. For `[p, q] ∈ I_n`
  the only such indices that occur are row `p − 1 = 0` and column `q + 1 = n + 1`, and
  `alpha n K` zeroes exactly these (`pad`) instead of reading row `0` and column `n + 1` of `K`.
  So `alpha n K J` is the paper's `a_J(K)` for every `J ∈ I_n`.
- **`Pf_n(a)`.** `intervalPfaffian n` lives in `MvPolynomial (intervals n) ℤ`, with exactly one
  variable for each interval `[p, q]`, `1 ≤ p < q ≤ n`, written as the pair `(p, q)`. Its value
  `Pf_n(a(K))` is written `MvPolynomial.aeval (fun J => alpha n K J)`.
- **Real versus coefficientwise statements.** The Alternating Prefix Sums lemma and the Endpoint
  Inequality each have a coefficientwise part (a polynomial in the `a_J` has nonnegative
  coefficients) and a real part (an inequality for real `A` with nonnegative interval
  coefficients). Only the real parts are formalized. Coefficient Positivity, by contrast, is
  formalized in its coefficientwise form.
- **Generality.** Some statements are proved without hypotheses they don't need. For example,
  Interval Decomposition holds for every `n`, Twin Rows needs neither skew-symmetry nor even `n`,
  Nonnegativity of Interval Coefficients needs only `f ≥ 0`, and nonnegativity and homogeneity of
  `Pf_n` hold for odd `n` as well, where `Pf_n = 0`. The Diameter Bound and the Rainbow Bound are
  stated for all even `n`, including `n = 0`.

## Terminology

The Lean sources were written from an earlier draft and use its names. The current manuscript
uses different ones:

| Lean sources | Manuscript |
|---|---|
| additive class `𝒜_n`, `additiveClass n` | matrices with nonnegative interval coefficients |
| mixed differences `α_J(K)`, `alpha n K J` | interval coefficients `a_J(A)` |
| `F_n`, `intervalPfaffian n` | `Pf_n(a) = Pf(A_n(a))` |
| `intervalMatrix n` | `A_n(a)` |
| `𝒯_n`, `skewExtension (Matrix.of fun _ _ => 1)` | `𝟙̃_n` |
| `K_{f,x}`, `kernel f x` | `A_f(x)` above the diagonal |
| Additivity of convex kernels | Nonnegativity of Interval Coefficients (Lemma 3.4) |
| Additive lower bound | the inequality `Pf(A) ≥ A_1n^{n/2}` in the proof of Theorem 3.5 |
| Convex lower bound | Pfaffian Diameter Bound (Theorem 3.5) |
| outer-pair bound | Endpoint Inequality (Proposition 4.2), real form, `S = [n]` |
| prefix sums of the bordered-Pfaffian cofactors | Alternating Prefix Sums (Lemma 4.1), real form |
| only the rainbow survives | Optimality of the Rainbow Bound (Theorem 1.2), weaker form |
