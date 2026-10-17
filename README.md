# convex-pfaffian-positivity-lean

[![Lean Action CI](https://github.com/wlpjohnson-math/convex-pfaffian-positivity-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/wlpjohnson-math/convex-pfaffian-positivity-lean/actions/workflows/lean_action_ci.yml)

A Lean 4 + Mathlib formalization of part of the paper *Pfaffian Positivity for Convex Kernels and
Optimal Matching Bounds* (W. Johnson).

The paper studies the skew-symmetric matrix `A_f(x)` with entries `A_ij = f(x_j − x_i)` for
`i < j`, where `x_1 < ⋯ < x_n` are points on the line and `f` is positive, nonincreasing and
convex on `(0, ∞)`. It proves that for even `n` the Pfaffian of `A_f(x)` is positive, with the
quantitative *diameter bound* `Pf A_f(x) ≥ f(x_n − x_1)^{n/2}` and the stronger *rainbow bound*,
and applies these to the nonvanishing conjecture of Albouy and Moeckel for collinear central
configurations.

This repository machine-checks the core positivity theorems and the algebraic results they rest
on, and records exactly which results of the paper are checked and in what form.

## At a glance

- **Formalized:** the Pfaffian Diameter Bound and the Rainbow Bound, together with Interval
  Decomposition, Twin Rows, Coefficient Positivity, and Nonnegativity of Interval Coefficients
  (except one conjunct; see the table).
- **Partially formalized:** the Alternating Prefix Sums lemma and the Endpoint Inequality (real
  inequalities only, not their coefficientwise forms), the Optimality theorem (Lean proves a
  weaker statement), and the Albouy–Moeckel corollary (only the ordinary even-order Pfaffian).
- **Not formalized:** the singly and doubly bordered Pfaffian corollaries and the Albouy–Moeckel
  normalizations. **The Albouy–Moeckel conjecture itself is not formalized.**

There is no `sorry`, and every result in [`PfaffianLean/Spec.lean`](PfaffianLean/Spec.lean)
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Main theorem

**Pfaffian Diameter Bound** (manuscript Theorem 3.5). For every positive, nonincreasing, convex
`f` on `(0, ∞)`, every even `n`, and every `x_1 < ⋯ < x_n`,

    Pf A_f(x) ≥ f(x_n − x_1)^{n/2} > 0.

The function `f` may blow up at `0`.

```lean
theorem convex_lower_bound (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel f x) ≥ f (x n - x 1) ^ (n / 2) ∧ f (x n - x 1) ^ (n / 2) > 0
```

`kernel f x` is the family `f(x_j − x_i)` over all `i, j` and is not itself skew-symmetric.
Since `pfaffian` reads only the entries with `i < j`, the statement is about `Pf A_f(x)`;
`convex_lower_bound_skew` states the same bound for the skew-symmetric matrix
`skewExtension (kernel f x)`, which is `A_f(x)`. The paper states the theorem for `n ≥ 2`; the Lean
statement also covers `n = 0`, where both sides equal `1`.

The Rainbow Bound (`convex_rainbow_bound`) has the same hypotheses and the stronger conclusion
`Pf A_f(x) ≥ ∏_{k=1}^{n/2} f(x_{n+1−k} − x_k) > 0`.

## Status

Numbers refer to the current manuscript draft and may change; the
[correspondence document](docs/PaperCorrespondence.md) also gives the LaTeX labels.

| Manuscript result | Status | Lean |
|---|---|---|
| Interval Decomposition (Lemma 2.1) | Formalized | `interval_decomposition`, `interval_decomposition_corner`, `interval_decomposition_pfaffian` |
| Twin Rows (Lemma 3.1) | Formalized (more general) | `pf_twin_rows`, `pf_twin_rows_consecutive` |
| Coefficient Positivity (Theorem 3.2) | Formalized | `coeff_nonneg`, `intervalPfaffian_isHomogeneous`, `coeff_corner` |
| Nonnegativity of Interval Coefficients (Lemma 3.4) | Formalized, except the conjunct `f(x_n − x_1) > 0` | `convex_kernel_additive` |
| Pfaffian Diameter Bound (Theorem 3.5) | Formalized | `convex_lower_bound`, `convex_lower_bound_skew` |
| Rainbow Bound (Theorem 1.1) | Formalized | `additive_rainbow_bound`, `convex_rainbow_bound` |
| Alternating Prefix Sums (Lemma 4.1) | Partial: the real inequality `Z_q(A) ≥ 0` only | `prefixSum_nonneg` |
| Endpoint Inequality (Proposition 4.2) | Partial: the real inequality for `S = [n]` only | `outer_pair_bound` |
| Singly and Doubly Bordered Pfaffians (Corollaries 5.1, 5.2) | Not formalized | — |
| Albouy–Moeckel (Corollary 5.3) | Partial: the ordinary even-order Pfaffian only | `albouy_moeckel_pos` |
| Optimality of the Rainbow Bound (Theorem 1.2) | Partial: a weaker conclusion, by a different construction | `exists_pfaffian_lt_prod_of_ne_rainbow` |
| Affine Kernel Pfaffian, Constant Outer Layer (Lemmas 6.1, 6.2) | Not formalized | — |

Two partial results deserve emphasis:

- **Optimality.** The paper proves that for every perfect matching `M` other than the rainbow, the
  infimum of `Pf A_f(x) / ∏_M f(x_j − x_i)` over `f` and `x` is `0`. Lean proves only that the
  ratio is `< 1` for some `f` and `x`: the product over `M` is not a universal lower bound.
- **Albouy–Moeckel.** `albouy_moeckel_pos` proves `Pf A_f(x) > 0` for `f(r) = r^{−2}`. The
  bordered Pfaffians and the relation to Albouy and Moeckel's normalization are not formalized.

The full table, result-by-result explanations, exact statements and the Lean lemmas that are not
results of the paper are in [docs/PaperCorrespondence.md](docs/PaperCorrespondence.md).

## Conventions in brief

Comparing a Lean statement with the paper requires the following translations:

- **Families indexed by `ℕ`, not `n × n` matrices.** Matrices have type `Matrix ℕ ℕ R`, points are
  sequences `x : ℕ → ℝ` required to be strictly increasing on `Icc 1 n` only, and `f : ℝ → ℝ` has
  every hypothesis restricted to `Set.Ioi 0`. Nothing uses `Fin n`.
- **Finite index sets.** `pfaffian S A` is defined for any finite set `S` in a linear order and is
  the Pfaffian of the principal submatrix on `S`, in increasing order. `[n]` is `Icc 1 n`, and the
  paper's `Pf(A(S))` is `pfaffian S A`.
- **Skew extension.** `pfaffian` reads only the entries `A a b` with `a < b`. So the statements
  take arbitrary families, and the Pfaffian of a family `K` is the Pfaffian of the skew-symmetric
  matrix `skewExtension K` (`pfaffian_skewExtension`).
- **The Pfaffian** is the signed sum over perfect matchings with sign `(−1)^{cr(M)}`, which is the
  paper's definition. It is not related to `det` in this repository.
- **Names.** The Lean sources use the names of an earlier draft: `additiveClass n` is "nonnegative
  interval coefficients", `alpha n K J` is the interval coefficient `a_J(K)`, and
  `intervalPfaffian n` is `Pf_n(a)`.

Details, including padding, signs, and a terminology table, are in
[Conventions](docs/PaperCorrespondence.md#conventions).

## Auditing: `Spec.lean`

[`PfaffianLean/Spec.lean`](PfaffianLean/Spec.lean) lets a reader check the statements without
reading any proof. It restates every reviewed statement as a `spec_<name>` theorem, pins every
definition those statements use with a `#print` guard, guards every theorem's axioms, and shows by
examples that the hypotheses of `convex_lower_bound` are satisfiable. It is imported by the root
module, so `lake build` fails if any statement, definition or axiom list changes.

`Spec.lean` certifies what the Lean theorems say, not how they relate to the paper; that relation
is the subject of the correspondence document. Provenance, the trusted base, signed commits and
reproducibility are covered in [docs/Auditing.md](docs/Auditing.md).

## Building

The project uses Lean `v4.34.1` (see `lean-toolchain`) and Mathlib `v4.34.1` (pinned in
`lake-manifest.json`).

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

CI builds the project on every push and pull request. Sanity tests are in
`PfaffianLean/Tests.lean`; see [Reproducibility](docs/Auditing.md#reproducibility).

## Repository layout

| File | Contents |
|---|---|
| `PfaffianLean/Pfaffian.lean` | Definition of the Pfaffian; evaluation lemma; first-row expansion |
| `PfaffianLean/Tests.lean` | Sanity tests for the definition, including a `#guard` evaluation |
| `PfaffianLean/Families.lean` | Families, interval coefficients, `additiveClass`, `Pf_n`, `kernel` |
| `PfaffianLean/IntervalDecomposition.lean` | Interval Decomposition |
| `PfaffianLean/ConvexKernel.lean` | Nonnegativity of Interval Coefficients |
| `PfaffianLean/TwinRows.lean` | Twin Rows (partner-swap involution) |
| `PfaffianLean/PfaffianFacts.lean` | `Pf(cA)`, reindexing, zero rows, `Pf(𝒯_n) = 1` |
| `PfaffianLean/CoeffPositivity.lean` | Coefficient Positivity and the `F_4` check |
| `PfaffianLean/LowerBounds.lean` | Additive lower bound; Pfaffian Diameter Bound |
| `PfaffianLean/PowerKernels.lean` | Power kernels `r^(−p)` and the case `p = 2` |
| `PfaffianLean/Rainbow.lean` | Real forms of Alternating Prefix Sums and the Endpoint Inequality; Rainbow Bound |
| `PfaffianLean/Sharpness.lean` | The rainbow matching; weak form of the Optimality theorem |
| `PfaffianLean/Spec.lean` | Frozen statements, definition guards, axiom guards and non-vacuity examples |
| `docs/PaperCorrespondence.md` | Theorem-by-theorem correspondence with the manuscript |
| `docs/Auditing.md` | Provenance, `Spec.lean`, trusted base, signed commits, reproducibility |

## Authorship

The Lean code was written by Claude Opus 5.5 (Anthropic), working in Claude Code from a written
excerpt of an early draft of the paper's proofs. The author reviewed the definitions and theorem
statements frozen in `Spec.lean` against the paper before their proofs were written; the proofs
are checked by Lean. Internal helper lemmas were not part of that review. See
[How this formalization was produced](docs/Auditing.md#how-this-formalization-was-produced).

## License

Released under the Apache 2.0 license; see [`LICENSE`](LICENSE).
