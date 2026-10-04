# pfaffian-lean

A Lean 4 + Mathlib formalization of a positivity theorem for Pfaffians of convex nonincreasing
kernels, following the note excerpted in [`refs/pfaffian-convex.tex`](refs/pfaffian-convex.tex).

The formalization is complete: there is no `sorry`, and every result in
[`PfaffianLean/Spec.lean`](PfaffianLean/Spec.lean) depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Main theorem

**Convex lower bound.** For every positive, nonincreasing, convex `f` on `(0, ∞)`, every even `n`,
and every `x_1 < ⋯ < x_n`,

    Pf A_f(x) ≥ f(x_n − x_1)^{n/2} > 0,

where `A_f(x)` is the skew-symmetric matrix with `A_ij = f(x_j − x_i)` for `i < j`. The function
`f` may blow up at `0`.

```lean
theorem convex_lower_bound (f : ℝ → ℝ) (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t)
    (hanti : AntitoneOn f (Set.Ioi 0)) (hconv : ConvexOn ℝ (Set.Ioi 0) f) (n : ℕ) (hn : Even n)
    (x : ℕ → ℝ) (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel f x) ≥ f (x n - x 1) ^ (n / 2) ∧ f (x n - x 1) ^ (n / 2) > 0
```

The case `n = 0` is included; there both sides equal `1`.

## From the reference to Lean

| Reference | Lean | File |
|---|---|---|
| Pfaffian as a signed sum over perfect matchings (eq. (1)) | `pfaffian`, `perfectMatchings`, `crossings`, `edges` | `Pfaffian.lean` |
| Evaluation lemma (Pf commutes with ring homs) | `RingHom.map_pfaffian` | `Pfaffian.lean` |
| First-row expansion | `pfaffian_insert_of_forall_lt` | `Pfaffian.lean` |
| Families, `α`, `I_n`, `𝒜_n`, `F_n`, `K_{f,x}` (Definitions 2.1, 2.2) | `intervals`, `pad`, `alpha`, `additiveClass`, `intervalMatrix`, `intervalPfaffian`, `kernel` | `Families.lean` |
| Twin rows | `pf_twin_rows`, and the general form `pf_twin_rows_consecutive` | `TwinRows.lean` |
| Interval decomposition | `interval_decomposition`, `interval_decomposition_pfaffian`, `interval_decomposition_corner` | `IntervalDecomposition.lean` |
| Additivity of convex kernels | `convex_kernel_additive` | `ConvexKernel.lean` |
| `Pf(𝒯_n) = 1` | `pfaffian_skewOnes` | `PfaffianFacts.lean` |
| Coefficient positivity | `coeff_nonneg`, `intervalPfaffian_isHomogeneous`, `coeff_corner` | `CoeffPositivity.lean` |
| The `F_4` check | `intervalPfaffian_four` | `CoeffPositivity.lean` |
| Additive lower bound | `additive_lower_bound` | `LowerBounds.lean` |
| Convex lower bound | `convex_lower_bound` | `LowerBounds.lean` |

The main proofs are written as named `have` steps that follow the paragraphs of the reference,
with comments quoting the sentence each step proves.

## Conventions

These are the places where the Lean statements differ in form from the reference.

- **Index sets.** The Pfaffian is defined on any finite set `S` of a linearly ordered type:
  `pfaffian S A` is the Pfaffian of the principal submatrix of `A` on `S`, in increasing order.
  The reference's `[n]` is `Finset.Icc 1 n`, and deleting rows and columns is set difference, so
  no reindexing is needed. Where the reference reindexes (the map `φ` in Coefficient positivity),
  the proof uses `pfaffian_image_strictMono`.
- **Upper entries only.** `pfaffian` reads only the entries `A a b` with `a < b`. For a
  skew-symmetric matrix this is exactly eq. (1); for a family `K` it is the Pfaffian of the skew
  extension (`pfaffian_skewExtension`). For odd `|S|` the Pfaffian is `0`.
- **Twin rows.** The twin hypothesis is stated on upper entries: `A y z = A y' z` for `z > y'`
  and `A z y = A z y'` for `z < y`. For a skew-symmetric matrix this is the reference's row
  condition.
- **Padding.** The mixed differences `alpha n K` insert the reference's convention
  `K(0, j) = K(i, n + 1) = 0` explicitly (`pad`), instead of reading row `0` and column `n + 1`
  of `K`.
- **`F_n`.** `intervalPfaffian n` lives in `MvPolynomial (intervals n) ℤ`, with exactly one
  variable for each interval `[p, q]`, `1 ≤ p < q ≤ n`. Its value `F_n(α(K))` is written
  `MvPolynomial.aeval`.
- **`f` and `x`.** `f : ℝ → ℝ`, with every hypothesis restricted to `Set.Ioi 0`, and
  `x : ℕ → ℝ`, required to be strictly increasing on `Icc 1 n` only.
- **Generality.** Some statements drop hypotheses the reference carries but the result doesn't
  need. For example, Interval decomposition holds for every `n`, and nonnegativity and
  homogeneity of `F_n` hold for odd `n` as well, where `F_n = 0`.

## Auditing

[`PfaffianLean/Spec.lean`](PfaffianLean/Spec.lean) is the audit surface: it lets a reader check
the statements without reading any proof.

- Each approved statement is restated in full as a `spec_<name>` theorem, proved by direct
  application of the project theorem.
- Each definition used in a statement is pinned by a `#guard_msgs in #print` of its current form.
- Each theorem has a `#guard_msgs in #print axioms` guard expecting exactly
  `[propext, Classical.choice, Quot.sound]`.

`Spec.lean` is imported by the root module, so a successful `lake build` certifies all of the
following:
- the statements are the approved ones;
- the definitions are unchanged;
- no other axioms are used.

## Building

The project uses Lean `v4.34.1` (see `lean-toolchain`) and Mathlib `v4.34.1`.

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

Sanity tests are in `PfaffianLean/Tests.lean`:
- the `n = 2` and `n = 4` formulas;
- `Pf(𝒯_n) = 1` at `n = 2, 4, 6`.

The `F_4` expansion is checked in `CoeffPositivity.lean`.

## Layout

| File | Contents |
|---|---|
| `PfaffianLean/Pfaffian.lean` | Definition of the Pfaffian; evaluation lemma; first-row expansion |
| `PfaffianLean/Tests.lean` | Sanity tests for the definition |
| `PfaffianLean/Families.lean` | Families, mixed differences, the additive class, `F_n`, `K_{f,x}` |
| `PfaffianLean/IntervalDecomposition.lean` | Interval decomposition |
| `PfaffianLean/ConvexKernel.lean` | Additivity of convex kernels |
| `PfaffianLean/TwinRows.lean` | Twin rows (partner-swap involution) |
| `PfaffianLean/PfaffianFacts.lean` | `Pf(cA)`, reindexing, zero rows, `Pf(𝒯_n) = 1` |
| `PfaffianLean/CoeffPositivity.lean` | Coefficient positivity and the `F_4` check |
| `PfaffianLean/LowerBounds.lean` | Additive and Convex lower bounds |
| `PfaffianLean/Spec.lean` | Frozen statements, definition guards and axiom guards |
| `refs/pfaffian-convex.tex` | The reference excerpt |
| `PROMPT.md` | The task specification the formalization was built against |

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
