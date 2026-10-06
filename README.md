# pfaffian-lean

A Lean 4 + Mathlib formalization of a positivity theorem for Pfaffians of convex nonincreasing kernels.

The formalization is complete apart from the rainbow-bound results below, which are in
progress. Outside those, there is no `sorry`, and every result in
[`PfaffianLean/Spec.lean`](PfaffianLean/Spec.lean) depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

**In progress: the rainbow bound.** [`PfaffianLean/Rainbow.lean`](PfaffianLean/Rainbow.lean)
states the outer-pair bound (`outer_pair_bound`) and the rainbow bound
`Pf(K) ≥ ∏_{k=1}^{n/2} K(k, n+1-k)` on the additive class (`additive_rainbow_bound`) and for
convex kernels (`convex_rainbow_bound`). Their statements are under review and their proofs are
still `sorry`.

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

`kernel f x` is the family `f(x_j − x_i)` over all `i, j`, and is not itself skew-symmetric.
Since `pfaffian` reads only the entries with `i < j`, the statement is about `Pf A_f(x)`.
`convex_lower_bound_skew` states the same bound for the skew-symmetric matrix
`skewExtension (kernel f x)`.

The case `n = 0` is included; there both sides equal `1`.

## Power kernels

For `p > 0`, the function `f(r) = r^(−p)` is positive, nonincreasing and convex on `(0, ∞)`, so
the Convex lower bound applies to it. The exponent is real (`Real.rpow`).

```lean
theorem power_kernel_lower_bound (p : ℝ) (hp : 0 < p) (n : ℕ) (hn : Even n) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel (fun r => r ^ (-p)) x) ≥ ((x n - x 1) ^ (-p)) ^ (n / 2) ∧
      ((x n - x 1) ^ (-p)) ^ (n / 2) > 0

theorem albouy_moeckel_pos (n : ℕ) (hn : Even n) (x : ℕ → ℝ)
    (hx : StrictMonoOn x (Set.Icc 1 n)) :
    pfaffian (Icc 1 n) (kernel (fun r => r ^ (-2 : ℝ)) x) > 0
```

The case `p = 2` is the Albouy–Moeckel kernel. That their matrix is this kernel is shown in the
paper, not here.

For `i ≥ j`, `kernel` evaluates `Real.rpow` at `r ≤ 0`, where its value is a convention. This has
no effect, since `pfaffian` reads only the entries with `i < j`, where `r > 0`.

Mathlib proves convexity of `r ↦ r^p` only for `p ≥ 1`, concavity only for `0 ≤ p ≤ 1`, and
convexity for integer exponents. Convexity for negative real exponents (`convexOn_rpow_neg`) is
proved here by composing with `r ↦ r⁻¹`.

## Results

| Result | Lean | File |
|---|---|---|
| Pfaffian as a signed sum over perfect matchings | `pfaffian`, `perfectMatchings`, `crossings`, `edges` | `Pfaffian.lean` |
| Evaluation lemma (Pf commutes with ring homs) | `RingHom.map_pfaffian` | `Pfaffian.lean` |
| First-row expansion | `pfaffian_insert_of_forall_lt` | `Pfaffian.lean` |
| Families, `α`, `I_n`, `𝒜_n`, `F_n`, `K_{f,x}` | `intervals`, `pad`, `alpha`, `additiveClass`, `intervalMatrix`, `intervalPfaffian`, `kernel` | `Families.lean` |
| Twin rows | `pf_twin_rows`, and the general form `pf_twin_rows_consecutive` | `TwinRows.lean` |
| Interval decomposition | `interval_decomposition`, `interval_decomposition_pfaffian`, `interval_decomposition_corner` | `IntervalDecomposition.lean` |
| Additivity of convex kernels | `convex_kernel_additive` | `ConvexKernel.lean` |
| `Pf(𝒯_n) = 1` | `pfaffian_skewOnes` | `PfaffianFacts.lean` |
| Coefficient positivity | `coeff_nonneg`, `intervalPfaffian_isHomogeneous`, `coeff_corner` | `CoeffPositivity.lean` |
| The `F_4` check | `intervalPfaffian_four` | `CoeffPositivity.lean` |
| Additive lower bound | `additive_lower_bound` | `LowerBounds.lean` |
| Convex lower bound | `convex_lower_bound` | `LowerBounds.lean` |
| Convex lower bound, skew-symmetric form | `convex_lower_bound_skew` | `LowerBounds.lean` |
| Power kernels `r^(−p)`, `p > 0` | `power_kernel_lower_bound`, `convexOn_rpow_neg` | `PowerKernels.lean` |
| Albouy–Moeckel kernel (`p = 2`) | `albouy_moeckel_pos` | `PowerKernels.lean` |

The main proofs are written as named `have` steps, each commented with the step of the argument
it proves.

## Conventions

The statements use the following conventions.

- **Index sets.** The Pfaffian is defined on any finite set `S` of a linearly ordered type:
  `pfaffian S A` is the Pfaffian of the principal submatrix of `A` on `S`, in increasing order.
  `[n] = {1, …, n}` is `Finset.Icc 1 n`, and deleting rows and columns is set difference, so no
  reindexing is needed. Where a proof does reindex (the map `φ` in Coefficient positivity), it
  uses `pfaffian_image_strictMono`.
- **Upper entries only.** `pfaffian` reads only the entries `A a b` with `a < b`. For a
  skew-symmetric matrix this is the usual signed sum over perfect matchings; for a family `K` it
  is the Pfaffian of the skew extension (`pfaffian_skewExtension`). For odd `|S|` the Pfaffian
  is `0`.
- **Twin rows.** The twin hypothesis is stated on upper entries: `A y z = A y' z` for `z > y'`
  and `A z y = A z y'` for `z < y`. For a skew-symmetric matrix this says that rows `y` and `y'`
  agree outside columns `y` and `y'`.
- **Padding.** The mixed differences `alpha n K` insert the convention
  `K(0, j) = K(i, n + 1) = 0` explicitly (`pad`), instead of reading row `0` and column `n + 1`
  of `K`.
- **`F_n`.** `intervalPfaffian n` lives in `MvPolynomial (intervals n) ℤ`, with exactly one
  variable for each interval `[p, q]`, `1 ≤ p < q ≤ n`. Its value `F_n(α(K))` is written
  `MvPolynomial.aeval`.
- **`f` and `x`.** `f : ℝ → ℝ`, with every hypothesis restricted to `Set.Ioi 0`, and
  `x : ℕ → ℝ`, required to be strictly increasing on `Icc 1 n` only.
- **Generality.** Some statements are proved without hypotheses they don't need. For example,
  Interval decomposition holds for every `n`, and nonnegativity and homogeneity of `F_n` hold for
  odd `n` as well, where `F_n = 0`.

## How this formalization was produced

The Lean code was written by Claude Opus 5.5 (Anthropic), working in Claude Code from a written
excerpt of an early draft of the paper's proofs. The work ran in stages. At each stage, the definitions and theorem
statements were written first, with `sorry` proofs, and reviewed by the author against the paper
before any proof was written. Approved statements were then frozen in `Spec.lean`. The proofs
themselves are checked by Lean. The author's review covers the definitions and statements in
`Spec.lean`, which is what a reader needs to check to trust the result.

## Auditing

[`PfaffianLean/Spec.lean`](PfaffianLean/Spec.lean) is the audit surface: it lets a reader check
the statements without reading any proof.

- Each statement approved by the author is restated in full as a `spec_<name>` theorem, proved
  by direct application of the project theorem.
- Each definition used in a statement is pinned by a `#guard_msgs in #print` of its current form.
- Each theorem has a `#guard_msgs in #print axioms` guard expecting exactly
  `[propext, Classical.choice, Quot.sound]`.
- A final "Non-vacuity" section shows the hypotheses of `convex_lower_bound` are satisfiable:
  for every even `n`, it applies the theorem with `x k = k` to `f = 1` and to `f t = t⁻¹` (which
  blows up at `0`), proving all the other hypotheses from Mathlib.

`Spec.lean` is imported by the root module, so a successful `lake build` certifies all of the
following:
- the project's theorems prove exactly the statements in `Spec.lean`;
- the definitions match their pinned forms;
- no other axioms are used.

That `Spec.lean` is the reviewed version is recorded by the signed commit history (see
[Verification](#verification)).

The definition of `pfaffian` can also be checked without relying on the crossing-number formula.
`spec_pfaffian_empty` and `spec_pfaffian_insert_of_forall_lt` together determine `pfaffian` on
every finite set, by induction on its size, removing the minimum each time. For `S = [n]`, the
term in which `1` is matched to `j` has sign `(−1)^(j−2) = (−1)^j`, which is the standard
first-row expansion. So a reader can check the definition either directly or through these two
lemmas.

## What's trusted

The result relies on three things:
- Lean's kernel.
- Mathlib's definitions of the standard notions in the statements: ℝ, `ConvexOn`, `AntitoneOn`,
  `StrictMonoOn`, `Even`, `Finset`, `Set.Icc`, `Matrix` and `MvPolynomial`. `MvPolynomial` is
  used only in the intermediate statements. The power-kernel results also use `Real.rpow`.
- The project definitions pinned in `Spec.lean`. The main theorem uses only five of them:
  `edges`, `perfectMatchings`, `crossings`, `pfaffian` and `kernel`, plus `skewExtension` for the
  skew form. `intervals`, `pad`, `alpha`, `additiveClass`, `intervalMatrix` and
  `intervalPfaffian` appear only in intermediate statements.

## Building

The project uses Lean `v4.34.1` (see `lean-toolchain`) and Mathlib `v4.34.1`.

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

Sanity tests are in `PfaffianLean/Tests.lean`:
- the `n = 2` and `n = 4` formulas;
- the value `418` for the skew matrix with `A_ij = 10i + j` for `i < j`, evaluated by `#guard`;
- `Pf(𝒯_n) = 1` at `n = 2, 4, 6`.

The `F_4` expansion is checked in `CoeffPositivity.lean`.

## Layout

| File | Contents |
|---|---|
| `PfaffianLean/Pfaffian.lean` | Definition of the Pfaffian; evaluation lemma; first-row expansion |
| `PfaffianLean/Tests.lean` | Sanity tests for the definition, including a `#guard` evaluation |
| `PfaffianLean/Families.lean` | Families, mixed differences, the additive class, `F_n`, `K_{f,x}` |
| `PfaffianLean/IntervalDecomposition.lean` | Interval decomposition |
| `PfaffianLean/ConvexKernel.lean` | Additivity of convex kernels |
| `PfaffianLean/TwinRows.lean` | Twin rows (partner-swap involution) |
| `PfaffianLean/PfaffianFacts.lean` | `Pf(cA)`, reindexing, zero rows, `Pf(𝒯_n) = 1` |
| `PfaffianLean/CoeffPositivity.lean` | Coefficient positivity and the `F_4` check |
| `PfaffianLean/LowerBounds.lean` | Additive and Convex lower bounds |
| `PfaffianLean/PowerKernels.lean` | Power kernels `r^(−p)` and the Albouy–Moeckel case |
| `PfaffianLean/Spec.lean` | Frozen statements, definition guards, axiom guards and non-vacuity examples |

## Verification

Commits and release tags are signed with the SSH key `SHA256:rbBuGOZMBxVRlDiLsdjqGtmhfobwvKrNbBt0dQxzivU` (ed25519), whose public key is in `allowed_signers`. To verify:

```
git config gpg.ssh.allowedSignersFile allowed_signers
git log --show-signature
```
