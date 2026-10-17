# Auditing and reproducibility

This document explains how the formalization was produced, what a successful build certifies,
what must be trusted, and how to reproduce and verify the build. For what the Lean theorems say
about the paper, see [PaperCorrespondence.md](PaperCorrespondence.md); for the landing page, see
the [README](../README.md).

- [What a successful build certifies](#what-a-successful-build-certifies)
- [How this formalization was produced](#how-this-formalization-was-produced)
- [The role of Spec.lean](#the-role-of-speclean)
- [Checking the Pfaffian definition](#checking-the-pfaffian-definition)
- [What's trusted](#whats-trusted)
- [Signed commits](#signed-commits)
- [Reproducibility](#reproducibility)

## What a successful build certifies

[`PfaffianLean/Spec.lean`](../PfaffianLean/Spec.lean) is imported by the root module
`PfaffianLean.lean`, so a successful `lake build` certifies all of the following:

- the project's theorems prove the statements in `Spec.lean`, as written there;
- the definitions match their pinned forms;
- no axioms beyond `propext`, `Classical.choice` and `Quot.sound` are used by any theorem guarded
  in `Spec.lean`. In particular none of them depends on `sorry`, which would add the axiom
  `sorryAx`.

There is also no `sorry` anywhere in the source (see [Reproducibility](#reproducibility)).

A build does **not** certify:

- that the Lean statements say what the paper says. That is a matter of reading the statements;
  the comparison, including which paper results are only partially formalized or not formalized,
  is in [PaperCorrespondence.md](PaperCorrespondence.md);
- anything about the results of the paper that are not formalized;
- that Mathlib's definitions mean what a reader expects (see [What's trusted](#whats-trusted)).

## How this formalization was produced

The Lean code was written by Claude Opus 5.5 (Anthropic), working in Claude Code from a written
excerpt of an early draft of the paper's proofs. The work ran in stages. At each stage, the
definitions and theorem statements were written first, with `sorry` proofs, and reviewed by the
author against the paper before any proof was written. Approved statements were then frozen in
`Spec.lean`. The proofs themselves are checked by Lean. The author's review covers the definitions
and statements in `Spec.lean`, which is what a reader needs to check to trust the result.
Internal helper lemmas and definitions, which do not appear in `Spec.lean`, were not part of that
review; the ones that matter for the comparison with the paper are marked † in the
[summary table](PaperCorrespondence.md#summary-table).

The stages are visible in the commit history: each has a "statement gate" commit, which adds its
statements to `Spec.lean`, and a "proof gate" commit, which enables its axiom guards.

Two arguments were devised during formalization rather than taken from the draft: the proof that
the prefix sums of the bordered-Pfaffian cofactors are nonnegative (`prefixSum_nonneg` in
`Rainbow.lean`, via a one-border family and the limit `h → 0⁺`), a result the draft states without
proof; and the construction in `Sharpness.lean`, which differs from the draft's proof.

The current manuscript proves both results differently. Its proof of the Alternating Prefix Sums
lemma uses the same bordered family but extracts a coefficient of a polynomial instead of taking a
limit, and so also proves the coefficientwise statement, which is not formalized. Its proof of the
Optimality theorem uses the Affine Kernel Pfaffian and Constant Outer Layer lemmas and gives the
stronger infimum statement, which is not formalized either. See
[Alternating Prefix Sums](PaperCorrespondence.md#alternating-prefix-sums) and
[Optimality of the Rainbow Bound](PaperCorrespondence.md#optimality-of-the-rainbow-bound).

## The role of Spec.lean

[`PfaffianLean/Spec.lean`](../PfaffianLean/Spec.lean) is the audit surface: it lets a reader check
the statements without reading any proof. According to its header, it changes only at gates: new
spec theorems and definition guards at a statement gate, enabled axiom guards at a proof gate.

### Spec theorems

Each statement approved by the author is restated in full as a `spec_<name>` theorem, proved by
direct application of the project theorem `<name>`. If the project theorem's statement stops
implying the frozen one by direct application, the `spec_` theorem fails to type-check and the
build fails.

### Definition guards

Each project definition used in a statement is pinned by a `#guard_msgs in #print` of its current
form: `edges`, `perfectMatchings`, `crossings`, `pfaffian`, `skewExtension`, `intervals`, `pad`,
`alpha`, `additiveClass`, `intervalMatrix`, `intervalPfaffian`, `kernel` and `rainbow`. Changing
any of them changes the printed form and fails the build.

### Axiom guards

Each theorem has a `#guard_msgs in #print axioms` guard expecting exactly
`[propext, Classical.choice, Quot.sound]`. The guards of a stage were enabled at that stage's
proof gate; all are enabled now. Since `#print axioms` collects axioms transitively, the guards
also cover every internal lemma a guarded theorem uses.

### Non-vacuity examples

A final "Non-vacuity" section shows the hypotheses of `convex_lower_bound` are satisfiable: for
every even `n`, it applies the theorem with `x k = k` to `f = 1` and to `f t = t⁻¹` (which blows up
at `0`), proving all the other hypotheses from Mathlib.

`Spec.lean` also contains smaller checks: `rainbow 4 = {(1, 4), (2, 3)}`; that the hypotheses of
`exists_pfaffian_lt_prod_of_ne_rainbow` hold for `n = 4` and `M = {(1, 2), (3, 4)}`; and that the
conclusion of `power_kernel_lower_bound` is that of `convex_lower_bound` at `f r = r ^ (-p)`, by
`rfl`.

### What Spec.lean does not cover

`Spec.lean` certifies what the Lean theorems say, not how they relate to the paper. That relation
is described in [PaperCorrespondence.md](PaperCorrespondence.md).

Internal lemmas and definitions are not restated or pinned. Their axioms are covered through the
guarded theorems that use them, but to know what they state a reader must read the source. This
matters for the partial formalization of the Alternating Prefix Sums lemma, which is stated with
the internal definition `prefixSum` (see
[Alternating Prefix Sums](PaperCorrespondence.md#alternating-prefix-sums)).

## Checking the Pfaffian definition

`pfaffian S A` is the sum over perfect matchings `M` of `S` of `(−1)^{cr(M)} ∏_{(a,b) ∈ M} A a b`,
where `crossings M` counts the ordered pairs of edges `((a, b), (c, d))` of `M` with
`a < c < b < d`. Each crossing pair is counted exactly once, by its ordering with `a < c`.

The definition can also be checked without relying on the crossing-number formula.
`spec_pfaffian_empty` and `spec_pfaffian_insert_of_forall_lt` together determine `pfaffian` on
every finite set, by induction on its size, removing the minimum each time. For `S = [n]`, the
term in which `1` is matched to `j` has sign `(−1)^(j−2) = (−1)^j`, which is the standard
first-row expansion. So a reader can check the definition either directly or through these two
lemmas.

The sign convention is also pinned by tests, restated in `Spec.lean`: `Pf = A_12` for `n = 2`,
`Pf = A_12 A_34 − A_13 A_24 + A_14 A_23` for `n = 4`, and `Pf(𝒯_n) = 1` at `n = 2, 4, 6` for the
skew matrix `𝒯_n` with all upper entries `1`. The repository does not relate `pfaffian` to the
determinant (`Pf² = det` is not proved).

## What's trusted

The result relies on three things:

- Lean's kernel.
- Mathlib's definitions of the standard notions in the statements: ℝ, `ConvexOn`, `AntitoneOn`,
  `StrictMonoOn`, `Even`, `Finset`, `Set.Icc`, `Matrix` and `MvPolynomial`. `MvPolynomial` is
  used only in the intermediate statements (with `Finsupp` for monomials, and
  `MvPolynomial.IsHomogeneous`). The power-kernel results also use `Real.rpow`.
- The project definitions pinned in `Spec.lean`. The main theorem uses only five of them:
  `edges`, `perfectMatchings`, `crossings`, `pfaffian` and `kernel`, plus `skewExtension` for the
  skew form; so do the power-kernel results and `convex_rainbow_bound`. `intervals`, `pad`,
  `alpha` and `additiveClass` also appear in the statements about nonnegative interval
  coefficients (`additive_lower_bound`, `outer_pair_bound` and `additive_rainbow_bound`), and
  `intervalMatrix` and `intervalPfaffian` only in intermediate statements. The result
  `exists_pfaffian_lt_prod_of_ne_rainbow` also uses `rainbow`.

Lean's kernel checks every proof; nothing in the proofs needs to be trusted.

## Signed commits

Commits are signed with the SSH key
`SHA256:rbBuGOZMBxVRlDiLsdjqGtmhfobwvKrNbBt0dQxzivU` (ed25519), whose public key is in
[`allowed_signers`](../allowed_signers). To verify without changing your git configuration:

```sh
git -c gpg.ssh.allowedSignersFile=allowed_signers log --show-signature
```

or, to make the setting persistent for this clone:

```sh
git config gpg.ssh.allowedSignersFile allowed_signers
git log --show-signature
```

Each signed commit should show a good signature for `wlj1@umd.edu` with that key. As of commit
`c9dc984`, every commit in the history is signed with this key. Release tags, starting with
`v1.0.0`, are signed with the same key; verify one with
`git -c gpg.ssh.allowedSignersFile=allowed_signers tag -v v1.0.0`.

What signatures establish, and what they do not:

- A good signature shows that the commit was created by someone holding the private key, and
  that its contents have not changed since. Together with the gate commits, this records the
  version of `Spec.lean` committed under the author's key at each stage.
- Signatures do **not** certify mathematical correctness; that is the job of Lean's kernel. They
  do not certify that the statements match the paper; that requires reading the statements (see
  [PaperCorrespondence.md](PaperCorrespondence.md)). They are not an independent review.
- `allowed_signers` is part of the repository, so checking against it only shows that the commits
  agree with the key the repository itself names. To tie the key to the author, compare it with a
  copy obtained independently, for example the signing keys on the author's GitHub account.

## Reproducibility

**Versions.** Lean `v4.34.1` (`lean-toolchain`: `leanprover/lean4:v4.34.1`), installed
automatically by `elan`. Mathlib `v4.34.1`, pinned in `lake-manifest.json` to commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

**Build.**

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

The build checks every proof and every guard in `Spec.lean`; a failing guard is a build error.

**Continuous integration.** [`.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml)
runs `leanprover/lean-action` on every push and pull request, and on manual dispatch.

**Further checks.**

- No `sorry`: `grep -rnw sorry PfaffianLean/` finds no occurrence.
- Axioms of any declaration, including internal lemmas not guarded in `Spec.lean`: put
  `import PfaffianLean` and `#print axioms <name>` in a file outside the source tree and run
  `lake env lean <file>`.

**Sanity tests** are in [`PfaffianLean/Tests.lean`](../PfaffianLean/Tests.lean):

- the `n = 2` and `n = 4` formulas;
- the value `418` for the skew matrix with `A_ij = 10i + j` for `i < j`, evaluated by `#guard`;
- `Pf(𝒯_n) = 1` at `n = 2, 4, 6`.

The `F_4` expansion (`intervalPfaffian_four`) is checked in
[`PfaffianLean/CoeffPositivity.lean`](../PfaffianLean/CoeffPositivity.lean) and restated in
`Spec.lean`.
