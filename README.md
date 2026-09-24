# A Lean proof of Weak Tiling Problem 4.1

This repository formalizes a solution to the `research open` target `WeakTiling.problem_4_1`
registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/WeakTiling.lean).
It is Problem 4.1 of Kolountzakis, Lev and Matolcsi,
[*Geometric implications of weak tiling*](https://arxiv.org/abs/2506.23631):

> Let `Ω ⊂ ℝ` be a finite union of intervals and `ν` a weak tiling measure for `Ω`.
> Must `supp(ν)` have bounded density?

The answer is **yes**.  For every such `Ω` and `ν` there is a constant `C` such that every open
unit interval `(x, x + 1)` contains at most `C` points of `supp(ν)`.

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fweak-tiling-bounded-density%2Frefs%2Fheads%2Fmain%2Flean4web%2FWeakTilingProblem41Lean4Web.lean)

The standalone file has about 11,500 lines, so Lean4Web needs a few minutes to check it.

## Formal Conjectures target

Formal Conjectures states the problem as

```lean
@[category research open, AMS 42 46]
theorem problem_4_1 :
    answer(sorry) ↔ ∀ (Ω : Set ℝ) (_ : IsFiniteUnionOfIntervals Ω)
      (ν : Measure ℝ) (_ : IsWeakTilingMeasure Ω ν), HasBoundedDensity ν.support
```

The file in `lean/` imports this statement's definitions from Formal Conjectures, unchanged, and
proves the statement with the answer `True`:

```lean
theorem WeakTiling.problem_4_1_solved :
    answer(True) ↔ ∀ (Ω : Set ℝ) (_ : IsFiniteUnionOfIntervals Ω)
      (ν : Measure ℝ) (_ : IsWeakTilingMeasure Ω ν), HasBoundedDensity ν.support
```

Thus the theorem `WeakTiling.problem_4_1` can be changed from `research open` to
`research solved` by replacing its answer hole with `True` and using this proof.

## Mathematical explanation (AI generated)

Write

```text
Ω = (a₀, b₀) ∪ (a₁, b₁) ∪ ... ∪ (aₙ₋₁, bₙ₋₁),   a₀ < b₀ < a₁ < ... < bₙ₋₁.
```

A weak tiling measure is a positive, locally finite measure `ν` with

```text
1_Ω * ν = 1_(Ωᶜ)   almost everywhere,   i.e.   1_Ω * (δ₀ + ν) = 1   almost everywhere.
```

The proof has five steps.

1. **Pure point structure.**  `ν` is pure point (Theorem 3.2 of the paper), and

   ```text
   supp(ν) ⊆ ℕL ∪ (−ℕL),
   ```

   where `ℕL` is the set of nonnegative integer combinations of the component lengths
   `L = {bⱼ − aⱼ}`.

2. **Lattice coordinates.**  There are reals `β₁, ..., β_r > 0`, linearly independent over `ℚ`,
   such that every length is a combination of the `βₖ` with positive integer coefficients.  An
   atom `x = Σ uₖ βₖ` then has a unique coordinate vector `u ∈ ℤʳ`.  Let `M(u)` be the mass of
   `δ₀ + ν` at that point.  The tiling equation becomes a finite convolution identity for `M`.
   Moreover, `M` vanishes outside `{0}` and the two strict orthants, and its rows of fixed total
   degree have uniformly bounded mass on both sides.

3. **Characteristic roots.**  For a point `z` of the torus `|z₁| = ... = |z_r| = 1`, put

   ```text
   S_m(z) = Σ_{u₁ + ... + u_r = m} M(u) zᵘ,   m ∈ ℤ.
   ```

   The convolution identity turns `m ↦ S_m(z)` into a bounded two-sided solution of a linear
   recurrence.  Hence it is a sum of exponentials `c(z) λ(z)ᵐ` with `|λ(z)| = 1`.  Near a
   generic point, the roots with nonzero amplitude are isolated by Hankel determinants and a
   Prony polynomial, which also handles repeated characteristic roots.  The implicit function
   theorem makes them depend smoothly on the angles.  Van der Corput estimates and Parseval's
   identity then show that their phases are affine with rational slopes.  So every active root
   is a monomial `λₗ(z) = cₗ z^(kₗ / Q)` with integer exponent vectors `kₗ` and a common
   denominator `Q`.

4. **Amplitudes.**  On the whole torus, the amplitudes are `L²` functions.  Away from finitely
   many frequencies, their Fourier coefficients satisfy a binomial relation
   `a · f(n − v) = b · f(n)` with `|a| = |b|` and `v ≠ 0`.  A square-summable sequence of this
   kind has finite support.  Hence every amplitude is a trigonometric polynomial.

5. **Exit.**  Comparing Fourier coefficients in `S_m(z) = Σₗ cₗ(z) λₗ(z)ᵐ` shows that every
   atom satisfies

   ```text
   Q · u = κ + (u₁ + ... + u_r) · kₗ
   ```

   for one of finitely many pairs `(κ, l)`.  So the coordinate vectors of the atoms lie in a
   finite set together with finitely many lattice rays `w + ℕv` with `v ≠ 0`.  Back on the real
   line, each ray becomes an arithmetic progression with positive step `Σ vₖ βₖ`.  A finite set
   plus finitely many such progressions has bounded density.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.33.1` | Formal Conjectures version, pinned to commit `8927a585...` |
| `lean4web/` | `v4.35.0-rc2` | Standalone mathlib-only proof for Lean4Web, mathlib pinned to `v4.35.0-rc2` |

Each directory contains one proof file, `lakefile.toml`, `lean-toolchain`, and the generated
`lake-manifest.json`.  The two proof files contain the same proof.  They differ only in these
points:

- The Formal Conjectures version imports `FormalConjectures.Paper.WeakTiling` and states the
  result with `answer(True)`.
- The Lean4Web version copies the four definitions it needs verbatim from Formal Conjectures and
  states the result with `True`.
- Lean v4.35 deprecates the core lemmas `if_pos`, `if_neg`, `dif_pos`, `if_true` and `if_false`.
  The Lean4Web version uses their new names `ite_eq_left`, `ite_eq_right`, `dite_eq_left`,
  `ite_true` and `ite_false`.

The file `FormalConjectures/Paper/WeakTiling.lean` is identical at the pinned commit and on the
current `main` branch of Formal Conjectures (checked 2026-09-24).

The proof was developed as a multi-file Lean project.  Each top-level `section` of the proof
files is one file of that project.  Auxiliary lemmas that the final theorem does not use were
removed.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both results are kernel checked.  The proof files contain no `sorry`, `admit`, custom axiom,
`native_decide`, or `unsafe` theorem.  Their final `#print axioms` commands report only Lean's
standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

The files were checked in these environments:

| File | Lean | Dependencies |
|---|---|---|
| `lean/WeakTilingProblem41FC.lean` | `v4.33.1` | Formal Conjectures `8927a585`, mathlib `0df444a3` |
| `lean4web/WeakTilingProblem41Lean4Web.lean` | `v4.35.0-rc2` | mathlib `v4.35.0-rc2` (`06535612`) |
| `lean4web/WeakTilingProblem41Lean4Web.lean` | `v4.35.0-rc2` | live.lean-lang.org ("Latest Mathlib", mathlib `045acef0`), checked in the browser on 2026-09-24 |

## Status boundary

What is proved here:

```text
Let Ω ⊂ ℝ be a finite union of intervals and ν a weak tiling measure for Ω.
Then supp(ν) has bounded density.
```

The proof is machine-checked against the pinned versions of Formal Conjectures and mathlib.  It
has not yet been reviewed independently by a human expert.

This repository does not address Problems 4.2 and 4.3 from the same paper.  Problem 4.3 was
answered negatively separately, in
[weak-tiling-counterexample](https://github.com/KitaKen1/weak-tiling-counterexample).

## Sources

- [Kolountzakis, Lev and Matolcsi, *Geometric implications of weak tiling*, arXiv:2506.23631](https://arxiv.org/abs/2506.23631)
- [Formal Conjectures: `Paper/WeakTiling.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/WeakTiling.lean)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra, and Claude Code using Claude Opus 5.5.
