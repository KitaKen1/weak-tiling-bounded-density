import Mathlib

#eval Lean.versionString

/-!
# Weak Tiling Problem 4.1: standalone Lean4Web proof

This file is self-contained apart from mathlib.  It restates the four definitions used by the
Formal Conjectures statement `WeakTiling.problem_4_1`
([source](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/WeakTiling.lean))
and proves that statement with the answer `True`.  The problem is Problem 4.1 of Kolountzakis,
Lev and Matolcsi, *Geometric implications of weak tiling*
([arXiv:2506.23631](https://arxiv.org/abs/2506.23631)): if `Ω ⊂ ℝ` is a finite union of intervals
and `ν` is a weak tiling measure for `Ω`, then `supp ν` has bounded density.

The final theorem is `WeakTiling.problem_4_1_solved`.

## Proof outline

1. **Pure point structure.**  A weak tiling measure `ν` of `Ω = ⋃ⱼ (aⱼ, bⱼ)` is pure point
   (Theorem 3.2 of the paper), and its support lies in `ℕL ∪ -ℕL`, where `L` is the set of
   component lengths.
2. **Lattice coordinates.**  The lengths are written with positive integer coordinates over a
   `ℚ`-linearly independent family.  In these coordinates the atoms of `δ₀ + ν` form a
   nonnegative lattice function `M`.  It satisfies the finite convolution identity coming from
   the tiling equation, lives in the two strict orthants, and has uniformly bounded rows of fixed
   total degree on both sides (`LatticeTilingData`).
3. **Characteristic roots.**  For each point of the torus, the degree slices of `M` form a
   bounded two-sided solution of a linear recurrence, so they are sums of unimodular
   exponentials.  The active roots are isolated with Hankel determinants and a Prony polynomial,
   which also covers repeated roots.  The implicit function theorem continues them smoothly.
   Van der Corput estimates and Parseval's identity force affine phases with rational slopes,
   so the active roots are monomials.
4. **Amplitudes.**  On the torus the amplitudes are `L²` functions.  Their Fourier coefficients
   satisfy a binomial recursion away from finitely many exceptional frequencies, and an `ℓ²`
   lemma shows that they are finitely supported.  So each amplitude is a trigonometric
   polynomial.
5. **Exit.**  Matching Fourier coefficients places every atom on one of finitely many lattice
   rays `w + ℕ v` (`latticeCoreHypothesis_holds`).  Back on the real line, the support is covered
   by a finite set and finitely many arithmetic progressions, and so has bounded density.

The file was generated from a multi-file development.  Each top-level `section` below is one
file of that development, and auxiliary lemmas that the final theorem does not use were removed.
-/

/-! ## Definitions from Formal Conjectures

The following four definitions are copied verbatim from
`FormalConjectures/Paper/WeakTiling.lean` (Copyright 2026 The Formal Conjectures Authors,
Apache License 2.0). -/

section FormalConjecturesDefinitions

open MeasureTheory Set ENNReal NNReal

namespace WeakTiling

/-- A set $A \subseteq \mathbb{R}$ is a **union of $n$ intervals** if it can be written as
    $A = \bigcup_{i=1}^{n} (a_i, b_i)$ with $a_1 < b_1 < a_2 < b_2 < \dots < a_n < b_n$,
    i.e., as a disjoint union of $n$ nondegenerate open intervals in strict order with strict
    separation. This matches the convention of [the paper](https://arxiv.org/abs/2506.23631)
    (see e.g. Theorem 3.4 there). -/
def IsUnionOfNIntervals (n : ℕ) (A : Set ℝ) : Prop :=
  ∃ (a b : Fin n → ℝ),
    (∀ i : Fin n, a i < b i) ∧
    (∀ i j : Fin n, i < j → b i < a j) ∧
    A = ⋃ i, Set.Ioo (a i) (b i)

/-- A set $A \subseteq \mathbb{R}$ is a **finite union of intervals** if it is a union of $n$
    intervals for some $n$. -/
def IsFiniteUnionOfIntervals (A : Set ℝ) : Prop :=
  ∃ n, IsUnionOfNIntervals n A

/-- A positive, locally finite Borel measure $\nu$ on $\mathbb{R}$ is a **weak tiling measure**
    for a bounded measurable set $\Omega \subset \mathbb{R}$ if the convolution
    $1_\Omega \ast \nu = 1_{\Omega^c}$ holds almost everywhere, i.e.,
    $\int 1_\Omega(x - t) \, d\nu(t) = 1_{\Omega^c}(x)$ for a.e. $x \in \mathbb{R}$.

    This is Definition 1.1 from [the paper](https://arxiv.org/abs/2506.23631). -/
def IsWeakTilingMeasure (Ω : Set ℝ) (ν : Measure ℝ) : Prop :=
  Bornology.IsBounded Ω ∧
  MeasurableSet Ω ∧
  IsLocallyFiniteMeasure ν ∧
  ∀ᵐ x ∂(volume : Measure ℝ),
    ∫ t, Ω.indicator (fun _ => (1 : ℝ)) (x - t) ∂ν =
    Ωᶜ.indicator (fun _ => (1 : ℝ)) x

/-- A set $\Lambda \subseteq \mathbb{R}$ has **bounded density** if the number of points of
    $\Lambda$ in any unit open interval is uniformly bounded:
    $\sup_{x \in \mathbb{R}} \#(\Lambda \cap (x, x + 1)) < \infty$. -/
def HasBoundedDensity (Λ : Set ℝ) : Prop :=
  ∃ C : ℕ, ∀ x : ℝ, (Λ ∩ Set.Ioo x (x + 1)).Finite ∧ (Λ ∩ Set.Ioo x (x + 1)).ncard ≤ C

end WeakTiling

end FormalConjecturesDefinitions

/-! ## Weak tiling Problem 4.1: the bounded-density exit lemma -/

section Root

section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace WeakTiling

set_option maxHeartbeats 1000000

/-- The two-sided arithmetic progression `c + hℤ`. -/
def arithmeticProgression (c h : ℝ) : Set ℝ :=
  {y | ∃ k : ℤ, y = c + (k : ℝ) * h}

/-- A finite arithmetic-progression cover: the set is contained in a finite exceptional set and
finitely many two-sided arithmetic progressions with positive steps. -/
def HasFiniteArithmeticProgressionCover (Λ : Set ℝ) : Prop :=
  ∃ (E : Set ℝ) (n : ℕ) (c h : Fin n → ℝ),
    E.Finite ∧ (∀ i, 0 < h i) ∧
      Λ ⊆ E ∪ ⋃ i, arithmeticProgression (c i) (h i)

/-- Distinct points in `c + hℤ`, with `h > 0`, are more than `h / 2` apart. -/
lemma arithmeticProgression_isSeparated (c h : ℝ) (hh : 0 < h) :
    Metric.IsSeparated (ENNReal.ofReal (h / 2))
      (arithmeticProgression c h) := by
  rintro y ⟨k, rfl⟩ z ⟨l, rfl⟩ hne
  have hdistpos : 0 < dist (c + (k : ℝ) * h) (c + (l : ℝ) * h) := dist_pos.mpr hne
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hdistpos]
  rw [Real.dist_eq]
  have hkl : k ≠ l := by
    intro h
    apply hne
    simp [h]
  have hdiff : (1 : ℝ) ≤ |((k - l : ℤ) : ℝ)| := by
    rw [← Int.cast_one, ← Int.cast_abs, Int.cast_le]
    exact Int.one_le_abs (sub_ne_zero.mpr hkl)
  rw [show c + (k : ℝ) * h - (c + (l : ℝ) * h) = ((k - l : ℤ) : ℝ) * h by
    push_cast
    ring]
  rw [abs_mul, abs_of_pos hh]
  nlinarith

/-- A single two-sided arithmetic progression with positive step has bounded density. -/
theorem hasBoundedDensity_arithmeticProgression (c h : ℝ) (hh : 0 < h) :
    HasBoundedDensity (arithmeticProgression c h) := by
  let ε : ℝ≥0 := ⟨h / 4, by positivity⟩
  obtain ⟨N, _hNsub, hNfin, hNcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact (s := Set.Icc (0 : ℝ) 1)
      (ε := ε) (by
        apply ne_of_gt
        exact_mod_cast (div_pos hh (by norm_num : (0 : ℝ) < 4))) isCompact_Icc
  refine ⟨N.ncard, fun x ↦ ?_⟩
  let S : Set ℝ := arithmeticProgression c h ∩ Set.Ioo x (x + 1)
  have hSsep : Metric.IsSeparated (ENNReal.ofReal (h / 2)) S :=
    (arithmeticProgression_isSeparated c h hh).subset inter_subset_left
  let center : S → N := fun y ↦ by
    have hyunit : y.1 - x ∈ Set.Icc (0 : ℝ) 1 := by
      rcases y.2.2 with ⟨hylo, hyhi⟩
      constructor <;> linarith
    exact ⟨(hNcover hyunit).choose, (hNcover hyunit).choose_spec.1⟩
  have hcenter_close (y : S) : edist (y.1 - x) (center y : ℝ) ≤ ε :=
    (hNcover (by
      rcases y.2.2 with ⟨hylo, hyhi⟩
      constructor <;> linarith)).choose_spec.2
  have hcenter_inj : Function.Injective center := by
    intro y z hyz
    apply Subtype.ext
    by_contra hyz'
    have hsep := hSsep y.2 z.2 hyz'
    have hdist : edist (y.1 - x) (z.1 - x) = edist y.1 z.1 := by
      simp [edist_dist, Real.dist_eq]
    have htri : edist (y.1 - x) (z.1 - x) ≤
        edist (y.1 - x) (center y : ℝ) + edist (center z : ℝ) (z.1 - x) := by
      calc
        edist (y.1 - x) (z.1 - x) ≤
            edist (y.1 - x) (center y : ℝ) + edist (center y : ℝ) (z.1 - x) :=
          edist_triangle _ _ _
        _ = edist (y.1 - x) (center y : ℝ) + edist (center z : ℝ) (z.1 - x) := by
          rw [hyz]
    have hupper : edist (y.1 - x) (z.1 - x) ≤ (2 : ℝ≥0∞) * ε := by
      calc
        edist (y.1 - x) (z.1 - x) ≤
            edist (y.1 - x) (center y : ℝ) + edist (center z : ℝ) (z.1 - x) := htri
        _ ≤ (ε : ℝ≥0∞) + ε := by
          gcongr
          · exact hcenter_close y
          · rw [edist_comm]
            exact hcenter_close z
        _ = (2 : ℝ≥0∞) * ε := (two_mul _).symm
    rw [hdist] at hupper
    have heq : (2 : ℝ≥0∞) * ε =
        ENNReal.ofReal (h / 2) := by
      calc
        (2 : ℝ≥0∞) * (ε : ℝ≥0∞) =
            (↑((2 : ℝ≥0) * ε) : ℝ≥0∞) := by norm_num
        _ = ENNReal.ofReal (((2 : ℝ≥0) * ε : ℝ≥0) : ℝ) :=
          ENNReal.coe_nnreal_eq _
        _ = ENNReal.ofReal (h / 2) := by
          congr 1
          change 2 * (h / 4) = h / 2
          ring
    exact (not_le_of_gt hsep) (heq ▸ hupper)
  have hSfin : S.Finite := by
    let _ : Fintype N := hNfin.fintype
    let _ : Finite S := Finite.of_injective center hcenter_inj
    exact Set.toFinite S
  have hcard : S.ncard ≤ N.ncard := by
    let _ : Fintype S := hSfin.fintype
    let _ : Fintype N := hNfin.fintype
    simpa using Fintype.card_le_of_injective center hcenter_inj
  exact ⟨hSfin, hcard⟩

/-- Bounded density is inherited by subsets. -/
lemma HasBoundedDensity.mono {A B : Set ℝ} (hAB : A ⊆ B) (hB : HasBoundedDensity B) :
    HasBoundedDensity A := by
  obtain ⟨C, hC⟩ := hB
  refine ⟨C, fun x ↦ ?_⟩
  have hsub : A ∩ Set.Ioo x (x + 1) ⊆ B ∩ Set.Ioo x (x + 1) :=
    inter_subset_inter hAB Subset.rfl
  exact ⟨(hC x).1.subset hsub, (Set.ncard_le_ncard hsub (hC x).1).trans (hC x).2⟩

/-- A union of two sets of bounded density has bounded density. -/
lemma HasBoundedDensity.union {A B : Set ℝ}
    (hA : HasBoundedDensity A) (hB : HasBoundedDensity B) :
    HasBoundedDensity (A ∪ B) := by
  obtain ⟨CA, hCA⟩ := hA
  obtain ⟨CB, hCB⟩ := hB
  refine ⟨CA + CB, fun x ↦ ?_⟩
  have heq : (A ∪ B) ∩ Set.Ioo x (x + 1) =
      (A ∩ Set.Ioo x (x + 1)) ∪ (B ∩ Set.Ioo x (x + 1)) := by
    ext y
    simp only [mem_inter_iff, mem_union]
    aesop
  rw [heq]
  constructor
  · exact (hCA x).1.union (hCB x).1
  · exact (Set.ncard_union_le _ _).trans (Nat.add_le_add (hCA x).2 (hCB x).2)

/-- Every finite set has bounded density. -/
lemma hasBoundedDensity_finite {E : Set ℝ} (hE : E.Finite) : HasBoundedDensity E := by
  refine ⟨E.ncard, fun x ↦ ?_⟩
  exact ⟨hE.inter_of_left _, Set.ncard_le_ncard inter_subset_left hE⟩

/-- A finite union of positive-step arithmetic progressions has bounded density. -/
lemma hasBoundedDensity_iUnion_arithmeticProgression
    {ι : Type*} [Fintype ι] (c h : ι → ℝ) (hh : ∀ i, 0 < h i) :
    HasBoundedDensity (⋃ i, arithmeticProgression (c i) (h i)) := by
  classical
  have aux : ∀ s : Finset ι,
      HasBoundedDensity (⋃ i ∈ s, arithmeticProgression (c i) (h i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using hasBoundedDensity_finite (Set.finite_empty : (∅ : Set ℝ).Finite)
    | @insert a s ha ih =>
        simpa [ha] using
          (hasBoundedDensity_arithmeticProgression (c a) (h a) (hh a)).union ih
  simpa using aux Finset.univ

/-- The exact final implication advertised in the proposed proof of Problem 4.1. -/
theorem hasBoundedDensity_of_subset_finite_union_arithmeticProgressions
    (Λ E : Set ℝ) (hE : E.Finite)
    {ι : Type*} [Fintype ι] (c h : ι → ℝ) (hh : ∀ i, 0 < h i)
    (hΛ : Λ ⊆ E ∪ ⋃ i, arithmeticProgression (c i) (h i)) :
    HasBoundedDensity Λ := by
  apply HasBoundedDensity.mono hΛ
  exact (hasBoundedDensity_finite hE).union
    (hasBoundedDensity_iUnion_arithmeticProgression c h hh)

/-- A finite arithmetic-progression cover implies bounded density. -/
theorem HasFiniteArithmeticProgressionCover.hasBoundedDensity {Λ : Set ℝ}
    (hΛ : HasFiniteArithmeticProgressionCover Λ) : HasBoundedDensity Λ := by
  obtain ⟨E, n, c, h, hE, hh, hsub⟩ := hΛ
  exact hasBoundedDensity_of_subset_finite_union_arithmeticProgressions
    Λ E hE c h hh hsub

end WeakTiling

end

end Root

/-! ## Step G: a positive integer coordinate basis for the interval lengths -/

section PositiveCoordinates

section

open Finset

namespace WeakTiling

/-- **Positive rational coordinates** with respect to a new positive, independent family. -/
theorem exists_positive_rational_coordinates {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (b : ι → ℝ) (hb : ∀ j, 0 < b j) (hind : LinearIndependent ℚ b) (ℓ : κ → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (q : κ → ι → ℚ) (hq : ∀ i, ℓ i = ∑ j, (q i j : ℝ) * b j) :
    ∃ (β : ι → ℝ) (x : κ → ι → ℚ), (∀ j, 0 < β j) ∧ LinearIndependent ℚ β ∧
      (∀ i j, 0 < x i j) ∧ (∀ i, ℓ i = ∑ j, (x i j : ℝ) * β j) ∧
      ∀ j, ∃ a : ι → ℚ, β j = ∑ k, (a k : ℝ) * b k := by
  classical
  -- constants
  set B : ℝ := ∑ j, b j with hB
  have hBpos : 0 < B := Finset.sum_pos (fun j _ ↦ hb j) univ_nonempty
  set Q : ℝ := ∑ i, ∑ j, |(q i j : ℝ)| + 1 with hQ
  have hQpos : 0 < Q := by positivity
  have hqQ : ∀ i j, |(q i j : ℝ)| ≤ Q - 1 := by
    intro i j
    have h1 := single_le_sum (fun j _ ↦ abs_nonneg ((q i j : ℝ))) (mem_univ j)
    have h2 := single_le_sum (f := fun i ↦ ∑ j, |(q i j : ℝ)|)
      (fun i _ ↦ sum_nonneg fun j _ ↦ abs_nonneg _) (mem_univ i)
    rw [hQ]; linarith
  obtain ⟨L, hLpos, hLle⟩ : ∃ L > 0, ∀ i, L ≤ ℓ i := by
    rcases isEmpty_or_nonempty κ with h | h
    · exact ⟨1, one_pos, fun i ↦ isEmptyElim i⟩
    · obtain ⟨i0, _, hmin⟩ := univ.exists_min_image ℓ univ_nonempty
      exact ⟨ℓ i0, hℓ i0, fun i ↦ hmin i (mem_univ i)⟩
  set G : ℝ := 3 * Q * B / L with hG
  have hGpos : 0 < G := by positivity
  set η : ℝ := min (1 / 2) (min (L / (2 * Q * B)) (1 / (4 * G + 4))) with hη
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hη2 : η ≤ L / (2 * Q * B) := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ 1 / (4 * G + 4) := (min_le_right _ _).trans (min_le_right _ _)
  -- rational approximations
  have hψex : ∀ j, ∃ r : ℚ, b j * (1 - η) < r ∧ (r : ℝ) < b j * (1 + η) := fun j ↦
    exists_rat_btwn (by nlinarith [hb j])
  choose ψ hψlo hψhi using hψex
  have hwin : G / (1 + G) < (1 - η) / (1 + η) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : η * (4 * G + 4) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hη3
      linarith
    nlinarith
  obtain ⟨t, htlo, hthi⟩ := exists_rat_btwn hwin
  have ht0 : (0 : ℝ) < t := lt_trans (by positivity) htlo
  have ht1 : (t : ℝ) < 1 := by
    have : (1 - η) / (1 + η) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  -- the rational quantities
  set S : ℚ := ∑ j, ψ j with hS
  set Ψ : κ → ℚ := fun i ↦ ∑ j, q i j * ψ j with hΨ
  have hSr : (S : ℝ) = ∑ j, (ψ j : ℝ) := by rw [hS]; push_cast; rfl
  have hSlo : (1 - η) * B ≤ S := by
    rw [hSr, hB, Finset.mul_sum]
    exact sum_le_sum fun j _ ↦ by linarith [hψlo j]
  have hShi : (S : ℝ) ≤ (1 + η) * B := by
    rw [hSr, hB, Finset.mul_sum]
    exact sum_le_sum fun j _ ↦ by linarith [hψhi j]
  have hSpos : (0 : ℝ) < S := lt_of_lt_of_le (by nlinarith) hSlo
  have hΨlo : ∀ i, ℓ i / 2 ≤ (Ψ i : ℝ) := by
    intro i
    have hΨr : (Ψ i : ℝ) = ∑ j, (q i j : ℝ) * ψ j := by rw [hΨ]; push_cast; rfl
    have hdiff : |(Ψ i : ℝ) - ℓ i| ≤ η * (Q * B) := by
      rw [hΨr, hq i, ← sum_sub_distrib]
      calc |∑ j, ((q i j : ℝ) * ψ j - q i j * b j)|
          ≤ ∑ j, |(q i j : ℝ) * ψ j - q i j * b j| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, Q * (η * b j) := sum_le_sum fun j _ ↦ by
            rw [← mul_sub, abs_mul]
            have h1 : |(ψ j : ℝ) - b j| ≤ η * b j := by
              rw [abs_le]; constructor <;> nlinarith [hψlo j, hψhi j]
            have h2 : |(q i j : ℝ)| ≤ Q := by linarith [hqQ i j]
            exact mul_le_mul h2 h1 (abs_nonneg _) hQpos.le
        _ = η * (Q * B) := by rw [← Finset.mul_sum, ← Finset.mul_sum, hB]; ring
    have hηQB : η * (Q * B) ≤ L / 2 := by
      rw [le_div_iff₀ (by positivity)] at hη2
      nlinarith
    have := (abs_le.mp hdiff).1
    linarith [hLle i]
  set γ : ℚ := t / (1 - t) with hγ
  have hγr : (γ : ℝ) = t / (1 - t) := by rw [hγ]; push_cast; ring
  have hγG : G < γ := by
    rw [hγr, lt_div_iff₀ (by linarith)]
    rw [div_lt_iff₀ (by positivity)] at htlo
    linarith
  set x : κ → ι → ℚ := fun i j ↦ q i j + γ * Ψ i / S with hx
  set β : ι → ℝ := fun j ↦ b j - (t * ψ j / S : ℚ) * B with hβ
  refine ⟨β, x, ?_, ?_, ?_, ?_, ?_⟩
  · -- positivity of `β`
    intro j
    simp only [hβ]
    push_cast
    have hkey : (t : ℝ) * ψ j * B < b j * S := by
      have h1 : (t : ℝ) * ψ j * B ≤ t * (b j * (1 + η)) * B := by
        have := (hψhi j).le
        have : (t : ℝ) * ψ j ≤ t * (b j * (1 + η)) := mul_le_mul_of_nonneg_left this ht0.le
        exact mul_le_mul_of_nonneg_right this hBpos.le
      have h2 : b j * ((1 - η) * B) ≤ b j * S := mul_le_mul_of_nonneg_left hSlo (hb j).le
      have h3 : (t : ℝ) * (1 + η) < 1 - η := by
        rw [lt_div_iff₀ (by positivity)] at hthi
        linarith
      have h4 : (t : ℝ) * (b j * (1 + η)) * B < b j * ((1 - η) * B) := by
        have := mul_lt_mul_of_pos_left h3 (mul_pos (hb j) hBpos)
        nlinarith
      linarith
    have : (t : ℝ) * ψ j / S * B < b j := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hSpos]
      linarith
    linarith
  · -- linear independence
    rw [Fintype.linearIndependent_iff] at hind ⊢
    intro g hg
    set ρ : ℚ := ∑ j, g j * ψ j with hρ
    have hsum : ∑ k, (g k - t * ρ / S) • b k = 0 := by
      have hρr : (ρ : ℝ) = ∑ j, (g j : ℝ) * ψ j := by rw [hρ]; push_cast; rfl
      simp only [Rat.smul_def] at hg ⊢
      rw [← hg]
      simp only [hβ]
      push_cast
      simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
      congr 1
      have e1 : ∑ x, (t : ℝ) * ρ / S * b x = (t : ℝ) * ρ / S * B := by
        rw [hB, Finset.mul_sum]
      have e2 : ∑ x, (g x : ℝ) * ((t : ℝ) * ψ x / S * B) = (t : ℝ) / S * B * ρ := by
        rw [hρr, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ ↦ by ring
      rw [e1, e2]
      ring
    have hc := hind _ hsum
    have hgk : ∀ k, g k = t * ρ / S := fun k ↦ sub_eq_zero.mp (hc k)
    have hρ0 : ρ = 0 := by
      have hρeq : ρ = t * ρ := by
        have hSq : (S : ℚ) ≠ 0 := by exact_mod_cast hSpos.ne'
        calc ρ = ∑ j, t * ρ / S * ψ j := by rw [hρ]; exact sum_congr rfl fun j _ ↦ by rw [hgk j]
          _ = t * ρ / S * S := by rw [← Finset.mul_sum]
          _ = t * ρ := by field_simp
      have ht1q : (t : ℚ) ≠ 1 := by
        intro h
        have : (t : ℝ) = 1 := by exact_mod_cast h
        linarith
      have : ρ * (1 - t) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd (by linarith : (t : ℚ) = 1) ht1q
    intro k
    rw [hgk k, hρ0, mul_zero, zero_div]
  · -- positivity of the new coordinates
    intro i j
    have hΨS : L / (3 * B) ≤ (Ψ i : ℝ) / S := by
      rw [div_le_div_iff₀ (by positivity) hSpos]
      have h1 : L / 2 ≤ (Ψ i : ℝ) := le_trans (by linarith [hLle i]) (hΨlo i)
      have h2 : (S : ℝ) ≤ 3 / 2 * B := by nlinarith
      nlinarith
    have hQlt : Q < (γ : ℝ) * ((Ψ i : ℝ) / S) := by
      have hGL : G * (L / (3 * B)) = Q := by rw [hG]; field_simp
      calc Q = G * (L / (3 * B)) := hGL.symm
        _ < γ * (L / (3 * B)) := mul_lt_mul_of_pos_right hγG (by positivity)
        _ ≤ γ * ((Ψ i : ℝ) / S) :=
            mul_le_mul_of_nonneg_left hΨS (le_trans hGpos.le hγG.le)
    have hqlo : -(Q - 1) ≤ (q i j : ℝ) := (abs_le.mp (hqQ i j)).1
    have : (0 : ℝ) < x i j := by
      simp only [hx]
      push_cast
      rw [mul_div_assoc]
      linarith
    exact_mod_cast this
  · -- the coordinate identity
    intro i
    have hΨr : (Ψ i : ℝ) = ∑ j, (q i j : ℝ) * ψ j := by rw [hΨ]; push_cast; rfl
    simp only [hx, hβ]
    push_cast
    have hSne : (S : ℝ) ≠ 0 := hSpos.ne'
    have ht1 : (1 : ℝ) - t ≠ 0 := by linarith
    have e1 : ∑ j, ((q i j : ℝ) + γ * Ψ i / S) * (b j - t * ψ j / S * B) =
        ∑ j, (q i j : ℝ) * b j - t / S * B * ∑ j, (q i j : ℝ) * ψ j +
          γ * Ψ i / S * ∑ j, b j - γ * Ψ i / S * (t / S * B) * ∑ j, (ψ j : ℝ) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [e1, ← hq i, ← hΨr, ← hB, ← hSr, hγr]
    field_simp
    ring
  · -- `β` lies in the span of `b`
    intro j
    refine ⟨fun k ↦ (if k = j then 1 else 0) - t * ψ j / S, ?_⟩
    simp only [hβ]
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hB]
    congr 1
    rw [Finset.sum_eq_single j (fun k _ hk ↦ by simp [hk]) (by simp)]
    simp

/-- **Positive integer coordinates for the interval lengths (step G).**

For finitely many positive reals `ℓᵢ` there is a finite family `βⱼ > 0`.  It is linearly
independent over `ℚ` and contained in the `ℚ`-span of the `ℓᵢ`, and every `ℓᵢ` is a
combination of the `βⱼ` with **positive integer** coefficients `nᵢⱼ ≥ 1`. -/
theorem exists_positive_integer_coordinates {κ : Type*} [Fintype κ] (ℓ : κ → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) :
    ∃ (ι : Type) (_ : Fintype ι) (β : ι → ℝ) (n : κ → ι → ℕ),
      (∀ j, 0 < β j) ∧ LinearIndependent ℚ β ∧
      (∀ j, β j ∈ Submodule.span ℚ (Set.range ℓ)) ∧
      (∀ i j, 1 ≤ n i j) ∧ ∀ i, ℓ i = ∑ j, (n i j : ℝ) * β j := by
  classical
  obtain ⟨bs, hsub, hspan, hli⟩ := exists_linearIndependent ℚ (Set.range ℓ)
  have hfin : bs.Finite := (Set.finite_range ℓ).subset hsub
  let _ : Fintype bs := hfin.fintype
  have hbpos : ∀ j : bs, 0 < (j : ℝ) := fun j ↦ by
    obtain ⟨i, hi⟩ := hsub j.2
    rw [← hi]
    exact hℓ i
  have hmem : ∀ i, ∃ c : bs → ℚ, ∑ j, c j • (j : ℝ) = ℓ i := by
    intro i
    have : ℓ i ∈ Submodule.span ℚ (Set.range ((↑) : bs → ℝ)) := by
      rw [Subtype.range_coe, hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).mp this
  choose q hq using hmem
  have hq' : ∀ i, ℓ i = ∑ j, (q i j : ℝ) * (j : ℝ) := fun i ↦ by
    rw [← hq i]
    simp [Rat.smul_def]
  rcases isEmpty_or_nonempty bs with hemp | hne
  · -- no lengths at all
    have hκ : IsEmpty κ := ⟨fun i ↦ by
      have := hq' i
      rw [Finset.univ_eq_empty, Finset.sum_empty] at this
      exact (hℓ i).ne' this⟩
    refine ⟨bs, inferInstance, fun j ↦ (j : ℝ), fun _ _ ↦ 1, hbpos, hli,
      fun j ↦ Submodule.subset_span (hsub j.2), fun i ↦ isEmptyElim i, fun i ↦ isEmptyElim i⟩
  obtain ⟨β', x, hβpos, hβind, hxpos, hid, hspanβ⟩ :=
    exists_positive_rational_coordinates (fun j : bs ↦ (j : ℝ)) hbpos hli ℓ hℓ q hq'
  -- clear denominators
  set D : ℕ := ∏ p : κ × bs, (x p.1 p.2).den with hD
  have hdvd : ∀ i j, (x i j).den ∣ D := fun i j ↦
    Finset.dvd_prod_of_mem (fun p : κ × bs ↦ (x p.1 p.2).den) (Finset.mem_univ (i, j))
  have hDpos : 0 < D := Finset.prod_pos fun p _ ↦ (x p.1 p.2).den_pos
  set n : κ → bs → ℕ := fun i j ↦ (x i j).num.toNat * (D / (x i j).den) with hn
  have hnum : ∀ i j, 0 < (x i j).num := fun i j ↦ Rat.num_pos.mpr (hxpos i j)
  have hncast : ∀ i j, (n i j : ℝ) = (x i j : ℝ) * D := by
    intro i j
    have hden : ((x i j).den : ℚ) ≠ 0 := by exact_mod_cast (x i j).den_nz
    have h1 : ((x i j).num.toNat : ℚ) = (x i j).num := by
      exact_mod_cast Int.toNat_of_nonneg (hnum i j).le
    have h2 : ((D / (x i j).den : ℕ) : ℚ) = D / (x i j).den := by
      rw [Nat.cast_div (hdvd i j) hden]
    have h3 : ((x i j).num : ℚ) = x i j * (x i j).den := (Rat.mul_den_eq_num _).symm
    have : (n i j : ℚ) = x i j * D := by
      simp only [hn]
      push_cast
      rw [h1, h2, h3]
      field_simp
    exact_mod_cast this
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hDpos.ne'
  refine ⟨bs, inferInstance, fun j ↦ β' j / D, n, fun j ↦ div_pos (hβpos j) (by positivity),
    ?_, ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff] at hβind ⊢
    intro g hg
    apply hβind g
    have : ∑ j, g j • β' j = (D : ℝ) * ∑ j, g j • (β' j / D) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [Rat.smul_def]
      field_simp
    rw [this, hg, mul_zero]
  · intro j
    obtain ⟨a, ha⟩ := hspanβ j
    have hβmem : β' j ∈ Submodule.span ℚ (Set.range ℓ) := by
      rw [ha]
      refine Submodule.sum_mem _ fun k _ ↦ ?_
      rw [← Rat.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hsub k.2))
    have : β' j / D = ((1 / D : ℚ)) • β' j := by
      rw [Rat.smul_def]
      push_cast
      ring
    show β' j / D ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ hβmem
  · intro i j
    have h1 : 1 ≤ (x i j).num.toNat := by
      have := hnum i j
      omega
    have h2 : 1 ≤ D / (x i j).den :=
      Nat.div_pos (Nat.le_of_dvd hDpos (hdvd i j)) (x i j).den_pos
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · intro i
    rw [hid i]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hncast]
    field_simp

end WeakTiling

end

end PositiveCoordinates

/-! ## Step M: endpoint structure of finite interval covers (Theorem 3.3 of the source paper) -/

section IntervalCover

section

open Finset

namespace WeakTiling

/-- `z` is a nonnegative integer combination of the lengths `len`. -/
def InSemigroup {J : Type*} [Fintype J] (len : J → ℝ) (z : ℝ) : Prop :=
  ∃ n : J → ℕ, z = ∑ j, (n j : ℝ) * len j

theorem InSemigroup.zero {J : Type*} [Fintype J] (len : J → ℝ) : InSemigroup len 0 :=
  ⟨0, by simp⟩

/-- Every point is isolated from the other points of a finite set. -/
theorem exists_isolation (F : Finset ℝ) (e : ℝ) :
    ∃ δ > 0, ∀ p ∈ F, p ≠ e → δ ≤ |p - e| := by
  classical
  set T := insert (1 : ℝ) ((F.erase e).image fun p ↦ |p - e|) with hT
  have hTne : T.Nonempty := insert_nonempty _ _
  refine ⟨T.min' hTne, ?_, fun p hp hpe ↦ ?_⟩
  · have hpos : ∀ y ∈ T, 0 < y := by
      intro y hy
      rw [hT, mem_insert, mem_image] at hy
      rcases hy with h | ⟨p, hp, hpe⟩
      · rw [h]; exact one_pos
      · rw [← hpe]
        exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_mem_erase hp))
    exact hpos _ (T.min'_mem hTne)
  · exact T.min'_le _ (mem_insert_of_mem (mem_image.mpr ⟨p, mem_erase.mpr ⟨hpe, hp⟩, rfl⟩))

end WeakTiling

end

end IntervalCover

/-! ## Step M: Theorem 3.3 of the source paper for infinite covers -/

section InfiniteCover

section

open Finset MeasureTheory

namespace WeakTiling

/-- **Tail control.**  For summable nonnegative weights and `δ > 0` there is a finite set `T`
such that every `[0,1]`-valued `r` vanishing on `T` has `∑ wⱼ rⱼ < δ`. -/
theorem exists_finset_tail {ι : Type*} (w : ι → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hs : Summable w)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : Finset ι, ∀ r : ι → ℝ, (∀ j, 0 ≤ r j ∧ r j ≤ 1) → (∀ j ∈ T, r j = 0) →
      ∑' j, w j * r j < δ := by
  classical
  obtain ⟨T, hT⟩ := (hs.hasSum.eventually (lt_mem_nhds (by linarith :
    ∑' j, w j - δ < ∑' j, w j))).exists
  refine ⟨T, fun r hr hrT ↦ ?_⟩
  set ind : ι → ℝ := fun j ↦ if j ∈ T then w j else 0 with hind
  have hwr : Summable fun j ↦ w j * r j :=
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (hw0 j) (hr j).1)
      (fun j ↦ by nlinarith [hw0 j, (hr j).1, (hr j).2]) hs
  have hind_s : Summable ind :=
    Summable.of_nonneg_of_le (fun j ↦ by simp only [hind]; split_ifs <;> linarith [hw0 j])
      (fun j ↦ by simp only [hind]; split_ifs <;> linarith [hw0 j]) hs
  have hsum_ind : ∑' j, ind j = ∑ j ∈ T, w j := by
    rw [tsum_eq_sum (s := T) (fun j hj ↦ by simp [hind, hj])]
    exact sum_congr rfl fun j hj ↦ by simp [hind, hj]
  have hle : ∑' j, (w j * r j + ind j) ≤ ∑' j, w j :=
    Summable.tsum_le_tsum (fun j ↦ by
      simp only [hind]
      split_ifs with hj
      · rw [hrT j hj]; simp
      · nlinarith [hw0 j, (hr j).2]) (hwr.add hind_s) hs
  rw [hwr.tsum_add hind_s, hsum_ind] at hle
  linarith

section

variable {ι : Type*} {a b : ℝ} {c len w : ι → ℝ}

/-- The infinite cover sum `∑ⱼ wⱼ 1_{(cⱼ, cⱼ+ℓⱼ)}(x)`. -/
noncomputable def coverTsum (c len w : ι → ℝ) (x : ℝ) : ℝ :=
  ∑' j, if c j < x ∧ x < c j + len j then w j else 0

theorem summable_coverTerm (hw : ∀ j, 0 < w j) (hs : Summable w) (x : ℝ) :
    Summable fun j ↦ if c j < x ∧ x < c j + len j then w j else 0 :=
  Summable.of_nonneg_of_le (fun j ↦ by split_ifs <;> linarith [hw j])
    (fun j ↦ by split_ifs <;> linarith [hw j]) hs

theorem coverTsum_ge (hw : ∀ j, 0 < w j) (hs : Summable w) {x : ℝ} (k : ι)
    (hk : c k < x ∧ x < c k + len k) : w k ≤ coverTsum c len w x := by
  have := (summable_coverTerm (c := c) (len := len) hw hs x).le_tsum k
    (fun j _ ↦ by split_ifs <;> linarith [hw j])
  simp only [hk, and_self, ite_true] at this
  exact this

/-- An a.e.-good point in every nonempty open interval. -/
theorem exists_good_point (hae : ∀ᵐ x ∂(volume : Measure ℝ),
    coverTsum c len w x = if a < x ∧ x < b then 1 else 0) {u v : ℝ} (huv : u < v) :
    ∃ x, u < x ∧ x < v ∧ coverTsum c len w x = if a < x ∧ x < b then 1 else 0 := by
  have hpos : (volume : Measure ℝ) (Set.Ioo u v) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  obtain ⟨x, hx, hgood⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hae)
  exact ⟨x, hx.1, hx.2, hgood⟩

/-- No interval starts to the left of `a`. -/
theorem le_start_inf (hae : ∀ᵐ x ∂(volume : Measure ℝ),
    coverTsum c len w x = if a < x ∧ x < b then 1 else 0)
    (hw : ∀ j, 0 < w j) (hs : Summable w) (hlen : ∀ j, 0 < len j) (j : ι) : a ≤ c j := by
  by_contra h
  push Not at h
  obtain ⟨x, hx1, hx2, hgood⟩ := exists_good_point hae
    (lt_min h (by linarith [hlen j]) : c j < min a (c j + len j))
  rw [ite_eq_right (fun h' ↦ by linarith [h'.1, min_le_left a (c j + len j), hx2])] at hgood
  have := coverTsum_ge hw hs j ⟨hx1, lt_of_lt_of_le hx2 (min_le_right _ _)⟩
  linarith [hw j]

/-- No interval ends to the right of `b`. -/
theorem end_le_inf (hae : ∀ᵐ x ∂(volume : Measure ℝ),
    coverTsum c len w x = if a < x ∧ x < b then 1 else 0)
    (hw : ∀ j, 0 < w j) (hs : Summable w) (hlen : ∀ j, 0 < len j) (j : ι) :
    c j + len j ≤ b := by
  by_contra h
  push Not at h
  obtain ⟨x, hx1, hx2, hgood⟩ := exists_good_point hae
    (max_lt h (by linarith [hlen j]) : max b (c j) < c j + len j)
  rw [ite_eq_right (fun h' ↦ by linarith [h'.2, le_max_left b (c j), hx1])] at hgood
  have := coverTsum_ge hw hs j ⟨lt_of_le_of_lt (le_max_right _ _) hx1, hx2⟩
  linarith [hw j]

/-- **Jump cancellation for infinite covers.**  An interval starting at `e ∈ (a, b)` forces an
interval ending at `e`. -/
theorem exists_end_of_start_inf (hae : ∀ᵐ x ∂(volume : Measure ℝ),
    coverTsum c len w x = if a < x ∧ x < b then 1 else 0)
    (hw : ∀ j, 0 < w j) (hs : Summable w) {ℓmin : ℝ} (hℓ : 0 < ℓmin)
    (hlen : ∀ j, ℓmin ≤ len j) (k : ι) (hak : a < c k) (hkb : c k < b) :
    ∃ i, c i + len i = c k := by
  classical
  by_contra hno
  push Not at hno
  set e := c k with he
  obtain ⟨T, hT⟩ := exists_finset_tail w (fun j ↦ (hw j).le) hs (hw k)
  obtain ⟨ε₀, hε₀, hiso⟩ :=
    exists_isolation (T.image c ∪ T.image fun j ↦ c j + len j) e
  set ε := min (min ε₀ ℓmin) (min (e - a) (b - e)) / 2 with hεdef
  have hmin_pos : 0 < min (min ε₀ ℓmin) (min (e - a) (b - e)) :=
    lt_min (lt_min hε₀ hℓ) (lt_min (by linarith) (by linarith))
  have hε : 0 < ε := by positivity
  have hεε₀ : ε < ε₀ := by
    have := min_le_left (min ε₀ ℓmin) (min (e - a) (b - e))
    have := min_le_left ε₀ ℓmin
    linarith
  have hεℓ : ε < ℓmin := by
    have := min_le_left (min ε₀ ℓmin) (min (e - a) (b - e))
    have := min_le_right ε₀ ℓmin
    linarith
  have hεa : ε < e - a := by
    have := min_le_right (min ε₀ ℓmin) (min (e - a) (b - e))
    have := min_le_left (e - a) (b - e)
    linarith
  have hεb : ε < b - e := by
    have := min_le_right (min ε₀ ℓmin) (min (e - a) (b - e))
    have := min_le_right (e - a) (b - e)
    linarith
  obtain ⟨x, hx1, hx2, hgx⟩ := exists_good_point hae (by linarith : e < e + ε)
  obtain ⟨x', hx'1, hx'2, hgx'⟩ := exists_good_point hae (by linarith : e - ε < e)
  rw [ite_eq_left ⟨by linarith, by linarith⟩] at hgx hgx'
  -- the remainder indicator
  set r : ι → ℝ := fun j ↦
    if (c j ≠ e ∧ |c j - e| < ε) ∨ (c j + len j ≠ e ∧ |c j + len j - e| < ε) then 1 else 0
    with hr
  have hr01 : ∀ j, 0 ≤ r j ∧ r j ≤ 1 := fun j ↦ by
    simp only [hr]; split_ifs <;> norm_num
  have hrT : ∀ j ∈ T, r j = 0 := by
    intro j hj
    simp only [hr]
    rw [ite_eq_right]
    rintro (⟨hne, hlt⟩ | ⟨hne, hlt⟩)
    · have := hiso (c j) (mem_union_left _ (mem_image_of_mem _ hj)) hne
      linarith
    · have := hiso (c j + len j) (mem_union_right _ (mem_image_of_mem (fun j ↦ c j + len j) hj))
        hne
      linarith
  have hR := hT r hr01 hrT
  -- termwise comparison
  set g : ι → ℝ := fun j ↦ (if c j < x ∧ x < c j + len j then w j else 0) -
    (if c j < x' ∧ x' < c j + len j then w j else 0) with hg
  set h : ι → ℝ := fun j ↦ (if j = k then w k else 0) - w j * r j with hh
  have hkact : c k < x ∧ x < c k + len k := ⟨by linarith, by linarith [hlen k]⟩
  have hkact' : ¬ (c k < x' ∧ x' < c k + len k) := fun h' ↦ by linarith [h'.1]
  have hgh : ∀ j, h j ≤ g j := by
    intro j
    simp only [hh, hg]
    by_cases hcond : (c j ≠ e ∧ |c j - e| < ε) ∨ (c j + len j ≠ e ∧ |c j + len j - e| < ε)
    · have hrj : r j = 1 := by simp only [hr]; rw [ite_eq_left hcond]
      rw [hrj, mul_one]
      by_cases hjk : j = k
      · subst hjk
        rw [ite_eq_left rfl, ite_eq_left hkact, ite_eq_right hkact']
        linarith [hw j]
      · rw [ite_eq_right hjk]
        split_ifs <;> linarith [hw j]
    · have hrj : r j = 0 := by simp only [hr]; rw [ite_eq_right hcond]
      rw [hrj, mul_zero, sub_zero]
      push Not at hcond
      obtain ⟨hc1, hc2⟩ := hcond
      have hend : ε ≤ |c j + len j - e| := hc2 (hno j)
      by_cases hce : c j = e
      · have hact : c j < x ∧ x < c j + len j := ⟨by linarith, by linarith [hlen j]⟩
        have hact' : ¬ (c j < x' ∧ x' < c j + len j) := fun h' ↦ by linarith [h'.1]
        rw [ite_eq_left hact, ite_eq_right hact', sub_zero]
        split_ifs with hjk
        · subst hjk; exact le_rfl
        · exact (hw j).le
      · have hcfar : ε ≤ |c j - e| := hc1 hce
        have hjk : j ≠ k := fun h' ↦ hce (h' ▸ rfl)
        rw [ite_eq_right hjk]
        have h1 : c j < x ↔ c j < x' := by
          rcases le_abs'.mp hcfar with h' | h' <;> constructor <;> intro _ <;> linarith
        have h2 : x < c j + len j ↔ x' < c j + len j := by
          rcases le_abs'.mp hend with h' | h' <;> constructor <;> intro _ <;> linarith
        simp only [h1, h2, sub_self, le_refl]
  -- sum up
  have hsx := summable_coverTerm (c := c) (len := len) hw hs x
  have hsx' := summable_coverTerm (c := c) (len := len) hw hs x'
  have hwr : Summable fun j ↦ w j * r j :=
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (hw j).le (hr01 j).1)
      (fun j ↦ by nlinarith [hw j, (hr01 j).1, (hr01 j).2]) hs
  have hsite : Summable fun j ↦ if j = k then w k else 0 :=
    summable_of_ne_finset_zero (s := {k}) (fun j hj ↦ by simp at hj; simp [hj])
  have hsumg : ∑' j, g j = 0 := by
    simp only [hg]
    rw [hsx.tsum_sub hsx']
    change coverTsum c len w x - coverTsum c len w x' = 0
    rw [hgx, hgx', sub_self]
  have hsumh : ∑' j, h j = w k - ∑' j, w j * r j := by
    simp only [hh]
    rw [hsite.tsum_sub hwr, tsum_ite_eq]
  have hle : ∑' j, h j ≤ ∑' j, g j :=
    Summable.tsum_le_tsum hgh (hsite.sub hwr) (hsx.sub hsx')
  linarith

/-- **Right end for infinite covers.**  Some interval ends exactly at `b`. -/
theorem exists_end_at_right_inf (hae : ∀ᵐ x ∂(volume : Measure ℝ),
    coverTsum c len w x = if a < x ∧ x < b then 1 else 0)
    (hw : ∀ j, 0 < w j) (hs : Summable w) (hlen : ∀ j, 0 < len j) (hab : a < b) :
    ∃ i, c i + len i = b := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨T, hT⟩ := exists_finset_tail w (fun j ↦ (hw j).le) hs (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨ε₀, hε₀, hiso⟩ :=
    exists_isolation (T.image c ∪ T.image fun j ↦ c j + len j) b
  set ε := min ε₀ (b - a) / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hεε₀ : ε < ε₀ := by have := min_le_left ε₀ (b - a); linarith
  have hεb : ε < b - a := by have := min_le_right ε₀ (b - a); linarith
  obtain ⟨x, hx1, hx2, hgx⟩ := exists_good_point hae (by linarith : b < b + ε)
  obtain ⟨x', hx'1, hx'2, hgx'⟩ := exists_good_point hae (by linarith : b - ε < b)
  rw [ite_eq_right (fun h' ↦ by linarith [h'.2])] at hgx
  rw [ite_eq_left ⟨by linarith, by linarith⟩] at hgx'
  set r : ι → ℝ := fun j ↦
    if (c j ≠ b ∧ |c j - b| < ε) ∨ (c j + len j ≠ b ∧ |c j + len j - b| < ε) then 1 else 0
    with hr
  have hr01 : ∀ j, 0 ≤ r j ∧ r j ≤ 1 := fun j ↦ by
    simp only [hr]; split_ifs <;> norm_num
  have hrT : ∀ j ∈ T, r j = 0 := by
    intro j hj
    simp only [hr]
    rw [ite_eq_right]
    rintro (⟨hne, hlt⟩ | ⟨hne, hlt⟩)
    · have := hiso (c j) (mem_union_left _ (mem_image_of_mem _ hj)) hne
      linarith
    · have := hiso (c j + len j) (mem_union_right _ (mem_image_of_mem (fun j ↦ c j + len j) hj))
        hne
      linarith
  have hR := hT r hr01 hrT
  set g : ι → ℝ := fun j ↦ (if c j < x' ∧ x' < c j + len j then w j else 0) -
    (if c j < x ∧ x < c j + len j then w j else 0) with hg
  have hgle : ∀ j, g j ≤ w j * r j := by
    intro j
    simp only [hg]
    by_cases hcond : (c j ≠ b ∧ |c j - b| < ε) ∨ (c j + len j ≠ b ∧ |c j + len j - b| < ε)
    · have hrj : r j = 1 := by simp only [hr]; rw [ite_eq_left hcond]
      rw [hrj, mul_one]
      split_ifs <;> linarith [hw j]
    · have hrj : r j = 0 := by simp only [hr]; rw [ite_eq_right hcond]
      rw [hrj, mul_zero]
      push Not at hcond
      obtain ⟨hc1, hc2⟩ := hcond
      have hend : ε ≤ |c j + len j - b| := hc2 (hno j)
      have hcb : c j ≠ b := by
        intro h'
        have := end_le_inf hae hw hs hlen j
        linarith [hlen j]
      have hcfar : ε ≤ |c j - b| := hc1 hcb
      have h1 : c j < x' ↔ c j < x := by
        rcases le_abs'.mp hcfar with h' | h' <;> constructor <;> intro _ <;> linarith
      have h2 : x' < c j + len j ↔ x < c j + len j := by
        rcases le_abs'.mp hend with h' | h' <;> constructor <;> intro _ <;> linarith
      simp only [h1, h2, sub_self, le_refl]
  have hsx := summable_coverTerm (c := c) (len := len) hw hs x
  have hsx' := summable_coverTerm (c := c) (len := len) hw hs x'
  have hwr : Summable fun j ↦ w j * r j :=
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (hw j).le (hr01 j).1)
      (fun j ↦ by nlinarith [hw j, (hr01 j).1, (hr01 j).2]) hs
  have hsumg : ∑' j, g j = 1 := by
    simp only [hg]
    rw [hsx'.tsum_sub hsx]
    change coverTsum c len w x' - coverTsum c len w x = 1
    rw [hgx, hgx', sub_zero]
  have hle : ∑' j, g j ≤ ∑' j, w j * r j :=
    Summable.tsum_le_tsum hgle (hsx'.sub hsx) hwr
  linarith

/-- Nonnegative integer combinations of a finite set of lengths. -/
def InSemigroupL (L : Finset ℝ) (z : ℝ) : Prop :=
  ∃ n : L → ℕ, z = ∑ l : L, (n l : ℝ) * l

theorem InSemigroupL.zero (L : Finset ℝ) : InSemigroupL L 0 := ⟨0, by simp⟩

theorem InSemigroupL.add_mem {L : Finset ℝ} {z l : ℝ} (hz : InSemigroupL L z) (hl : l ∈ L) :
    InSemigroupL L (z + l) := by
  classical
  obtain ⟨n, rfl⟩ := hz
  refine ⟨n + Pi.single ⟨l, hl⟩ 1, ?_⟩
  simp only [Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single (⟨l, hl⟩ : L) (fun j _ hj ↦ by simp [Pi.single_apply, hj]) (by simp)]
  simp

/-- **Theorem 3.3 (infinite covers), endpoints.**  Every start point lies in `a + ℕ·L`. -/
theorem start_mem_semigroup_inf (hae : ∀ᵐ x ∂(volume : Measure ℝ),
    coverTsum c len w x = if a < x ∧ x < b then 1 else 0)
    (hw : ∀ j, 0 < w j) (hs : Summable w) {ℓmin : ℝ} (hℓ : 0 < ℓmin)
    (hlen : ∀ j, ℓmin ≤ len j) (L : Finset ℝ) (hL : ∀ j, len j ∈ L) (j : ι) :
    InSemigroupL L (c j - a) := by
  have hlenpos : ∀ j, 0 < len j := fun j ↦ lt_of_lt_of_le hℓ (hlen j)
  suffices H : ∀ N : ℕ, ∀ j, c j - a < (N + 1) * ℓmin → InSemigroupL L (c j - a) by
    obtain ⟨N, hN⟩ := exists_nat_gt ((c j - a) / ℓmin)
    exact H N j (by rw [div_lt_iff₀ hℓ] at hN; nlinarith)
  intro N
  induction N with
  | zero =>
    intro j hj
    rcases (le_start_inf hae hw hs hlenpos j).lt_or_eq with hlt | heq
    · obtain ⟨i, hi⟩ := exists_end_of_start_inf hae hw hs hℓ hlen j hlt
        (by linarith [end_le_inf hae hw hs hlenpos j, hlenpos j])
      have := le_start_inf hae hw hs hlenpos i
      have := hlen i
      push_cast at hj
      linarith
    · rw [← heq, sub_self]; exact InSemigroupL.zero L
  | succ N ih =>
    intro j hj
    rcases (le_start_inf hae hw hs hlenpos j).lt_or_eq with hlt | heq
    · obtain ⟨i, hi⟩ := exists_end_of_start_inf hae hw hs hℓ hlen j hlt
        (by linarith [end_le_inf hae hw hs hlenpos j, hlenpos j])
      have hi' : c i - a < (N + 1) * ℓmin := by
        have := hlen i
        push_cast at hj
        linarith
      have := (ih i hi').add_mem (hL i)
      rwa [show c i - a + len i = c j - a by linarith] at this
    · rw [← heq, sub_self]; exact InSemigroupL.zero L

/-- **Theorem 3.3 (infinite covers), length.**  `b - a ∈ ℕ·L`. -/
theorem length_mem_semigroup_inf (hae : ∀ᵐ x ∂(volume : Measure ℝ),
    coverTsum c len w x = if a < x ∧ x < b then 1 else 0)
    (hw : ∀ j, 0 < w j) (hs : Summable w) {ℓmin : ℝ} (hℓ : 0 < ℓmin)
    (hlen : ∀ j, ℓmin ≤ len j) (L : Finset ℝ) (hL : ∀ j, len j ∈ L) (hab : a < b) :
    InSemigroupL L (b - a) := by
  have hlenpos : ∀ j, 0 < len j := fun j ↦ lt_of_lt_of_le hℓ (hlen j)
  obtain ⟨i, hi⟩ := exists_end_at_right_inf hae hw hs hlenpos hab
  have := (start_mem_semigroup_inf hae hw hs hℓ hlen L hL i).add_mem (hL i)
  rwa [show c i - a + len i = b - a by linarith] at this

/-- The bounded part of `ℕ·L` is finite when `L` consists of lengths `≥ ℓmin > 0`. -/
theorem finite_semigroupL_le (L : Finset ℝ) {ℓmin : ℝ} (hℓ : 0 < ℓmin)
    (hL : ∀ l ∈ L, ℓmin ≤ l) (B : ℝ) :
    {z : ℝ | InSemigroupL L z ∧ z ≤ B}.Finite := by
  classical
  set K : ℕ := ⌊B / ℓmin⌋₊ with hK
  refine (Set.finite_range fun m : L → Fin (K + 1) ↦ ∑ l : L, ((m l : ℕ) : ℝ) * l).subset ?_
  rintro z ⟨⟨n, rfl⟩, hzB⟩
  have hbound : ∀ l : L, n l ≤ K := by
    intro l
    have hl : ℓmin ≤ (l : ℝ) := hL l l.2
    have hlpos : (0 : ℝ) < l := lt_of_lt_of_le hℓ hl
    have hterm : (n l : ℝ) * l ≤ B := by
      refine le_trans ?_ hzB
      exact Finset.single_le_sum (f := fun l : L ↦ (n l : ℝ) * l)
        (fun l _ ↦ mul_nonneg (Nat.cast_nonneg _) (lt_of_lt_of_le hℓ (hL l l.2)).le)
        (mem_univ l)
    rw [hK]
    apply Nat.le_floor
    rw [le_div_iff₀ hℓ]
    nlinarith [Nat.cast_nonneg (α := ℝ) (n l)]
  refine ⟨fun l ↦ ⟨n l, Nat.lt_succ_of_le (hbound l)⟩, ?_⟩
  simp

end

end WeakTiling

end

end InfiniteCover

/-! ## Step M: Theorem 3.4 of the source paper (covers of a half-line) -/

section HalfLineCover

section

open Finset MeasureTheory

namespace WeakTiling

variable {ι : Type*} {a : ℝ} {c len w : ι → ℝ}

/-- Local summability: intervals starting before any bound carry summable weight. -/
def LocallySummable (c w : ι → ℝ) : Prop :=
  ∀ R : ℝ, Summable fun j ↦ if c j < R then w j else 0

theorem summable_coverTerm_loc (hw : ∀ j, 0 < w j) (hls : LocallySummable c w) (x : ℝ) :
    Summable fun j ↦ if c j < x ∧ x < c j + len j then w j else 0 :=
  Summable.of_nonneg_of_le (fun j ↦ by split_ifs <;> linarith [hw j])
    (fun j ↦ by
      by_cases h : c j < x ∧ x < c j + len j
      · rw [ite_eq_left h, ite_eq_left h.1]
      · rw [ite_eq_right h]; split_ifs <;> linarith [hw j]) (hls x)

theorem coverTsum_ge_loc (hw : ∀ j, 0 < w j) (hls : LocallySummable c w) {x : ℝ} (k : ι)
    (hk : c k < x ∧ x < c k + len k) : w k ≤ coverTsum c len w x := by
  have := (summable_coverTerm_loc (len := len) hw hls x).le_tsum k
    (fun j _ ↦ by split_ifs <;> linarith [hw j])
  simp only [hk, and_self, ite_true] at this
  exact this

theorem exists_good_point_half (hae : ∀ᵐ x ∂(volume : Measure ℝ),
    coverTsum c len w x = if a < x then 1 else 0) {u v : ℝ} (huv : u < v) :
    ∃ x, u < x ∧ x < v ∧ coverTsum c len w x = if a < x then 1 else 0 := by
  have hpos : (volume : Measure ℝ) (Set.Ioo u v) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  obtain ⟨x, hx, hgood⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hae)
  exact ⟨x, hx.1, hx.2, hgood⟩

/-- No interval starts to the left of `a`. -/
theorem le_start_half (hae : ∀ᵐ x ∂(volume : Measure ℝ),
    coverTsum c len w x = if a < x then 1 else 0)
    (hw : ∀ j, 0 < w j) (hls : LocallySummable c w) (hlen : ∀ j, 0 < len j) (j : ι) :
    a ≤ c j := by
  by_contra h
  push Not at h
  obtain ⟨x, hx1, hx2, hgood⟩ := exists_good_point_half hae
    (lt_min h (by linarith [hlen j]) : c j < min a (c j + len j))
  rw [ite_eq_right (fun h' ↦ by linarith [min_le_left a (c j + len j)])] at hgood
  have := coverTsum_ge_loc hw hls j ⟨hx1, lt_of_lt_of_le hx2 (min_le_right _ _)⟩
  linarith [hw j]

/-- **Jump cancellation for half-line covers.** -/
theorem exists_end_of_start_half (hae : ∀ᵐ x ∂(volume : Measure ℝ),
    coverTsum c len w x = if a < x then 1 else 0)
    (hw : ∀ j, 0 < w j) (hls : LocallySummable c w) {ℓmin : ℝ} (hℓ : 0 < ℓmin)
    (hlen : ∀ j, ℓmin ≤ len j) (k : ι) (hak : a < c k) : ∃ i, c i + len i = c k := by
  classical
  by_contra hno
  push Not at hno
  set e := c k with he
  set w' : ι → ℝ := fun j ↦ if c j < e + 1 then w j else 0 with hw'
  have hw'0 : ∀ j, 0 ≤ w' j := fun j ↦ by simp only [hw']; split_ifs <;> linarith [hw j]
  obtain ⟨T, hT⟩ := exists_finset_tail w' hw'0 (hls (e + 1)) (hw k)
  obtain ⟨ε₀, hε₀, hiso⟩ :=
    exists_isolation (T.image c ∪ T.image fun j ↦ c j + len j) e
  set ε := min (min ε₀ ℓmin) (min (e - a) 1) / 2 with hεdef
  have hmin_pos : 0 < min (min ε₀ ℓmin) (min (e - a) 1) :=
    lt_min (lt_min hε₀ hℓ) (lt_min (by linarith) one_pos)
  have hε : 0 < ε := by positivity
  have hεε₀ : ε < ε₀ := by
    have := min_le_left (min ε₀ ℓmin) (min (e - a) 1)
    have := min_le_left ε₀ ℓmin
    linarith
  have hεℓ : ε < ℓmin := by
    have := min_le_left (min ε₀ ℓmin) (min (e - a) 1)
    have := min_le_right ε₀ ℓmin
    linarith
  have hεa : ε < e - a := by
    have := min_le_right (min ε₀ ℓmin) (min (e - a) 1)
    have := min_le_left (e - a) 1
    linarith
  have hε1 : ε < 1 := by
    have := min_le_right (min ε₀ ℓmin) (min (e - a) 1)
    have := min_le_right (e - a) 1
    linarith
  obtain ⟨x, hx1, hx2, hgx⟩ := exists_good_point_half hae (by linarith : e < e + ε)
  obtain ⟨x', hx'1, hx'2, hgx'⟩ := exists_good_point_half hae (by linarith : e - ε < e)
  rw [ite_eq_left (by linarith)] at hgx hgx'
  set r : ι → ℝ := fun j ↦
    if (c j ≠ e ∧ |c j - e| < ε) ∨ (c j + len j ≠ e ∧ |c j + len j - e| < ε) then 1 else 0
    with hr
  have hr01 : ∀ j, 0 ≤ r j ∧ r j ≤ 1 := fun j ↦ by
    simp only [hr]; split_ifs <;> norm_num
  have hrT : ∀ j ∈ T, r j = 0 := by
    intro j hj
    simp only [hr]
    rw [ite_eq_right]
    rintro (⟨hne, hlt⟩ | ⟨hne, hlt⟩)
    · have := hiso (c j) (mem_union_left _ (mem_image_of_mem _ hj)) hne
      linarith
    · have := hiso (c j + len j) (mem_union_right _ (mem_image_of_mem (fun j ↦ c j + len j) hj))
        hne
      linarith
  have hR := hT r hr01 hrT
  -- intervals with `r j = 1` start before `e + 1`
  have hrw : ∀ j, w j * r j = w' j * r j := by
    intro j
    simp only [hr, hw']
    split_ifs with h1 h2 <;> try simp
    exfalso
    rcases h1 with ⟨_, hlt⟩ | ⟨_, hlt⟩
    · rw [abs_lt] at hlt; linarith
    · rw [abs_lt] at hlt; linarith [hlen j]
  set g : ι → ℝ := fun j ↦ (if c j < x ∧ x < c j + len j then w j else 0) -
    (if c j < x' ∧ x' < c j + len j then w j else 0) with hg
  set h : ι → ℝ := fun j ↦ (if j = k then w k else 0) - w' j * r j with hh
  have hkact : c k < x ∧ x < c k + len k := ⟨by linarith, by linarith [hlen k]⟩
  have hkact' : ¬ (c k < x' ∧ x' < c k + len k) := fun h' ↦ by linarith [h'.1]
  have hgh : ∀ j, h j ≤ g j := by
    intro j
    simp only [hh, hg]
    rw [← hrw j]
    by_cases hcond : (c j ≠ e ∧ |c j - e| < ε) ∨ (c j + len j ≠ e ∧ |c j + len j - e| < ε)
    · have hrj : r j = 1 := by simp only [hr]; rw [ite_eq_left hcond]
      rw [hrj, mul_one]
      by_cases hjk : j = k
      · subst hjk
        rw [ite_eq_left rfl, ite_eq_left hkact, ite_eq_right hkact']
        linarith [hw j]
      · rw [ite_eq_right hjk]
        split_ifs <;> linarith [hw j]
    · have hrj : r j = 0 := by simp only [hr]; rw [ite_eq_right hcond]
      rw [hrj, mul_zero, sub_zero]
      push Not at hcond
      obtain ⟨hc1, hc2⟩ := hcond
      have hend : ε ≤ |c j + len j - e| := hc2 (hno j)
      by_cases hce : c j = e
      · have hact : c j < x ∧ x < c j + len j := ⟨by linarith, by linarith [hlen j]⟩
        have hact' : ¬ (c j < x' ∧ x' < c j + len j) := fun h' ↦ by linarith [h'.1]
        rw [ite_eq_left hact, ite_eq_right hact', sub_zero]
        split_ifs with hjk
        · subst hjk; exact le_rfl
        · exact (hw j).le
      · have hcfar : ε ≤ |c j - e| := hc1 hce
        have hjk : j ≠ k := fun h' ↦ hce (h' ▸ rfl)
        rw [ite_eq_right hjk]
        have h1 : c j < x ↔ c j < x' := by
          rcases le_abs'.mp hcfar with h' | h' <;> constructor <;> intro _ <;> linarith
        have h2 : x < c j + len j ↔ x' < c j + len j := by
          rcases le_abs'.mp hend with h' | h' <;> constructor <;> intro _ <;> linarith
        simp only [h1, h2, sub_self, le_refl]
  have hsx := summable_coverTerm_loc (len := len) hw hls x
  have hsx' := summable_coverTerm_loc (len := len) hw hls x'
  have hwr : Summable fun j ↦ w' j * r j :=
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (hw'0 j) (hr01 j).1)
      (fun j ↦ by nlinarith [hw'0 j, (hr01 j).1, (hr01 j).2]) (hls (e + 1))
  have hsite : Summable fun j ↦ if j = k then w k else 0 :=
    summable_of_ne_finset_zero (s := {k}) (fun j hj ↦ by simp at hj; simp [hj])
  have hsumg : ∑' j, g j = 0 := by
    simp only [hg]
    rw [hsx.tsum_sub hsx']
    change coverTsum c len w x - coverTsum c len w x' = 0
    rw [hgx, hgx', sub_self]
  have hsumh : ∑' j, h j = w k - ∑' j, w' j * r j := by
    simp only [hh]
    rw [hsite.tsum_sub hwr, tsum_ite_eq]
  have hle : ∑' j, h j ≤ ∑' j, g j :=
    Summable.tsum_le_tsum hgh (hsite.sub hwr) (hsx.sub hsx')
  linarith

/-- **Theorem 3.4 (i).**  Every start point lies in `a + ℕ·L`. -/
theorem start_mem_semigroup_half (hae : ∀ᵐ x ∂(volume : Measure ℝ),
    coverTsum c len w x = if a < x then 1 else 0)
    (hw : ∀ j, 0 < w j) (hls : LocallySummable c w) {ℓmin : ℝ} (hℓ : 0 < ℓmin)
    (hlen : ∀ j, ℓmin ≤ len j) (L : Finset ℝ) (hL : ∀ j, len j ∈ L) (j : ι) :
    InSemigroupL L (c j - a) := by
  have hlenpos : ∀ j, 0 < len j := fun j ↦ lt_of_lt_of_le hℓ (hlen j)
  suffices H : ∀ N : ℕ, ∀ j, c j - a < (N + 1) * ℓmin → InSemigroupL L (c j - a) by
    obtain ⟨N, hN⟩ := exists_nat_gt ((c j - a) / ℓmin)
    exact H N j (by rw [div_lt_iff₀ hℓ] at hN; nlinarith)
  intro N
  induction N with
  | zero =>
    intro j hj
    rcases (le_start_half hae hw hls hlenpos j).lt_or_eq with hlt | heq
    · obtain ⟨i, hi⟩ := exists_end_of_start_half hae hw hls hℓ hlen j hlt
      have := le_start_half hae hw hls hlenpos i
      have := hlen i
      push_cast at hj
      linarith
    · rw [← heq, sub_self]; exact InSemigroupL.zero L
  | succ N ih =>
    intro j hj
    rcases (le_start_half hae hw hls hlenpos j).lt_or_eq with hlt | heq
    · obtain ⟨i, hi⟩ := exists_end_of_start_half hae hw hls hℓ hlen j hlt
      have hi' : c i - a < (N + 1) * ℓmin := by
        have := hlen i
        push_cast at hj
        linarith
      have := (ih i hi').add_mem (hL i)
      rwa [show c i - a + len i = c j - a by linarith] at this
    · rw [← heq, sub_self]; exact InSemigroupL.zero L

end WeakTiling

end

end HalfLineCover

/-! ## Step M: translates of the tile avoid `Ω` and sit in one component of `Ωᶜ` -/

section AtomicSupport

section

open Finset MeasureTheory

namespace WeakTiling

variable {n : ℕ} {A B : Fin n → ℝ}

/-- The finite union of intervals `⋃ᵢ (Aᵢ, Bᵢ)`. -/
def unionIoo (A B : Fin n → ℝ) : Set ℝ :=
  ⋃ i, Set.Ioo (A i) (B i)

/-- An open interval `(u, v)` disjoint from `(A, B)` lies on one side of it. -/
theorem side_of_disjoint {u v a b : ℝ} (huv : u < v) (hab : a < b)
    (hdisj : ∀ x, u < x → x < v → ¬ (a < x ∧ x < b)) : v ≤ a ∨ b ≤ u := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hlo : max u a < min v b := lt_min (max_lt huv h1) (max_lt h2 hab)
  refine hdisj ((max u a + min v b) / 2) ?_ ?_ ⟨?_, ?_⟩ <;>
    linarith [le_max_left u a, le_max_right u a, min_le_left v b, min_le_right v b]

/-- **Component classification.**  An open interval disjoint from all `(Aᵢ, Bᵢ)` (with the
intervals ordered) lies in the left half-line, a gap, or the right half-line. -/
theorem component_of_disjoint (hn : 0 < n) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j) {u v : ℝ} (huv : u < v)
    (hdisj : ∀ x, u < x → x < v → x ∉ unionIoo A B) :
    v ≤ A ⟨0, hn⟩ ∨ (∃ m : Fin n, ∃ hm : m.val + 1 < n,
      B m ≤ u ∧ v ≤ A ⟨m.val + 1, hm⟩) ∨ B ⟨n - 1, by omega⟩ ≤ u := by
  classical
  have hside : ∀ i, v ≤ A i ∨ B i ≤ u := fun i ↦
    side_of_disjoint huv (hAB i) fun x hx1 hx2 hx ↦
      hdisj x hx1 hx2 (Set.mem_iUnion.mpr ⟨i, hx⟩)
  by_cases hall : ∀ i, v ≤ A i
  · exact Or.inl (hall ⟨0, hn⟩)
  push Not at hall
  -- the largest index with `B i ≤ u`
  set S := univ.filter fun i : Fin n ↦ B i ≤ u with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hall
    exact ⟨i, by simp [hS, (hside i).resolve_left (not_le.mpr hi)]⟩
  set m := S.max' hSne with hm
  have hmS : B m ≤ u := by
    have := S.max'_mem hSne
    simp only [hS, mem_filter, mem_univ, true_and] at this
    exact this
  by_cases hlast : m.val + 1 < n
  · refine Or.inr (Or.inl ⟨m, hlast, hmS, ?_⟩)
    rcases hside ⟨m.val + 1, hlast⟩ with h | h
    · exact h
    · exfalso
      have hmem : (⟨m.val + 1, hlast⟩ : Fin n) ∈ S := by simp [hS, h]
      have := S.le_max' _ hmem
      rw [← hm] at this
      have : m.val + 1 ≤ m.val := this
      omega
  · refine Or.inr (Or.inr ?_)
    have hmeq : m = ⟨n - 1, by omega⟩ := Fin.ext (by show m.val = n - 1; have := m.isLt; omega)
    rw [← hmeq]
    exact hmS

/-- Two-sided local summability: intervals starting in any bounded window carry summable weight.
This is what local finiteness of the weak tiling measure provides. -/
def LocSum2 {ι : Type*} (c w : ι → ℝ) : Prop :=
  ∀ R : ℝ, Summable fun p ↦ if |c p| ≤ R then w p else 0

/-- A bounded subfamily is summable. -/
theorem LocSum2.summable_subtype {ι : Type*} {c w : ι → ℝ} (h : LocSum2 c w)
    (P : ι → Prop) (R : ℝ) (hR : ∀ p, P p → |c p| ≤ R) :
    Summable fun q : {p // P p} ↦ w q.1 := by
  refine ((h R).subtype P).congr fun q ↦ ?_
  simp [hR q.1 q.2]

/-- The cover terms at a point are summable when the lengths are bounded. -/
theorem LocSum2.summable_coverTerm {ι : Type*} {c len w : ι → ℝ} (h : LocSum2 c w)
    (hw : ∀ p, 0 < w p) {ℓmax : ℝ} (hlen : ∀ p, len p ≤ ℓmax) (x : ℝ) :
    Summable fun p ↦ if c p < x ∧ x < c p + len p then w p else 0 := by
  refine Summable.of_nonneg_of_le (fun p ↦ by split_ifs <;> linarith [hw p])
    (fun p ↦ ?_) (h (|x| + |ℓmax|))
  by_cases hp : c p < x ∧ x < c p + len p
  · rw [ite_eq_left hp, ite_eq_left]
    have := hlen p
    rw [abs_le]
    constructor <;> cases abs_cases x <;> cases abs_cases ℓmax <;> linarith [hp.1, hp.2]
  · rw [ite_eq_right hp]; split_ifs <;> linarith [hw p]

theorem LocSum2.coverTsum_ge {ι : Type*} {c len w : ι → ℝ} (h : LocSum2 c w)
    (hw : ∀ p, 0 < w p) {ℓmax : ℝ} (hlen : ∀ p, len p ≤ ℓmax) {x : ℝ} (k : ι)
    (hk : c k < x ∧ x < c k + len k) : w k ≤ coverTsum c len w x := by
  have := (h.summable_coverTerm hw hlen x).le_tsum k
    (fun j _ ↦ by split_ifs <;> linarith [hw j])
  simp only [hk, and_self, ite_true] at this
  exact this

variable {κ : Type*} {lam wt : κ → ℝ}

/-- Start points of the translated intervals. -/
def transStart (A : Fin n → ℝ) (lam : κ → ℝ) (p : κ × Fin n) : ℝ :=
  A p.2 + lam p.1

/-- Lengths of the translated intervals. -/
def transLen (A B : Fin n → ℝ) (p : κ × Fin n) : ℝ :=
  B p.2 - A p.2

/-- Weights of the translated intervals. -/
def transWt (wt : κ → ℝ) (p : κ × Fin n) : ℝ :=
  wt p.1

open Classical in
/-- **Translates avoid `Ω`.** -/
theorem translate_disjoint (hAB : ∀ i, A i < B i) (hwt : ∀ k, 0 < wt k)
    (hls : LocSum2 (transStart A lam) (transWt (n := n) wt))
    (hT : ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (transStart A lam) (transLen A B) (transWt wt) x =
        if x ∈ unionIoo A B then 0 else 1)
    (p : κ × Fin n) (x : ℝ) (hx1 : transStart A lam p < x)
    (hx2 : x < transStart A lam p + transLen A B p) : x ∉ unionIoo A B := by
  intro hxΩ
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxΩ
  -- a nonempty open piece of the translate inside `(Aᵢ, Bᵢ)`
  set u := max (transStart A lam p) (A i)
  set v := min (transStart A lam p + transLen A B p) (B i)
  have hi1 := hi.1
  have hi2 := hi.2
  have huv : u < v := lt_min (max_lt (by linarith) (by linarith)) (max_lt (by linarith) (hAB i))
  have hpos : (volume : Measure ℝ) (Set.Ioo u v) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  obtain ⟨y, hy, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hT)
  have hyΩ : y ∈ unionIoo A B := Set.mem_iUnion.mpr ⟨i,
    ⟨lt_of_le_of_lt (le_max_right _ _) hy.1, lt_of_lt_of_le hy.2 (min_le_right _ _)⟩⟩
  rw [ite_eq_left hyΩ] at hgood
  have hwpos : ∀ q : κ × Fin n, 0 < transWt wt q := fun q ↦ hwt q.1
  have hlenle : ∀ q : κ × Fin n, transLen A B q ≤ ∑ i, (B i - A i) := fun q ↦
    Finset.single_le_sum (f := fun i ↦ B i - A i) (fun i _ ↦ by linarith [hAB i]) (mem_univ q.2)
  have := hls.coverTsum_ge hwpos hlenle p
    ⟨lt_of_le_of_lt (le_max_left _ _) hy.1, lt_of_lt_of_le hy.2 (min_le_left _ _)⟩
  linarith [hwpos p]

section Gap

variable (hn : 0 < n) (hAB : ∀ i, A i < B i) (hord : ∀ i j : Fin n, i < j → B i < A j)

include hAB hord in
theorem A_mono {i j : Fin n} (hij : i ≤ j) : A i ≤ A j := by
  rcases hij.lt_or_eq with h | h
  · linarith [hord i j h, hAB i]
  · rw [h]

include hAB hord in
theorem B_mono {i j : Fin n} (hij : i ≤ j) : B i ≤ B j := by
  rcases hij.lt_or_eq with h | h
  · linarith [hord i j h, hAB j]
  · rw [h]

include hAB hord in
/-- Points of a gap are not in `Ω`. -/
theorem gap_notMem {m : Fin n} (hm : m.val + 1 < n) {x : ℝ} (hx1 : B m < x)
    (hx2 : x < A ⟨m.val + 1, hm⟩) : x ∉ unionIoo A B := by
  intro hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  by_cases him : i ≤ m
  · linarith [B_mono hAB hord him, hi.2]
  · have : (⟨m.val + 1, hm⟩ : Fin n) ≤ i := by
      show m.val + 1 ≤ i.val
      have : m.val < i.val := not_le.mp him
      omega
    linarith [A_mono hAB hord this, hi.1]

/-- The set of lengths `L = {Bᵢ - Aᵢ}`. -/
noncomputable def lengthSet (A B : Fin n → ℝ) : Finset ℝ :=
  univ.image fun i ↦ B i - A i

include hAB in
theorem lengthSet_pos {l : ℝ} (hl : l ∈ lengthSet A B) : 0 < l := by
  obtain ⟨i, -, rfl⟩ := mem_image.mp hl
  linarith [hAB i]

theorem mem_lengthSet (i : Fin n) : B i - A i ∈ lengthSet A B :=
  mem_image.mpr ⟨i, mem_univ i, rfl⟩

/-- A positive lower bound for the lengths. -/
noncomputable def minLength (hn : 0 < n) (A B : Fin n → ℝ) : ℝ :=
  (lengthSet A B).min' ⟨B ⟨0, hn⟩ - A ⟨0, hn⟩, mem_lengthSet _⟩

include hAB in
theorem minLength_pos : 0 < minLength hn A B :=
  lengthSet_pos hAB (Finset.min'_mem _ _)

theorem minLength_le (i : Fin n) : minLength hn A B ≤ B i - A i :=
  Finset.min'_le _ _ (mem_lengthSet i)

variable {hn}

open Classical in
include hAB hord in
/-- **Restriction to a gap.**  The translates lying in the gap `(Bₘ, Aₘ₊₁)` cover it exactly. -/
theorem gap_cover {m : Fin n} (hm : m.val + 1 < n) (hwt : ∀ k, 0 < wt k)
    (hls : LocSum2 (transStart A lam) (transWt (n := n) wt))
    (hT : ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (transStart A lam) (transLen A B) (transWt wt) x =
        if x ∈ unionIoo A B then 0 else 1) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (ι := {p : κ × Fin n // B m ≤ transStart A lam p ∧
          transStart A lam p + transLen A B p ≤ A ⟨m.val + 1, hm⟩})
        (fun q ↦ transStart A lam q.1) (fun q ↦ transLen A B q.1) (fun q ↦ transWt wt q.1) x =
        if B m < x ∧ x < A ⟨m.val + 1, hm⟩ then 1 else 0 := by
  set u := B m
  set v := A ⟨m.val + 1, hm⟩
  set P : κ × Fin n → Prop := fun p ↦ u ≤ transStart A lam p ∧
    transStart A lam p + transLen A B p ≤ v with hP
  filter_upwards [hT, Measure.ae_ne volume u, Measure.ae_ne volume v] with x hx hxu hxv
  unfold coverTsum
  set f : κ × Fin n → ℝ := fun p ↦ if transStart A lam p < x ∧
    x < transStart A lam p + transLen A B p then transWt wt p else 0 with hf
  have key : (∑' j : {p // P p}, f j.1) = ∑' p, Set.indicator {p | P p} f p :=
    tsum_subtype {p | P p} f
  change (∑' j : {p // P p}, f j.1) = _
  rw [key]
  by_cases hin : u < x ∧ x < v
  · rw [ite_eq_left hin]
    have hxΩ : x ∉ unionIoo A B := gap_notMem hAB hord hm hin.1 hin.2
    rw [ite_eq_right hxΩ] at hx
    unfold coverTsum at hx
    rw [← hx]
    congr 1
    funext p
    by_cases hPp : P p
    · rw [Set.indicator_of_mem (show p ∈ {p | P p} from hPp)]
    · rw [Set.indicator_of_notMem (show p ∉ {p | P p} from hPp)]
      symm
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      apply hPp
      -- the translate containing `x` lies in the gap
      have hdisj : ∀ y, transStart A lam p < y → y < transStart A lam p + transLen A B p →
          y ∉ unionIoo A B := fun y hy1 hy2 ↦
        translate_disjoint hAB hwt hls hT p y hy1 hy2
      have hside1 := side_of_disjoint (by linarith) (hAB m) fun y hy1 hy2 hy ↦
        hdisj y hy1 hy2 (Set.mem_iUnion.mpr ⟨m, hy⟩)
      have hside2 := side_of_disjoint (by linarith) (hAB ⟨m.val + 1, hm⟩) fun y hy1 hy2 hy ↦
        hdisj y hy1 hy2 (Set.mem_iUnion.mpr ⟨⟨m.val + 1, hm⟩, hy⟩)
      refine ⟨?_, ?_⟩
      · rcases hside1 with h | h
        · linarith [hAB m, hin.1]
        · exact h
      · rcases hside2 with h | h
        · exact h
        · linarith [hAB ⟨m.val + 1, hm⟩, hin.2]
  · rw [ite_eq_right hin]
    refine (tsum_congr fun p ↦ ?_).trans tsum_zero
    by_cases hPp : P p
    · rw [Set.indicator_of_mem (show p ∈ {p | P p} from hPp), hf]
      dsimp only
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      apply hin
      exact ⟨lt_of_le_of_lt hPp.1 h1, lt_of_lt_of_le h2 hPp.2⟩
    · rw [Set.indicator_of_notMem (show p ∉ {p | P p} from hPp)]

/-- Local summability passes to subfamilies. -/
theorem LocallySummable.subtype {ι : Type*} {c w : ι → ℝ} (hls : LocallySummable c w)
    (P : ι → Prop) :
    LocallySummable (fun q : {p // P p} ↦ c q.1) (fun q ↦ w q.1) := fun R ↦
  (hls R).subtype P

open Classical in
include hAB hord in
/-- **Theorem 3.6 (gaps).**  Each gap length `Aₘ₊₁ - Bₘ` is a nonnegative integer combination of
the interval lengths, and every translate inside the gap starts in `Bₘ + ℕ·L`. -/
theorem gap_semigroup {m : Fin n} (hm : m.val + 1 < n) (hwt : ∀ k, 0 < wt k)
    (hls : LocSum2 (transStart A lam) (transWt (n := n) wt))
    (hT : ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (transStart A lam) (transLen A B) (transWt wt) x =
        if x ∈ unionIoo A B then 0 else 1) :
    InSemigroupL (lengthSet A B) (A ⟨m.val + 1, hm⟩ - B m) ∧
      ∀ p : κ × Fin n, B m ≤ transStart A lam p →
        transStart A lam p + transLen A B p ≤ A ⟨m.val + 1, hm⟩ →
        InSemigroupL (lengthSet A B) (transStart A lam p - B m) := by
  have hn : 0 < n := by omega
  set P : κ × Fin n → Prop := fun p ↦ B m ≤ transStart A lam p ∧
    transStart A lam p + transLen A B p ≤ A ⟨m.val + 1, hm⟩ with hP
  have hcov := gap_cover (lam := lam) hAB hord hm hwt hls hT
  have hwpos : ∀ q : {p // P p}, 0 < transWt wt q.1 := fun q ↦ hwt q.1.1
  have hsum : Summable fun q : {p // P p} ↦ transWt wt q.1 :=
    hls.summable_subtype P (|B m| + |A ⟨m.val + 1, hm⟩|) fun p hp ↦ by
      have h1 := hp.1
      have h2 := hp.2
      have : 0 < transLen A B p := by
        simp only [transLen]; linarith [hAB p.2]
      rw [abs_le]
      constructor <;> cases abs_cases (B m) <;> cases abs_cases (A ⟨m.val + 1, hm⟩) <;> linarith
  have hℓ := minLength_pos hn hAB
  have hlen : ∀ q : {p // P p}, minLength hn A B ≤ transLen A B q.1 := fun q ↦
    minLength_le hn q.1.2
  have hL : ∀ q : {p // P p}, transLen A B q.1 ∈ lengthSet A B := fun q ↦ mem_lengthSet q.1.2
  have hgap : B m < A ⟨m.val + 1, hm⟩ := hord m ⟨m.val + 1, hm⟩ (by
    show m.val < m.val + 1; omega)
  refine ⟨length_mem_semigroup_inf hcov hwpos hsum hℓ hlen _ hL hgap, fun p hp1 hp2 ↦ ?_⟩
  exact start_mem_semigroup_inf hcov hwpos hsum hℓ hlen _ hL ⟨p, hp1, hp2⟩

end Gap

section RightHalf

variable (hAB : ∀ i, A i < B i) (hord : ∀ i j : Fin n, i < j → B i < A j)

include hAB hord in
/-- Points to the right of the last interval are not in `Ω`. -/
theorem right_notMem (hn : 0 < n) {x : ℝ} (hx : B ⟨n - 1, by omega⟩ < x) :
    x ∉ unionIoo A B := by
  intro hxΩ
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxΩ
  have : i ≤ ⟨n - 1, by omega⟩ := by show i.val ≤ n - 1; have := i.isLt; omega
  linarith [B_mono hAB hord this, hi.2]

open Classical in
include hAB hord in
/-- **Restriction to the right half-line.** -/
theorem right_cover (hn : 0 < n) (hwt : ∀ k, 0 < wt k)
    (hls : LocSum2 (transStart A lam) (transWt (n := n) wt))
    (hT : ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (transStart A lam) (transLen A B) (transWt wt) x =
        if x ∈ unionIoo A B then 0 else 1) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (ι := {p : κ × Fin n // B ⟨n - 1, by omega⟩ ≤ transStart A lam p})
        (fun q ↦ transStart A lam q.1) (fun q ↦ transLen A B q.1) (fun q ↦ transWt wt q.1) x =
        if B ⟨n - 1, by omega⟩ < x then 1 else 0 := by
  set u := B ⟨n - 1, by omega⟩ with hu
  set P : κ × Fin n → Prop := fun p ↦ u ≤ transStart A lam p with hP
  filter_upwards [hT, Measure.ae_ne volume u] with x hx hxu
  unfold coverTsum
  set f : κ × Fin n → ℝ := fun p ↦ if transStart A lam p < x ∧
    x < transStart A lam p + transLen A B p then transWt wt p else 0 with hf
  have key : (∑' j : {p // P p}, f j.1) = ∑' p, Set.indicator {p | P p} f p :=
    tsum_subtype {p | P p} f
  change (∑' j : {p // P p}, f j.1) = _
  rw [key]
  by_cases hin : u < x
  · rw [ite_eq_left hin]
    rw [ite_eq_right (right_notMem hAB hord hn hin)] at hx
    unfold coverTsum at hx
    rw [← hx]
    congr 1
    funext p
    by_cases hPp : P p
    · rw [Set.indicator_of_mem (show p ∈ {p | P p} from hPp)]
    · rw [Set.indicator_of_notMem (show p ∉ {p | P p} from hPp)]
      symm
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      apply hPp
      have hside := side_of_disjoint (by linarith) (hAB ⟨n - 1, by omega⟩)
        fun y hy1 hy2 hy ↦ translate_disjoint hAB hwt hls hT p y hy1 hy2
          (Set.mem_iUnion.mpr ⟨⟨n - 1, by omega⟩, hy⟩)
      rcases hside with h | h
      · linarith [hAB ⟨n - 1, by omega⟩]
      · exact h
  · rw [ite_eq_right hin]
    refine (tsum_congr fun p ↦ ?_).trans tsum_zero
    by_cases hPp : P p
    · rw [Set.indicator_of_mem (show p ∈ {p | P p} from hPp), hf]
      dsimp only
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      have : x ≤ u := not_lt.mp hin
      have := hPp
      linarith
    · rw [Set.indicator_of_notMem (show p ∉ {p | P p} from hPp)]

open Classical in
include hAB hord in
/-- **Right half-line (Theorem 3.4 applied).**  Every translate to the right of `Ω` starts in
`B_{n-1} + ℕ·L`. -/
theorem right_semigroup (hn : 0 < n) (hwt : ∀ k, 0 < wt k)
    (hls : LocSum2 (transStart A lam) (transWt (n := n) wt))
    (hT : ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (transStart A lam) (transLen A B) (transWt wt) x =
        if x ∈ unionIoo A B then 0 else 1)
    (p : κ × Fin n) (hp : B ⟨n - 1, by omega⟩ ≤ transStart A lam p) :
    InSemigroupL (lengthSet A B) (transStart A lam p - B ⟨n - 1, by omega⟩) := by
  set u := B ⟨n - 1, by omega⟩ with hu
  set P : κ × Fin n → Prop := fun p ↦ u ≤ transStart A lam p with hP
  have hcov := right_cover (lam := lam) hAB hord hn hwt hls hT
  have hwpos : ∀ q : {p // P p}, 0 < transWt wt q.1 := fun q ↦ hwt q.1.1
  have hloc : LocallySummable (fun q : {p // P p} ↦ transStart A lam q.1)
      (fun q ↦ transWt wt q.1) := by
    intro R
    refine Summable.of_nonneg_of_le (fun q ↦ by split_ifs <;> linarith [hwpos q]) (fun q ↦ ?_)
      ((hls (|u| + |R|)).subtype P)
    by_cases hq : transStart A lam q.1 < R
    · simp only [Function.comp, ite_eq_left hq]
      rw [ite_eq_left]
      have := q.2
      rw [abs_le]
      constructor <;> cases abs_cases u <;> cases abs_cases R <;> linarith
    · simp only [Function.comp, ite_eq_right hq]
      split_ifs <;> linarith [hwpos q]
  have hℓ := minLength_pos hn hAB
  have hlen : ∀ q : {p // P p}, minLength hn A B ≤ transLen A B q.1 := fun q ↦
    minLength_le hn q.1.2
  have hL : ∀ q : {p // P p}, transLen A B q.1 ∈ lengthSet A B := fun q ↦ mem_lengthSet q.1.2
  exact start_mem_semigroup_half hcov hwpos hloc hℓ hlen _ hL ⟨p, hp⟩

end RightHalf

/-- Reflecting a cover: `(−(c+ℓ), −c)` covers the mirror image. -/
theorem reflect_cover {ι : Type*} {c len w : ι → ℝ} {target : ℝ → ℝ}
    (h : ∀ᵐ x ∂(volume : Measure ℝ), coverTsum c len w x = target x) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (fun p ↦ -(c p + len p)) len w x = target (-x) := by
  have h' := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h
  filter_upwards [h'] with x hx
  rw [← hx]
  unfold coverTsum
  refine tsum_congr fun p ↦ ?_
  have h1 : (-(c p + len p) < x ∧ x < -(c p + len p) + len p) ↔ (c p < -x ∧ -x < c p + len p) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [Pi.neg_apply, h1]

theorem InSemigroupL.add {L : Finset ℝ} {z z' : ℝ} (hz : InSemigroupL L z)
    (hz' : InSemigroupL L z') : InSemigroupL L (z + z') := by
  obtain ⟨n, rfl⟩ := hz
  obtain ⟨n', rfl⟩ := hz'
  refine ⟨n + n', ?_⟩
  simp only [Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem InSemigroupL.of_mem {L : Finset ℝ} {l : ℝ} (hl : l ∈ L) : InSemigroupL L l := by
  have := (InSemigroupL.zero L).add_mem hl
  rwa [zero_add] at this

section Left

variable (hAB : ∀ i, A i < B i) (hord : ∀ i j : Fin n, i < j → B i < A j)

include hAB hord in
theorem left_notMem (hn : 0 < n) {x : ℝ} (hx : x < A ⟨0, hn⟩) : x ∉ unionIoo A B := by
  intro hxΩ
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxΩ
  have : (⟨0, hn⟩ : Fin n) ≤ i := by show 0 ≤ i.val; omega
  linarith [A_mono hAB hord this, hi.1]

open Classical in
include hAB hord in
/-- **Restriction to the left half-line.** -/
theorem left_cover (hn : 0 < n) (hwt : ∀ k, 0 < wt k)
    (hls : LocSum2 (transStart A lam) (transWt (n := n) wt))
    (hT : ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (transStart A lam) (transLen A B) (transWt wt) x =
        if x ∈ unionIoo A B then 0 else 1) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (ι := {p : κ × Fin n // transStart A lam p + transLen A B p ≤ A ⟨0, hn⟩})
        (fun q ↦ transStart A lam q.1) (fun q ↦ transLen A B q.1) (fun q ↦ transWt wt q.1) x =
        if x < A ⟨0, hn⟩ then 1 else 0 := by
  set v := A ⟨0, hn⟩ with hv
  set P : κ × Fin n → Prop := fun p ↦ transStart A lam p + transLen A B p ≤ v with hP
  filter_upwards [hT, Measure.ae_ne volume v] with x hx hxv
  unfold coverTsum
  set f : κ × Fin n → ℝ := fun p ↦ if transStart A lam p < x ∧
    x < transStart A lam p + transLen A B p then transWt wt p else 0 with hf
  have key : (∑' j : {p // P p}, f j.1) = ∑' p, Set.indicator {p | P p} f p :=
    tsum_subtype {p | P p} f
  change (∑' j : {p // P p}, f j.1) = _
  rw [key]
  by_cases hin : x < v
  · rw [ite_eq_left hin]
    rw [ite_eq_right (left_notMem hAB hord hn hin)] at hx
    unfold coverTsum at hx
    rw [← hx]
    congr 1
    funext p
    by_cases hPp : P p
    · rw [Set.indicator_of_mem (show p ∈ {p | P p} from hPp)]
    · rw [Set.indicator_of_notMem (show p ∉ {p | P p} from hPp)]
      symm
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      apply hPp
      have hside := side_of_disjoint (by linarith) (hAB ⟨0, hn⟩)
        fun y hy1 hy2 hy ↦ translate_disjoint hAB hwt hls hT p y hy1 hy2
          (Set.mem_iUnion.mpr ⟨⟨0, hn⟩, hy⟩)
      rcases hside with h | h
      · exact h
      · linarith [hAB ⟨0, hn⟩]
  · rw [ite_eq_right hin]
    refine (tsum_congr fun p ↦ ?_).trans tsum_zero
    by_cases hPp : P p
    · rw [Set.indicator_of_mem (show p ∈ {p | P p} from hPp), hf]
      dsimp only
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      have : v ≤ x := not_lt.mp hin
      have := hPp
      linarith
    · rw [Set.indicator_of_notMem (show p ∉ {p | P p} from hPp)]

open Classical in
include hAB hord in
/-- **Left half-line.**  Every translate to the left of `Ω` ends in `A₀ - ℕ·L`. -/
theorem left_semigroup (hn : 0 < n) (hwt : ∀ k, 0 < wt k)
    (hls : LocSum2 (transStart A lam) (transWt (n := n) wt))
    (hT : ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (transStart A lam) (transLen A B) (transWt wt) x =
        if x ∈ unionIoo A B then 0 else 1)
    (p : κ × Fin n) (hp : transStart A lam p + transLen A B p ≤ A ⟨0, hn⟩) :
    InSemigroupL (lengthSet A B) (A ⟨0, hn⟩ - (transStart A lam p + transLen A B p)) := by
  set v := A ⟨0, hn⟩ with hv
  set P : κ × Fin n → Prop := fun p ↦ transStart A lam p + transLen A B p ≤ v with hP
  have hcov := reflect_cover (left_cover (lam := lam) hAB hord hn hwt hls hT)
  have hcov' : ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (fun q : {p // P p} ↦ -(transStart A lam q.1 + transLen A B q.1))
        (fun q ↦ transLen A B q.1) (fun q ↦ transWt wt q.1) x = if -v < x then 1 else 0 := by
    filter_upwards [hcov] with x hx
    rw [hx]
    by_cases h : -x < v
    · rw [ite_eq_left h, ite_eq_left (by linarith)]
    · rw [ite_eq_right h, ite_eq_right (by linarith)]
  have hwpos : ∀ q : {p // P p}, 0 < transWt wt q.1 := fun q ↦ hwt q.1.1
  have hlenmax : ∀ q : κ × Fin n, transLen A B q ≤ ∑ i, (B i - A i) := fun q ↦
    Finset.single_le_sum (f := fun i ↦ B i - A i) (fun i _ ↦ by linarith [hAB i]) (mem_univ q.2)
  have hlenpos : ∀ q : κ × Fin n, 0 < transLen A B q := fun q ↦ by
    simp only [transLen]; linarith [hAB q.2]
  set S := ∑ i, (B i - A i)
  have hloc : LocallySummable (fun q : {p // P p} ↦ -(transStart A lam q.1 + transLen A B q.1))
      (fun q ↦ transWt wt q.1) := by
    intro R
    refine Summable.of_nonneg_of_le (fun q ↦ by split_ifs <;> linarith [hwpos q]) (fun q ↦ ?_)
      ((hls (|v| + |R| + |S|)).subtype P)
    by_cases hq : -(transStart A lam q.1 + transLen A B q.1) < R
    · simp only [Function.comp, ite_eq_left hq]
      rw [ite_eq_left]
      have h2 := q.2
      have h3 := hlenmax q.1
      have h4 := hlenpos q.1
      rw [abs_le]
      constructor <;> cases abs_cases v <;> cases abs_cases R <;> cases abs_cases S <;>
        simp only [hP] at h2 <;> linarith
    · simp only [Function.comp, ite_eq_right hq]
      split_ifs <;> linarith [hwpos q]
  have hℓ := minLength_pos hn hAB
  have hlen : ∀ q : {p // P p}, minLength hn A B ≤ transLen A B q.1 := fun q ↦
    minLength_le hn q.1.2
  have hL : ∀ q : {p // P p}, transLen A B q.1 ∈ lengthSet A B := fun q ↦ mem_lengthSet q.1.2
  have := start_mem_semigroup_half hcov' hwpos hloc hℓ hlen _ hL ⟨p, hp⟩
  rwa [show -(transStart A lam p + transLen A B p) - -v = v - (transStart A lam p +
    transLen A B p) by ring] at this

open Classical in
include hAB hord in
/-- **Chain.**  `Bⱼ - A₀ ∈ ℕ·L` for every `j`, using the gap lengths of Theorem 3.6. -/
theorem chain_semigroup (hn : 0 < n) (hwt : ∀ k, 0 < wt k)
    (hls : LocSum2 (transStart A lam) (transWt (n := n) wt))
    (hT : ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (transStart A lam) (transLen A B) (transWt wt) x =
        if x ∈ unionIoo A B then 0 else 1) :
    ∀ j : Fin n, InSemigroupL (lengthSet A B) (B j - A ⟨0, hn⟩) := by
  suffices H : ∀ t : ℕ, ∀ ht : t < n, InSemigroupL (lengthSet A B) (B ⟨t, ht⟩ - A ⟨0, hn⟩) from
    fun j ↦ H j.val j.isLt
  intro t
  induction t with
  | zero => intro ht; exact InSemigroupL.of_mem (mem_lengthSet _)
  | succ t ih =>
    intro ht
    have hgap := (gap_semigroup (lam := lam) (m := ⟨t, by omega⟩) hAB hord (by simpa using ht)
      hwt hls hT).1
    have := ((ih (by omega)).add hgap).add (InSemigroupL.of_mem (mem_lengthSet ⟨t + 1, ht⟩))
    convert this using 1
    simp only
    ring

open Classical in
include hAB hord in
/-- **Theorem 3.7 (support structure).**  Every atom `λₖ` of a pure point weak tiling measure is,
up to sign, a nonnegative integer combination of the interval lengths:
`λₖ ∈ ℕ·L` or `-λₖ ∈ ℕ·L`. -/
theorem atom_semigroup (hn : 0 < n) (hwt : ∀ k, 0 < wt k)
    (hls : LocSum2 (transStart A lam) (transWt (n := n) wt))
    (hT : ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (transStart A lam) (transLen A B) (transWt wt) x =
        if x ∈ unionIoo A B then 0 else 1) (k : κ) :
    InSemigroupL (lengthSet A B) (lam k) ∨ InSemigroupL (lengthSet A B) (-lam k) := by
  set i0 : Fin n := ⟨0, hn⟩
  set p : κ × Fin n := (k, i0)
  have hlenpos : 0 < transLen A B p := by simp only [transLen]; linarith [hAB i0]
  have hdisj : ∀ x, transStart A lam p < x → x < transStart A lam p + transLen A B p →
      x ∉ unionIoo A B := fun x h1 h2 ↦ translate_disjoint hAB hwt hls hT p x h1 h2
  have hchain := chain_semigroup (lam := lam) hAB hord hn hwt hls hT
  have hc : transStart A lam p = A i0 + lam k := rfl
  have hl : transLen A B p = B i0 - A i0 := rfl
  rcases component_of_disjoint hn hAB hord (by linarith) hdisj with h | ⟨m, hm, h1, h2⟩ | h
  · -- left half-line
    right
    have hleft := left_semigroup (lam := lam) hAB hord hn hwt hls hT p h
    have := hleft.add (InSemigroupL.of_mem (mem_lengthSet i0))
    convert this using 1
    rw [hc, hl]
    ring
  · -- a gap `m`
    left
    have hstart := (gap_semigroup (lam := lam) hAB hord hm hwt hls hT).2 p h1 h2
    have := hstart.add (hchain m)
    convert this using 1
    rw [hc]
    ring
  · -- right half-line
    left
    have hstart := right_semigroup (lam := lam) hAB hord hn hwt hls hT p h
    have := hstart.add (hchain ⟨n - 1, by omega⟩)
    convert this using 1
    rw [hc]
    ring

end Left

end WeakTiling

end

end AtomicSupport

/-! ## Step M: basic reformulations of the weak tiling condition -/

section MeasureBasics

section

open MeasureTheory Set
open scoped ENNReal

namespace WeakTiling

/-- The translate `x - Ω = {t | x - t ∈ Ω}`. -/
def reflTranslate (Ω : Set ℝ) (x : ℝ) : Set ℝ :=
  (fun t ↦ x - t) ⁻¹' Ω

theorem measurableSet_reflTranslate {Ω : Set ℝ} (hΩ : MeasurableSet Ω) (x : ℝ) :
    MeasurableSet (reflTranslate Ω x) :=
  (measurable_const.sub measurable_id) hΩ

theorem isBounded_reflTranslate {Ω : Set ℝ} (hΩ : Bornology.IsBounded Ω) (x : ℝ) :
    Bornology.IsBounded (reflTranslate Ω x) := by
  obtain ⟨C, hC⟩ := hΩ.exists_norm_le
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mpr ⟨|x| + C, fun t ht ↦ ?_⟩
  have h := hC _ ht
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Real.norm_eq_abs] at h ⊢
  calc |t| = |x - (x - t)| := by ring_nf
    _ ≤ |x| + |x - t| := abs_sub _ _
    _ ≤ |x| + C := by linarith

/-- A locally finite measure gives finite mass to every translate of a bounded set. -/
theorem measure_translate_lt_top {Ω : Set ℝ} (hΩ : Bornology.IsBounded Ω) (ν : Measure ℝ)
    [IsLocallyFiniteMeasure ν] (x : ℝ) : ν (reflTranslate Ω x) < ∞ :=
  (isBounded_reflTranslate hΩ x).measure_lt_top

/-- The convolution against the indicator is the mass of the reflected translate. -/
theorem integral_indicator_translate {Ω : Set ℝ} (hΩ : MeasurableSet Ω) (ν : Measure ℝ)
    (x : ℝ) :
    ∫ t, Ω.indicator (fun _ ↦ (1 : ℝ)) (x - t) ∂ν = (ν (reflTranslate Ω x)).toReal := by
  have : (fun t ↦ Ω.indicator (fun _ ↦ (1 : ℝ)) (x - t)) =
      (reflTranslate Ω x).indicator 1 := by
    funext t
    by_cases ht : x - t ∈ Ω <;> simp [Set.indicator, reflTranslate, ht]
  rw [this, integral_indicator_one (measurableSet_reflTranslate hΩ x)]
  rfl

/-- **Measure form of the weak tiling condition.**  `ν(x - Ω) = 1_{Ωᶜ}(x)` for a.e. `x`. -/
theorem weakTiling_measure_eq {Ω : Set ℝ} {ν : Measure ℝ} (h : IsWeakTilingMeasure Ω ν) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ν (reflTranslate Ω x) = ENNReal.ofReal (Ωᶜ.indicator (fun _ ↦ (1 : ℝ)) x) := by
  obtain ⟨hbd, hmeas, hlf, hae⟩ := h
  filter_upwards [hae] with x hx
  rw [integral_indicator_translate hmeas ν x] at hx
  rw [← hx, ENNReal.ofReal_toReal (measure_translate_lt_top hbd ν x).ne]

/-- **Inside `Ω`**: for a.e. `x ∈ Ω`, `ν` has no mass in `x - Ω`. -/
theorem weakTiling_inside {Ω : Set ℝ} {ν : Measure ℝ} (h : IsWeakTilingMeasure Ω ν) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ω → ν (reflTranslate Ω x) = 0 := by
  filter_upwards [weakTiling_measure_eq h] with x hx hxΩ
  rw [hx]
  simp [hxΩ]

/-- **Normalization `μ = δ₀ + ν`**: `μ(x - Ω) = 1` for a.e. `x`, i.e. `1_Ω * μ = 1`. -/
theorem weakTiling_normalized {Ω : Set ℝ} {ν : Measure ℝ} (h : IsWeakTilingMeasure Ω ν) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ((Measure.dirac (0 : ℝ) + ν : Measure ℝ)) (reflTranslate Ω x) = 1 := by
  have hmeas := h.2.1
  filter_upwards [weakTiling_measure_eq h] with x hx
  rw [Measure.add_apply, hx, Measure.dirac_apply' _ (measurableSet_reflTranslate hmeas x)]
  by_cases hxΩ : x ∈ Ω
  · have h0 : (0 : ℝ) ∈ reflTranslate Ω x := by simpa [reflTranslate] using hxΩ
    simp [Set.indicator_of_mem h0, hxΩ]
  · have h0 : (0 : ℝ) ∉ reflTranslate Ω x := by simpa [reflTranslate] using hxΩ
    simp [Set.indicator_of_notMem h0, hxΩ]

/-- **The support avoids the difference set.**  If `Ω` is open, then no point `x - y` with
`x, y ∈ Ω` lies in `supp ν`.  In particular `0 ∉ supp ν` when `Ω ≠ ∅`, and `supp ν` misses the
open interval `(-(b-a), b-a)` for every component `(a, b)` of `Ω`. -/
theorem sub_notMem_support {Ω : Set ℝ} {ν : Measure ℝ} (h : IsWeakTilingMeasure Ω ν)
    (hopen : IsOpen Ω) {x y : ℝ} (hx : x ∈ Ω) (hy : y ∈ Ω) : x - y ∉ ν.support := by
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.isOpen_iff.mp hopen x hx
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hopen y hy
  set r := min r₁ r₂ with hr
  have hrpos : 0 < r := lt_min hr₁ hr₂
  -- a good point `x'` near `x`
  have hpos : (volume : Measure ℝ) (Metric.ball x r) ≠ 0 := by
    rw [Real.volume_ball]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  obtain ⟨x', hx'ball, hx'good⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae (weakTiling_inside h))
  have hx'Ω : x' ∈ Ω := hball₁ (Metric.ball_subset_ball (min_le_left _ _) hx'ball)
  have hzero := hx'good hx'Ω
  rw [Measure.notMem_support_iff_exists]
  refine ⟨reflTranslate Ω x', ?_, hzero⟩
  have hopenT : IsOpen (reflTranslate Ω x') := hopen.preimage (continuous_const.sub continuous_id)
  refine hopenT.mem_nhds ?_
  show x' - (x - y) ∈ Ω
  apply hball₂
  rw [Metric.mem_ball, Real.dist_eq]
  have hd : |x' - x| < r := by rwa [Metric.mem_ball, Real.dist_eq] at hx'ball
  have : x' - (x - y) - y = x' - x := by ring
  rw [this]
  exact lt_of_lt_of_le hd (min_le_right _ _)

/-- `0 ∉ supp ν` for a weak tiling measure of a nonempty open set. -/
theorem zero_notMem_support {Ω : Set ℝ} {ν : Measure ℝ} (h : IsWeakTilingMeasure Ω ν)
    (hopen : IsOpen Ω) (hne : Ω.Nonempty) : (0 : ℝ) ∉ ν.support := by
  obtain ⟨x, hx⟩ := hne
  have := sub_notMem_support h hopen hx hx
  rwa [sub_self] at this

end WeakTiling

end

end MeasureBasics

/-! ## Step M on the Formal Conjectures definitions: pure point weak tiling measures -/

section PurePointFC

section

open MeasureTheory Finset
open scoped ENNReal

namespace WeakTiling

variable {n : ℕ} {A B : Fin n → ℝ} {κ : Type*} {lam wt : κ → ℝ}

/-- The components are disjoint: a point lies in at most one of them. -/
theorem unique_component (hord : ∀ i j : Fin n, i < j → B i < A j) {y : ℝ} {i j : Fin n}
    (hi : A i < y ∧ y < B i) (hj : A j < y ∧ y < B j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · linarith [hord i j h, hi.2, hj.1]
  · linarith [hord j i h, hj.2, hi.1]

/-- A pure point measure with the given atoms and weights. -/
noncomputable def purePoint (lam wt : κ → ℝ) : Measure ℝ :=
  Measure.sum fun k ↦ ENNReal.ofReal (wt k) • Measure.dirac (lam k)

open Classical in
/-- The mass of a reflected translate under a pure point measure. -/
theorem purePoint_reflTranslate (hord : ∀ i j : Fin n, i < j → B i < A j) (x : ℝ) :
    purePoint lam wt (reflTranslate (unionIoo A B) x) =
      ∑' p : κ × Fin n, if transStart A lam p < x ∧ x < transStart A lam p + transLen A B p
        then ENNReal.ofReal (transWt wt p) else 0 := by
  have hmeas : MeasurableSet (reflTranslate (unionIoo A B) x) :=
    measurableSet_reflTranslate (MeasurableSet.iUnion fun i ↦ measurableSet_Ioo) x
  set g : κ × Fin n → ℝ≥0∞ := fun p ↦ if transStart A lam p < x ∧
    x < transStart A lam p + transLen A B p then ENNReal.ofReal (transWt wt p) else 0 with hg
  have hprod : (∑' p : κ × Fin n, g p) = ∑' k, ∑' i, g (k, i) :=
    ENNReal.tsum_prod (f := fun k i ↦ g (k, i))
  rw [purePoint, Measure.sum_apply _ hmeas, hprod]
  refine tsum_congr fun k ↦ ?_
  simp only [hg]
  rw [Measure.smul_apply, Measure.dirac_apply' _ hmeas, tsum_fintype, smul_eq_mul]
  simp only [transStart, transLen, transWt]
  by_cases hk : lam k ∈ reflTranslate (unionIoo A B) x
  · rw [Set.indicator_of_mem hk, Pi.one_apply, mul_one]
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (show x - lam k ∈ unionIoo A B from hk)
    rw [Finset.sum_eq_single i]
    · have hc : A i + lam k < x ∧ x < A i + lam k + (B i - A i) :=
        ⟨by linarith [hi.1], by linarith [hi.2]⟩
      simp [hc]
    · intro j _ hji
      have hc : ¬ (A j + lam k < x ∧ x < A j + lam k + (B j - A j)) := fun hc ↦
        hji (unique_component hord ⟨by linarith [hc.1], by linarith [hc.2]⟩ hi)
      simp [hc]
    · simp
  · rw [Set.indicator_of_notMem hk, mul_zero]
    symm
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hc : ¬ (A i + lam k < x ∧ x < A i + lam k + (B i - A i)) := fun hc ↦
      hk (show x - lam k ∈ unionIoo A B from
        Set.mem_iUnion.mpr ⟨i, by linarith [hc.1], by linarith [hc.2]⟩)
    simp [hc]

open Classical in
/-- **The atom-level tiling identity** from FC's definition. -/
theorem transCover_ae (hord : ∀ i j : Fin n, i < j → B i < A j) (hwt : ∀ k, 0 < wt k)
    (h : IsWeakTilingMeasure (unionIoo A B) (purePoint lam wt)) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      coverTsum (transStart A lam) (transLen A B) (transWt wt) x =
        if x ∈ unionIoo A B then 0 else 1 := by
  have hbd := h.1
  have hlf := h.2.2.1
  filter_upwards [weakTiling_measure_eq h] with x hx
  have hfin : purePoint lam wt (reflTranslate (unionIoo A B) x) ≠ ∞ :=
    (measure_translate_lt_top hbd _ x).ne
  rw [purePoint_reflTranslate hord] at hx hfin
  have hterm : ∀ p : κ × Fin n, (if transStart A lam p < x ∧
      x < transStart A lam p + transLen A B p then ENNReal.ofReal (transWt wt p) else 0) ≠ ∞ :=
    fun p ↦ by split_ifs <;> simp
  have hreal := congrArg ENNReal.toReal hx
  rw [ENNReal.tsum_toReal_eq hterm, ENNReal.toReal_ofReal (by
    by_cases hxΩ : x ∈ unionIoo A B <;> simp [hxΩ])] at hreal
  unfold coverTsum
  rw [show (∑' p : κ × Fin n, if transStart A lam p < x ∧ x < transStart A lam p +
      transLen A B p then transWt wt p else 0) = ∑' p : κ × Fin n,
      (if transStart A lam p < x ∧ x < transStart A lam p + transLen A B p then
        ENNReal.ofReal (transWt wt p) else 0).toReal from
    tsum_congr fun p ↦ by split_ifs <;> simp [transWt, (hwt p.1).le]]
  rw [hreal]
  by_cases hxΩ : x ∈ unionIoo A B <;> simp [hxΩ]

open Classical in
/-- **Two-sided local summability** from local finiteness of the pure point measure. -/
theorem locSum2_of_locallyFinite (hwt : ∀ k, 0 < wt k)
    [hlf : IsLocallyFiniteMeasure (purePoint lam wt)] :
    LocSum2 (transStart A lam) (transWt (n := n) wt) := by
  intro R
  set R' := R + ∑ i, |A i| with hR'
  set g : κ → ℝ := fun k ↦ if |lam k| ≤ R' then wt k else 0 with hg
  have hmeas : MeasurableSet (Set.Icc (-R') R') := measurableSet_Icc
  have hfin : purePoint lam wt (Set.Icc (-R') R') ≠ ∞ := (isCompact_Icc.measure_lt_top).ne
  rw [purePoint, Measure.sum_apply _ hmeas] at hfin
  have hsg : Summable g := by
    refine (ENNReal.summable_toReal hfin).congr fun k ↦ ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hmeas, smul_eq_mul, hg]
    dsimp only
    by_cases hk : |lam k| ≤ R'
    · rw [ite_eq_left hk, Set.indicator_of_mem (show lam k ∈ Set.Icc (-R') R' from abs_le.mp hk),
        Pi.one_apply, mul_one,
        ENNReal.toReal_ofReal (hwt k).le]
    · rw [ite_eq_right hk, Set.indicator_of_notMem (show lam k ∉ Set.Icc (-R') R' from
        fun h ↦ hk (abs_le.mpr h)), mul_zero,
        ENNReal.toReal_zero]
  have hg0 : ∀ k, 0 ≤ g k := fun k ↦ by simp only [hg]; split_ifs <;> linarith [hwt k]
  have hsprod : Summable fun p : κ × Fin n ↦ g p.1 := by
    rw [summable_prod_of_nonneg (fun p ↦ hg0 p.1)]
    refine ⟨fun k ↦ Summable.of_finite, ?_⟩
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hsg.mul_left _
  refine Summable.of_nonneg_of_le (fun p ↦ by unfold transWt; split_ifs <;> linarith [hwt p.1])
    (fun p ↦ ?_) hsprod
  have hA : |A p.2| ≤ ∑ i, |A i| :=
    Finset.single_le_sum (f := fun i ↦ |A i|) (fun i _ ↦ abs_nonneg _) (mem_univ p.2)
  have himp : |A p.2 + lam p.1| ≤ R → |lam p.1| ≤ R' := fun h1 ↦
    calc |lam p.1| = |(A p.2 + lam p.1) - A p.2| := by ring_nf
      _ ≤ |A p.2 + lam p.1| + |A p.2| := abs_sub _ _
      _ ≤ R' := by rw [hR']; linarith
  by_cases h1 : |transStart A lam p| ≤ R
  · rw [ite_eq_left h1]
    have hl : |lam p.1| ≤ R' := himp h1
    show wt p.1 ≤ g p.1
    rw [hg]
    dsimp only
    rw [ite_eq_left hl]
  · rw [ite_eq_right h1]
    exact hg0 p.1

/-- The support of a pure point measure lies in the closure of its atoms. -/
theorem support_purePoint_subset (lam wt : κ → ℝ) :
    (purePoint lam wt).support ⊆ closure (Set.range lam) := by
  intro x hx
  by_contra hxc
  apply (Measure.notMem_support_iff_exists).mpr _ hx
  refine ⟨(closure (Set.range lam))ᶜ, isClosed_closure.isOpen_compl.mem_nhds hxc, ?_⟩
  rw [purePoint, Measure.sum_apply _ isClosed_closure.isOpen_compl.measurableSet]
  refine ENNReal.tsum_eq_zero.mpr fun k ↦ ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ isClosed_closure.isOpen_compl.measurableSet,
    Set.indicator_of_notMem (show lam k ∉ (closure (Set.range lam))ᶜ from
      fun h ↦ h (subset_closure ⟨k, rfl⟩)), smul_zero]

/-- A set whose bounded parts are finite contains the closure of any subset. -/
theorem closure_subset_of_locallyFinite {S T : Set ℝ} (hTS : T ⊆ S)
    (hfin : ∀ x : ℝ, (S ∩ Set.Icc (x - 1) (x + 1)).Finite) : closure T ⊆ S := by
  intro x hx
  by_contra hxS
  set F := S ∩ Set.Icc (x - 1) (x + 1)
  have hxF : x ∉ F := fun h ↦ hxS h.1
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hfin x).isClosed.isOpen_compl x hxF
  obtain ⟨y, hyT, hy⟩ := Metric.mem_closure_iff.mp hx (min δ 1) (lt_min hδ one_pos)
  have hyF : y ∈ F := by
    refine ⟨hTS hyT, ?_⟩
    rw [dist_comm, Real.dist_eq] at hy
    have := min_le_right δ 1
    constructor <;> cases abs_cases (y - x) <;> linarith
  apply hball (show y ∈ Metric.ball x δ from by
    rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hy (min_le_left _ _)) hyF

/-- The signed semigroup `ℕ·L ∪ -ℕ·L` has finite bounded parts. -/
theorem signedSemigroup_finite (L : Finset ℝ) {ℓmin : ℝ} (hℓ : 0 < ℓmin)
    (hL : ∀ l ∈ L, ℓmin ≤ l) (x : ℝ) :
    ({z | InSemigroupL L z ∨ InSemigroupL L (-z)} ∩ Set.Icc (x - 1) (x + 1)).Finite := by
  have h1 := finite_semigroupL_le L hℓ hL (|x| + 1)
  refine (h1.union (h1.image fun z ↦ -z)).subset ?_
  rintro z ⟨hz | hz, hz1, hz2⟩
  · left
    refine ⟨hz, ?_⟩
    cases abs_cases x <;> linarith
  · right
    refine ⟨-z, ⟨hz, ?_⟩, by ring⟩
    cases abs_cases x <;> linarith

/-- **Theorem 3.7 of the source paper, on FC's definitions (pure point case).**

Let `Ω = ⋃ᵢ (Aᵢ, Bᵢ)` be ordered with `n ≥ 1` components, and let `ν = ∑ₖ wₖ δ_{λₖ}`
(`wₖ > 0`) be a weak tiling measure for `Ω` in the sense of Formal Conjectures.  Then the support
of `ν` lies in `±ℕ·L`, the nonnegative integer combinations of the interval lengths and their
negatives. -/
theorem support_subset_signedSemigroup (hn : 0 < n) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j) (hwt : ∀ k, 0 < wt k)
    (h : IsWeakTilingMeasure (unionIoo A B) (purePoint lam wt)) :
    (purePoint lam wt).support ⊆
      {z | InSemigroupL (lengthSet A B) z ∨ InSemigroupL (lengthSet A B) (-z)} := by
  have hlf : IsLocallyFiniteMeasure (purePoint lam wt) := h.2.2.1
  have hT := transCover_ae hord hwt h
  have hls := locSum2_of_locallyFinite (A := A) (lam := lam) hwt
  have hatoms : Set.range lam ⊆
      {z | InSemigroupL (lengthSet A B) z ∨ InSemigroupL (lengthSet A B) (-z)} := by
    rintro _ ⟨k, rfl⟩
    exact atom_semigroup hAB hord hn hwt hls hT k
  refine (support_purePoint_subset lam wt).trans (closure_subset_of_locallyFinite hatoms ?_)
  exact signedSemigroup_finite _ (minLength_pos hn hAB) (fun l hl ↦ by
    obtain ⟨i, -, rfl⟩ := mem_image.mp hl
    exact minLength_le hn i)

end WeakTiling

end

end PurePointFC

/-! ## Theorem 3.2 of the source paper: weak tiling measures are pure point -/

section PurePointTheorem

section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeakTiling

variable {n : ℕ} {a b : Fin n → ℝ}

/-- **The interval shift identity.** -/
theorem interval_shift (ρ : Measure ℝ) {x y p q : ℝ} (hxy : x < y) (hpq : p < q) :
    ρ (Ioo (x - q) (x - p)) + ρ (Ico (x - p) (y - p)) =
      ρ (Ioc (x - q) (y - q)) + ρ (Ioo (y - q) (y - p)) := by
  have h1 : Ioo (x - q) (x - p) ∪ Ico (x - p) (y - p) = Ioo (x - q) (y - p) :=
    Ioo_union_Ico_eq_Ioo (by linarith) (by linarith)
  have h2 : Ioc (x - q) (y - q) ∪ Ioo (y - q) (y - p) = Ioo (x - q) (y - p) :=
    Ioc_union_Ioo_eq_Ioo (by linarith) (by linarith)
  have d1 : Disjoint (Ioo (x - q) (x - p)) (Ico (x - p) (y - p)) :=
    Set.disjoint_left.mpr fun t h h' ↦ by linarith [h.2, h'.1]
  have d2 : Disjoint (Ioc (x - q) (y - q)) (Ioo (y - q) (y - p)) :=
    Set.disjoint_left.mpr fun t h h' ↦ by linarith [h.2, h'.1]
  rw [← measure_union d1 measurableSet_Ico, ← measure_union d2 measurableSet_Ioo, h1, h2]

/-- The reflected translate splits into the disjoint component translates. -/
theorem reflTranslate_eq_iUnion (x : ℝ) :
    reflTranslate (unionIoo a b) x = ⋃ j, Ioo (x - b j) (x - a j) := by
  ext t
  simp only [reflTranslate, unionIoo, mem_preimage, mem_iUnion, mem_Ioo]
  constructor <;> rintro ⟨j, h1, h2⟩ <;> exact ⟨j, by linarith, by linarith⟩

/-- `ρ(x - Ω) = ∑ⱼ ρ((x-bⱼ, x-aⱼ))`. -/
theorem measure_reflTranslate_eq_sum (hord : ∀ i j : Fin n, i < j → b i < a j) (ρ : Measure ℝ)
    (x : ℝ) :
    ρ (reflTranslate (unionIoo a b) x) = ∑ j, ρ (Ioo (x - b j) (x - a j)) := by
  rw [reflTranslate_eq_iUnion, measure_iUnion _ (fun j ↦ measurableSet_Ioo), tsum_fintype]
  intro i j hij
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  rintro t ⟨h1, h2⟩ ⟨h3, h4⟩
  exact hij (unique_component (y := x - t) hord ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩)

/-- **Summed shift identity.** -/
theorem shift_sum (hab : ∀ i, a i < b i) (hord : ∀ i j : Fin n, i < j → b i < a j)
    (ρ : Measure ℝ) {x y : ℝ} (hxy : x < y) :
    ρ (reflTranslate (unionIoo a b) x) + ∑ j, ρ (Ico (x - a j) (y - a j)) =
      ∑ j, ρ (Ioc (x - b j) (y - b j)) + ρ (reflTranslate (unionIoo a b) y) := by
  rw [measure_reflTranslate_eq_sum hord, measure_reflTranslate_eq_sum hord,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ interval_shift ρ hxy (hab j)

/-- Measures of small open neighbourhoods tend to the atom. -/
theorem tendsto_nhd_measure (ρ : Measure ℝ) [IsLocallyFiniteMeasure ρ] (c : ℝ) :
    Tendsto (fun k : ℕ ↦ ρ (Ioo (c - 1 / (k + 1)) (c + 1 / (k + 1)))) atTop (𝓝 (ρ {c})) := by
  set s : ℕ → Set ℝ := fun k ↦ Ioo (c - 1 / (k + 1)) (c + 1 / (k + 1)) with hs
  have hanti : Antitone s := by
    intro k l hkl
    have : (1 : ℝ) / (l + 1) ≤ 1 / (k + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hkl
    exact Ioo_subset_Ioo (by linarith) (by linarith)
  have hinter : ⋂ k, s k = {c} := by
    ext t
    simp only [hs, mem_iInter, mem_Ioo, mem_singleton_iff]
    constructor
    · intro h
      by_contra hne
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (abs_pos.mpr (sub_ne_zero.mpr hne))
      have := h k
      exact absurd (abs_lt.mpr ⟨by linarith [this.1], by linarith [this.2]⟩) (not_lt.mpr hk.le)
    · rintro rfl k
      constructor <;> linarith [one_div_pos.mpr (by positivity : (0 : ℝ) < k + 1)]
  have hfin : ∃ k, ρ (s k) ≠ ∞ := ⟨0, measure_Ioo_lt_top.ne⟩
  have ht := tendsto_measure_iInter_atTop (fun k ↦ measurableSet_Ioo.nullMeasurableSet) hanti hfin
  rwa [hinter] at ht

/-- Sums of measures of small open neighbourhoods approach the sum of the atoms. -/
theorem exists_nhd_sum_le (ρ : Measure ℝ) [IsLocallyFiniteMeasure ρ] (c : Fin n → ℝ)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ ε > 0, ∑ j, ρ (Ioo (c j - ε) (c j + ε)) ≤ ∑ j, ρ {c j} + δ := by
  have ht := tendsto_finsetSum Finset.univ fun j _ ↦ tendsto_nhd_measure ρ (c j)
  have hlt : ∑ j, ρ {c j} < ∑ j, ρ {c j} + δ := ENNReal.lt_add_right
    (ENNReal.sum_ne_top.mpr fun j _ ↦ isCompact_singleton.measure_lt_top.ne) hδ
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hlt)).exists
  exact ⟨1 / (k + 1), by positivity, hk.le⟩

/-- A property holding almost everywhere holds somewhere in every nonempty open interval. -/
theorem exists_mem_Ioo_of_ae {P : ℝ → Prop} (h : ∀ᵐ x ∂(volume : Measure ℝ), P x) {u v : ℝ}
    (huv : u < v) : ∃ x ∈ Ioo u v, P x :=
  Measure.exists_mem_of_measure_ne_zero_of_ae
    (by rw [Real.volume_Ioo, Ne, ENNReal.ofReal_eq_zero, not_le, sub_pos]; exact huv)
    (ae_restrict_of_ae h)

/-- Near any `t` there are good points `x < t < y` where the two interval sums agree. -/
theorem good_pair (hab : ∀ i, a i < b i) (hord : ∀ i j : Fin n, i < j → b i < a j)
    (ρ : Measure ℝ) (hgood : ∀ᵐ x ∂(volume : Measure ℝ), ρ (reflTranslate (unionIoo a b) x) = 1)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ x y, t - ε < x ∧ x < t ∧ t < y ∧ y < t + ε ∧
      ∑ j, ρ (Ico (x - a j) (y - a j)) = ∑ j, ρ (Ioc (x - b j) (y - b j)) := by
  obtain ⟨x, hx, hxg⟩ := exists_mem_Ioo_of_ae hgood (show t - ε < t by linarith)
  obtain ⟨y, hy, hyg⟩ := exists_mem_Ioo_of_ae hgood (show t < t + ε by linarith)
  refine ⟨x, y, hx.1, hx.2, hy.1, hy.2, ?_⟩
  have := shift_sum hab hord ρ (hx.2.trans hy.1)
  rw [hxg, hyg, add_comm] at this
  exact (ENNReal.add_left_inj ENNReal.one_ne_top).mp this

/-- **Atom identity.**  `∑ⱼ ρ{t-aⱼ} = ∑ⱼ ρ{t-bⱼ}` whenever `ρ(x - Ω) = 1` for a.e. `x`. -/
theorem atom_identity (hab : ∀ i, a i < b i) (hord : ∀ i j : Fin n, i < j → b i < a j)
    (ρ : Measure ℝ) [IsLocallyFiniteMeasure ρ]
    (hgood : ∀ᵐ x ∂(volume : Measure ℝ), ρ (reflTranslate (unionIoo a b) x) = 1) (t : ℝ) :
    ∑ j, ρ {t - a j} = ∑ j, ρ {t - b j} := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    obtain ⟨ε, hε, hle⟩ := exists_nhd_sum_le ρ (fun j ↦ t - b j) (δ := δ)
      (ENNReal.coe_ne_zero.mpr hδ.ne')
    obtain ⟨x, y, h1, h2, h3, h4, heq⟩ := good_pair hab hord ρ hgood t hε
    calc ∑ j, ρ {t - a j} ≤ ∑ j, ρ (Ico (x - a j) (y - a j)) :=
          Finset.sum_le_sum fun j _ ↦ measure_mono
            (singleton_subset_iff.mpr ⟨by linarith, by linarith⟩)
      _ = ∑ j, ρ (Ioc (x - b j) (y - b j)) := heq
      _ ≤ ∑ j, ρ (Ioo (t - b j - ε) (t - b j + ε)) :=
          Finset.sum_le_sum fun j _ ↦ measure_mono
            (fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      _ ≤ _ := hle
  · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    obtain ⟨ε, hε, hle⟩ := exists_nhd_sum_le ρ (fun j ↦ t - a j) (δ := δ)
      (ENNReal.coe_ne_zero.mpr hδ.ne')
    obtain ⟨x, y, h1, h2, h3, h4, heq⟩ := good_pair hab hord ρ hgood t hε
    calc ∑ j, ρ {t - b j} ≤ ∑ j, ρ (Ioc (x - b j) (y - b j)) :=
          Finset.sum_le_sum fun j _ ↦ measure_mono
            (singleton_subset_iff.mpr ⟨by linarith, by linarith⟩)
      _ = ∑ j, ρ (Ico (x - a j) (y - a j)) := heq.symm
      _ ≤ ∑ j, ρ (Ioo (t - a j - ε) (t - a j + ε)) :=
          Finset.sum_le_sum fun j _ ↦ measure_mono
            (fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      _ ≤ _ := hle

/-- The atomic part `∑ₛ ρ{s} δₛ` of a measure. -/
noncomputable def atomPart (ρ : Measure ℝ) : Measure ℝ :=
  Measure.sum fun s : ℝ ↦ ρ {s} • Measure.dirac s

theorem atomPart_apply (ρ : Measure ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    atomPart ρ S = ∑' s, S.indicator (fun s ↦ ρ {s}) s := by
  rw [atomPart, Measure.sum_apply _ hS]
  refine tsum_congr fun s ↦ ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]
  by_cases h : s ∈ S <;> simp [h]

theorem atomPart_le (ρ : Measure ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    atomPart ρ S ≤ ρ S := by
  rw [atomPart_apply ρ hS, ← tsum_subtype]
  calc ∑' s : S, ρ {(s : ℝ)} ≤ ρ (⋃ s : S, {(s : ℝ)}) :=
        tsum_meas_le_meas_iUnion_of_disjoint ρ (fun _ ↦ measurableSet_singleton _)
          fun s t hst ↦ by
            simp only [Function.onFun, Set.disjoint_singleton]
            exact Subtype.coe_injective.ne hst
    _ ≤ ρ S := measure_mono (iUnion_subset fun s ↦ singleton_subset_iff.mpr s.2)

/-- Translated atomic masses, summed over the components. -/
theorem atomPart_translate_sum (ρ : Measure ℝ) (c : Fin n → ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    ∑ j, atomPart ρ ((· + c j) ⁻¹' S) = ∑' t, S.indicator (fun t ↦ ∑ j, ρ {t - c j}) t := by
  have key : ∀ j, atomPart ρ ((· + c j) ⁻¹' S) =
      ∑' t, S.indicator (fun t ↦ ρ {t - c j}) t := by
    intro j
    rw [atomPart_apply ρ (measurable_add_const (c j) hS),
      ← (Equiv.subRight (c j)).tsum_eq]
    refine tsum_congr fun t ↦ ?_
    rw [Equiv.subRight_apply]
    by_cases ht : t ∈ S
    · rw [indicator_of_mem (show t - c j ∈ (· + c j) ⁻¹' S by simpa using ht),
        indicator_of_mem ht]
    · rw [indicator_of_notMem (show t - c j ∉ (· + c j) ⁻¹' S by simpa using ht),
        indicator_of_notMem ht]
  simp_rw [key]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  refine tsum_congr fun t ↦ ?_
  by_cases ht : t ∈ S <;> simp [ht]

theorem tsum_Ico_eq_Ioc {h : ℝ → ℝ≥0∞} {x y : ℝ} (hx : h x = 0) (hy : h y = 0) :
    ∑' t, (Ico x y).indicator h t = ∑' t, (Ioc x y).indicator h t := by
  refine tsum_congr fun t ↦ ?_
  by_cases htx : t = x
  · simp [htx, indicator_apply, hx]
  by_cases hty : t = y
  · simp [hty, indicator_apply, hy]
  have : t ∈ Ico x y ↔ t ∈ Ioc x y := by
    simp only [mem_Ico, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm htx), h2.le⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, lt_of_le_of_ne h2 hty⟩
  simp only [indicator_apply]
  exact if_congr this rfl rfl

/-- **Invariance of the atomic tiling function** between atom-free good points. -/
theorem atomPart_shift (hab : ∀ i, a i < b i) (hord : ∀ i j : Fin n, i < j → b i < a j)
    (ρ : Measure ℝ) [IsLocallyFiniteMeasure ρ]
    (hgood : ∀ᵐ x ∂(volume : Measure ℝ), ρ (reflTranslate (unionIoo a b) x) = 1) {x y : ℝ}
    (hxy : x < y) (hx : ∑ j, ρ {x - a j} = 0) (hy : ∑ j, ρ {y - a j} = 0) :
    atomPart ρ (reflTranslate (unionIoo a b) x) = atomPart ρ (reflTranslate (unionIoo a b) y) := by
  have hsh := shift_sum hab hord (atomPart ρ) hxy
  have hA := atomPart_translate_sum ρ a (measurableSet_Ico (a := x) (b := y))
  have hB := atomPart_translate_sum ρ b (measurableSet_Ioc (a := x) (b := y))
  simp only [preimage_add_const_Ico, preimage_add_const_Ioc] at hA hB
  have hid : (fun t ↦ ∑ j, ρ {t - b j}) = fun t ↦ ∑ j, ρ {t - a j} :=
    funext fun t ↦ (atom_identity hab hord ρ hgood t).symm
  rw [hid] at hB
  have hfin : ∑ j, atomPart ρ (Ioc (x - b j) (y - b j)) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun j _ ↦
      ne_top_of_le_ne_top measure_Ioc_lt_top.ne (atomPart_le ρ measurableSet_Ioc)
  rw [hA, tsum_Ico_eq_Ioc hx hy, ← hB, add_comm] at hsh
  exact (ENNReal.add_right_inj hfin).mp hsh

/-- Almost every point is atom-free for the translated atoms. -/
theorem ae_atomFree (ρ : Measure ℝ) [SFinite ρ] (c : Fin n → ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ), ∑ j, ρ {x - c j} = 0 := by
  have hC : {s : ℝ | 0 < ρ {s}}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun s ↦ measurableSet_singleton s)
      fun s t hst ↦ by
        simp only [Function.onFun, Set.disjoint_singleton]
        exact hst
  have hD : (⋃ j, (· + c j) '' {s : ℝ | 0 < ρ {s}}).Countable :=
    countable_iUnion fun j ↦ hC.image _
  filter_upwards [hD.ae_notMem volume] with x hx
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  by_contra hne
  exact hx (mem_iUnion.mpr ⟨j, x - c j, pos_iff_ne_zero.mpr hne, sub_add_cancel x (c j)⟩)

theorem measurableSet_unionIoo : MeasurableSet (unionIoo a b) :=
  MeasurableSet.iUnion fun _ ↦ measurableSet_Ioo

/-- A good point gives a component. -/
theorem exists_component {ρ : Measure ℝ}
    (hgood : ∀ᵐ x ∂(volume : Measure ℝ), ρ (reflTranslate (unionIoo a b) x) = 1) :
    Nonempty (Fin n) := by
  obtain ⟨x, -, hx⟩ := exists_mem_Ioo_of_ae hgood zero_lt_one
  obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero (hx ▸ one_ne_zero : ρ _ ≠ 0)
  obtain ⟨j, -⟩ := mem_iUnion.mp ht
  exact ⟨j⟩

/-- **The atomic part carries the full tiling mass** at almost every point. -/
theorem atomPart_reflTranslate_ae (hab : ∀ i, a i < b i)
    (hord : ∀ i j : Fin n, i < j → b i < a j) (ρ : Measure ℝ) [IsLocallyFiniteMeasure ρ]
    (hgood : ∀ᵐ x ∂(volume : Measure ℝ), ρ (reflTranslate (unionIoo a b) x) = 1)
    (h0 : 1 ≤ ρ {0}) :
    ∀ᵐ x ∂(volume : Measure ℝ), atomPart ρ (reflTranslate (unionIoo a b) x) = 1 ∧
      ρ (reflTranslate (unionIoo a b) x) = 1 := by
  have hE := hgood.and (ae_atomFree ρ a)
  obtain ⟨j0⟩ := exists_component hgood
  obtain ⟨x0, hx0, hg0, hf0⟩ := exists_mem_Ioo_of_ae hE (hab j0)
  have hmeas := measurableSet_reflTranslate (measurableSet_unionIoo (a := a) (b := b))
  have hbase : atomPart ρ (reflTranslate (unionIoo a b) x0) = 1 := by
    refine le_antisymm (hg0 ▸ atomPart_le ρ (hmeas x0)) ?_
    have hmem : (0 : ℝ) ∈ reflTranslate (unionIoo a b) x0 :=
      mem_iUnion.mpr ⟨j0, by simpa using hx0⟩
    rw [atomPart_apply ρ (hmeas x0)]
    refine h0.trans (le_of_eq_of_le ?_ (ENNReal.le_tsum 0))
    rw [indicator_of_mem hmem]
  filter_upwards [hE] with x ⟨hg, hf⟩
  refine ⟨?_, hg⟩
  rcases lt_trichotomy x x0 with hlt | rfl | hgt
  · rw [atomPart_shift hab hord ρ hgood hlt hf hf0, hbase]
  · exact hbase
  · rw [← atomPart_shift hab hord ρ hgood hgt hf0 hf, hbase]

theorem ENNReal.eq_of_le_of_add_eq {p q r s : ℝ≥0∞} (hpr : p ≤ r) (hqs : q ≤ s)
    (h : p + q = r + s) (hfin : r + s ≠ ∞) : p = r := by
  refine le_antisymm hpr (not_lt.mp fun hlt ↦ ?_)
  have hq : q ≠ ∞ := ne_top_of_le_ne_top (ne_top_of_le_ne_top hfin le_add_self) hqs
  exact (ENNReal.add_lt_add_of_lt_of_le hq hlt hqs).ne h

/-- Agreement on short intervals. -/
theorem atomPart_Ioc_short
    (ρ : Measure ℝ) [IsLocallyFiniteMeasure ρ]
    (hkey : ∀ᵐ x ∂(volume : Measure ℝ), atomPart ρ (reflTranslate (unionIoo a b) x) = 1 ∧
      ρ (reflTranslate (unionIoo a b) x) = 1)
    (j0 : Fin n) {p h : ℝ} (hh : h < b j0 - a j0) :
    atomPart ρ (Ioc p (p + h)) = ρ (Ioc p (p + h)) := by
  obtain ⟨x, hx, hxa, hxr⟩ := exists_mem_Ioo_of_ae hkey (show p + h + a j0 < p + b j0 by linarith)
  set U := reflTranslate (unionIoo a b) x
  have hU : MeasurableSet U := measurableSet_reflTranslate measurableSet_unionIoo x
  have hSU : Ioc p (p + h) ⊆ U := fun t ht ↦
    mem_iUnion.mpr ⟨j0, by linarith [hx.1, ht.2], by linarith [hx.2, ht.1]⟩
  have e1 := measure_inter_add_sdiff U (measurableSet_Ioc (a := p) (b := p + h)) (μ := atomPart ρ)
  have e2 := measure_inter_add_sdiff U (measurableSet_Ioc (a := p) (b := p + h)) (μ := ρ)
  rw [inter_eq_right.mpr hSU] at e1 e2
  refine ENNReal.eq_of_le_of_add_eq (atomPart_le ρ measurableSet_Ioc)
    (atomPart_le ρ (hU.diff measurableSet_Ioc)) (by rw [e1, e2, hxa, hxr]) (by rw [e2, hxr]; simp)

/-- Agreement on all intervals `(u, v]`. -/
theorem atomPart_Ioc (hab : ∀ i, a i < b i)
    (ρ : Measure ℝ) [IsLocallyFiniteMeasure ρ]
    (hkey : ∀ᵐ x ∂(volume : Measure ℝ), atomPart ρ (reflTranslate (unionIoo a b) x) = 1 ∧
      ρ (reflTranslate (unionIoo a b) x) = 1)
    (j0 : Fin n) : ∀ N : ℕ, ∀ u v : ℝ, v ≤ u + N * ((b j0 - a j0) / 2) →
      atomPart ρ (Ioc u v) = ρ (Ioc u v) := by
  have hL := hab j0
  intro N
  induction N with
  | zero =>
    intro u v hv
    rw [Ioc_eq_empty (not_lt.mpr (by simpa using hv))]
    simp
  | succ N ih =>
    intro u v hv
    by_cases hs : v ≤ u + (b j0 - a j0) / 2
    · have : Ioc u v = Ioc u (u + (v - u)) := by rw [add_sub_cancel]
      rw [this]
      exact atomPart_Ioc_short ρ hkey j0 (by linarith)
    · have hs' := not_le.mp hs
      set m := u + (b j0 - a j0) / 2 with hm
      have hsplit : Ioc u v = Ioc u m ∪ Ioc m v :=
        (Ioc_union_Ioc_eq_Ioc (by rw [hm]; linarith) hs'.le).symm
      have hd : Disjoint (Ioc u m) (Ioc m v) :=
        Set.disjoint_left.mpr fun t h h' ↦ by linarith [h.2, h'.1]
      have h1 : atomPart ρ (Ioc u m) = ρ (Ioc u m) :=
        atomPart_Ioc_short ρ hkey j0 (by linarith)
      have h2 : atomPart ρ (Ioc m v) = ρ (Ioc m v) := ih m v (by rw [hm]; push_cast at hv; linarith)
      rw [hsplit, measure_union hd measurableSet_Ioc, measure_union hd measurableSet_Ioc, h1, h2]

/-- **Pure atomicity (general form).**  A locally finite `ρ` with `ρ{0} ≥ 1` and
`ρ(x - Ω) = 1` for a.e. `x` equals its atomic part. -/
theorem eq_atomPart (hab : ∀ i, a i < b i) (hord : ∀ i j : Fin n, i < j → b i < a j)
    (ρ : Measure ℝ) [IsLocallyFiniteMeasure ρ]
    (hgood : ∀ᵐ x ∂(volume : Measure ℝ), ρ (reflTranslate (unionIoo a b) x) = 1)
    (h0 : 1 ≤ ρ {0}) : ρ = atomPart ρ := by
  have hkey := atomPart_reflTranslate_ae hab hord ρ hgood h0
  obtain ⟨j0⟩ := exists_component hgood
  have hL := hab j0
  refine Measure.ext_of_Ioc' ρ (atomPart ρ) (fun u v _ ↦ measure_Ioc_lt_top.ne)
    fun u v _ ↦ ?_
  obtain ⟨N, hN⟩ := exists_nat_ge ((v - u) / ((b j0 - a j0) / 2))
  refine (atomPart_Ioc hab ρ hkey j0 N u v ?_).symm
  have hpos : 0 < (b j0 - a j0) / 2 := by linarith
  rw [div_le_iff₀ hpos] at hN
  linarith

theorem atomPart_add_apply (ρ₁ ρ₂ : Measure ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    atomPart (ρ₁ + ρ₂) S = atomPart ρ₁ S + atomPart ρ₂ S := by
  rw [atomPart_apply _ hS, atomPart_apply _ hS, atomPart_apply _ hS, ← ENNReal.tsum_add]
  refine tsum_congr fun s ↦ ?_
  by_cases hs : s ∈ S <;> simp [hs]

theorem isLocallyFiniteMeasure_dirac_add (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (Measure.dirac (0 : ℝ) + ν) :=
  ⟨fun x ↦ ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, measure_Ioo_lt_top⟩⟩⟩

/-- **Theorem 3.2, measure form.**  A weak tiling measure equals its atomic part. -/
theorem weakTiling_eq_atomPart (hab : ∀ i, a i < b i) (hord : ∀ i j : Fin n, i < j → b i < a j)
    {ν : Measure ℝ} (h : IsWeakTilingMeasure (unionIoo a b) ν) : ν = atomPart ν := by
  haveI : IsLocallyFiniteMeasure ν := h.2.2.1
  haveI := isLocallyFiniteMeasure_dirac_add ν
  have h0 : 1 ≤ (Measure.dirac (0 : ℝ) + ν) {0} := by
    rw [Measure.add_apply, Measure.dirac_apply_of_mem (mem_singleton 0)]
    exact le_self_add
  have hρ := eq_atomPart hab hord _ (weakTiling_normalized h) h0
  refine Measure.ext_of_Ioc' ν (atomPart ν) (fun u v _ ↦ measure_Ioc_lt_top.ne) fun u v _ ↦ ?_
  have e := congrArg (fun m : Measure ℝ ↦ m (Ioc u v)) hρ
  rw [atomPart_add_apply _ _ measurableSet_Ioc, Measure.add_apply, add_comm (atomPart _ _),
    add_comm (Measure.dirac _ _)] at e
  refine (ENNReal.eq_of_le_of_add_eq (atomPart_le ν measurableSet_Ioc)
    (atomPart_le _ measurableSet_Ioc) e.symm ?_).symm
  exact ENNReal.add_ne_top.mpr ⟨measure_Ioc_lt_top.ne, measure_ne_top _ _⟩

/-- The atoms of `ν`. -/
def atomSet (ν : Measure ℝ) : Set ℝ := {s | ν {s} ≠ 0}

/-- **Theorem 3.2, pure point form.**  A weak tiling measure is `purePoint` over its atoms, with
positive weights. -/
theorem weakTiling_eq_purePoint (hab : ∀ i, a i < b i) (hord : ∀ i j : Fin n, i < j → b i < a j)
    {ν : Measure ℝ} (h : IsWeakTilingMeasure (unionIoo a b) ν) :
    (∀ k : atomSet ν, 0 < (ν {(k : ℝ)}).toReal) ∧
      ν = purePoint (fun k : atomSet ν ↦ (k : ℝ)) fun k ↦ (ν {(k : ℝ)}).toReal := by
  haveI : IsLocallyFiniteMeasure ν := h.2.2.1
  have hfin : ∀ s : ℝ, ν {s} ≠ ∞ := fun s ↦ isCompact_singleton.measure_lt_top.ne
  refine ⟨fun k ↦ ENNReal.toReal_pos k.2 (hfin k), ?_⟩
  conv_lhs => rw [weakTiling_eq_atomPart hab hord h]
  ext S hS
  rw [atomPart_apply ν hS, purePoint, Measure.sum_apply _ hS]
  rw [← tsum_subtype_eq_of_support_subset (s := atomSet ν) (f := S.indicator fun s ↦ ν {s})]
  · refine tsum_congr fun k ↦ ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul,
      ENNReal.ofReal_toReal (hfin k)]
    by_cases hk : (k : ℝ) ∈ S <;> simp [hk]
  · intro s hs
    by_contra hns
    exact hs (by simp [atomSet] at hns; simp [indicator_apply, hns])

/-- **Step M, unconditional.**  The support of every weak tiling measure of `Ω = ⋃ⱼ (aⱼ, bⱼ)`
lies in `ℕL ∪ -ℕL`, where `L` is the set of component lengths. -/
theorem weakTiling_support_subset (hab : ∀ i, a i < b i)
    (hord : ∀ i j : Fin n, i < j → b i < a j) {ν : Measure ℝ}
    (h : IsWeakTilingMeasure (unionIoo a b) ν) :
    ν.support ⊆ {z | InSemigroupL (lengthSet a b) z ∨ InSemigroupL (lengthSet a b) (-z)} := by
  haveI : IsLocallyFiniteMeasure ν := h.2.2.1
  haveI := isLocallyFiniteMeasure_dirac_add ν
  obtain ⟨j0⟩ := exists_component (weakTiling_normalized h)
  obtain ⟨hwt, hpp⟩ := weakTiling_eq_purePoint hab hord h
  rw [hpp] at h ⊢
  exact support_subset_signedSemigroup (Fin.pos j0) hab hord hwt h

end WeakTiling

end

end PurePointTheorem

/-! ## Positive coordinate rows for a finitely generated length semigroup -/

section CoordinateRows

section

open Finset
open MeasureTheory
open scoped ENNReal

namespace WeakTiling

/-- The real number represented by an integer coordinate vector in a positive independent family. -/
noncomputable def coordinateValueInt {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (v : ι → ℤ) : ℝ :=
  ∑ j, (v j : ℝ) * β j

theorem coordinateValueInt_nat {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (v : ι → ℕ) :
    coordinateValueInt β (fun j ↦ (v j : ℤ)) = ∑ j, (v j : ℝ) * β j := by
  simp [coordinateValueInt]

theorem coordinateValueInt_sub {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (u v : ι → ℤ) :
    coordinateValueInt β (u - v) = coordinateValueInt β u - coordinateValueInt β v := by
  classical
  unfold coordinateValueInt
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [Pi.sub_apply, Int.cast_sub, sub_mul]

/-- The positive integer coordinate vector of a semigroup point, using one representation. -/
noncomputable def coordVectorOfSemigroup {ι : Type*} [Fintype ι]
    (L : Finset ℝ) (_β : ι → ℝ) (g : L → ι → ℕ) (z : ℝ) : ι → ℕ := by
  classical
  exact if hz : InSemigroupL L z then
    fun j ↦ ∑ l : L, Classical.choose hz l * g l j
  else fun _ ↦ 0

/-- A semigroup representation gives the real value of its integer coordinate vector. -/
theorem coordVectorOfSemigroup_repr {ι : Type*} [Fintype ι]
    (L : Finset ℝ) (β : ι → ℝ) (g : L → ι → ℕ)
    (hgen : ∀ l : L, (l : ℝ) = ∑ j, (g l j : ℝ) * β j)
    {z : ℝ} (hz : InSemigroupL L z) :
    z = ∑ j, (coordVectorOfSemigroup L β g z j : ℝ) * β j := by
  classical
  let m : L → ℕ := Classical.choose hz
  have hm : z = ∑ l : L, (m l : ℝ) * (l : ℝ) := by
    simpa [m] using Classical.choose_spec hz
  have hcoord : ∀ j, (coordVectorOfSemigroup L β g z j : ℝ) =
      ∑ l : L, (m l : ℝ) * (g l j : ℝ) := by
    intro j
    simp [coordVectorOfSemigroup, dite_eq_left hz, m, Nat.cast_sum, Nat.cast_mul]
  calc
    z = ∑ l : L, (m l : ℝ) * (l : ℝ) := hm
    _ = ∑ j, (∑ l : L, (m l : ℝ) * (g l j : ℝ)) * β j := by
      calc
        _ = ∑ l : L, (m l : ℝ) * ∑ j, (g l j : ℝ) * β j := by
          refine sum_congr rfl fun l _ ↦ ?_
          rw [hgen l]
        _ = ∑ l : L, ∑ j, (m l : ℝ) * ((g l j : ℝ) * β j) := by
          simp_rw [mul_sum]
        _ = ∑ j, ∑ l : L, (m l : ℝ) * ((g l j : ℝ) * β j) := sum_comm
        _ = ∑ j, (∑ l : L, (m l : ℝ) * (g l j : ℝ)) * β j := by
          refine sum_congr rfl fun j _ ↦ ?_
          calc
            _ = ∑ l : L, ((m l : ℝ) * (g l j : ℝ)) * β j := by
              refine sum_congr rfl fun l _ ↦ ?_
              ring
            _ = _ := by rw [← sum_mul]
    _ = ∑ j, (coordVectorOfSemigroup L β g z j : ℝ) * β j := by
      refine sum_congr rfl fun j _ ↦ ?_
      rw [hcoord j]

/-- Rational linear independence makes the coordinate vector unique. -/
theorem coordVector_unique {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (hβ : LinearIndependent ℚ β) {p q : ι → ℕ}
    (hpq : (∑ j, (p j : ℝ) * β j) = ∑ j, (q j : ℝ) * β j) : p = q := by
  classical
  rw [Fintype.linearIndependent_iff] at hβ
  have hzero : ∑ j, ((p j : ℚ) - (q j : ℚ)) • β j = 0 := by
    simp only [Rat.smul_def]
    calc
      ∑ j, (((p j : ℚ) - (q j : ℚ) : ℚ) : ℝ) * β j =
          (∑ j, (p j : ℝ) * β j) - ∑ j, (q j : ℝ) * β j := by
        push_cast
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun j _ ↦ ?_
        ring
      _ = 0 := by rw [hpq]; ring
  have hcoeff : ∀ j, (p j : ℚ) - (q j : ℚ) = 0 := hβ _ hzero
  funext j
  exact_mod_cast (sub_eq_zero.mp (hcoeff j))

/-- Rationally independent coordinates are also unique for signed integer vectors. -/
theorem coordVectorInt_unique {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (hβ : LinearIndependent ℚ β) {u v : ι → ℤ}
    (huv : coordinateValueInt β u = coordinateValueInt β v) : u = v := by
  classical
  rw [Fintype.linearIndependent_iff] at hβ
  have hzero : ∑ j, ((u j - v j : ℤ) : ℚ) • β j = 0 := by
    simp only [Rat.smul_def]
    calc
      ∑ j, ((((u j - v j : ℤ) : ℚ) : ℝ) * β j) =
          coordinateValueInt β u - coordinateValueInt β v := by
        unfold coordinateValueInt
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        push_cast
        ring
      _ = 0 := sub_eq_zero.mpr huv
  have hcoeff : ∀ j, ((u j - v j : ℤ) : ℚ) = 0 := hβ _ hzero
  funext j
  have hdiff : u j - v j = 0 := by exact_mod_cast hcoeff j
  exact sub_eq_zero.mp hdiff

/-- Any representation of the same semigroup point yields the same integer coordinate vector. -/
theorem coordVectorOfSemigroup_eq_of_representation {ι : Type*} [Fintype ι]
    (L : Finset ℝ) (β : ι → ℝ) (g : L → ι → ℕ)
    (hβ : LinearIndependent ℚ β)
    (hgen : ∀ l : L, (l : ℝ) = ∑ j, (g l j : ℝ) * β j)
    {z : ℝ} (hz : InSemigroupL L z) (m : L → ℕ)
    (hm : z = ∑ l : L, (m l : ℝ) * (l : ℝ)) :
    coordVectorOfSemigroup L β g z = fun j ↦ ∑ l : L, m l * g l j := by
  classical
  let q : ι → ℕ := fun j ↦ ∑ l : L, m l * g l j
  apply coordVector_unique β hβ
  calc
    (∑ j, (coordVectorOfSemigroup L β g z j : ℝ) * β j) = z :=
      (coordVectorOfSemigroup_repr L β g hgen hz).symm
    _ = ∑ j, (q j : ℝ) * β j := by
      have hrepr : z = ∑ j, (∑ l : L, (m l : ℝ) * (g l j : ℝ)) * β j := by
        calc
          z = ∑ l : L, (m l : ℝ) * (l : ℝ) := hm
          _ = ∑ l : L, (m l : ℝ) * ∑ j, (g l j : ℝ) * β j := by
            refine sum_congr rfl fun l _ ↦ ?_
            rw [hgen l]
          _ = ∑ l : L, ∑ j, (m l : ℝ) * ((g l j : ℝ) * β j) := by
            simp_rw [mul_sum]
          _ = ∑ j, ∑ l : L, (m l : ℝ) * ((g l j : ℝ) * β j) := sum_comm
          _ = ∑ j, (∑ l : L, (m l : ℝ) * (g l j : ℝ)) * β j := by
            refine sum_congr rfl fun j _ ↦ ?_
            calc
              _ = ∑ l : L, ((m l : ℝ) * (g l j : ℝ)) * β j := by
                refine sum_congr rfl fun l _ ↦ ?_
                ring
              _ = _ := by rw [← sum_mul]
      simpa [q, Nat.cast_sum, Nat.cast_mul] using hrepr

/-- The canonical integer coordinates respect addition in the generated semigroup. -/
theorem coordVectorOfSemigroup_add {ι : Type*} [Fintype ι]
    (L : Finset ℝ) (β : ι → ℝ) (g : L → ι → ℕ)
    (hβ : LinearIndependent ℚ β)
    (hgen : ∀ l : L, (l : ℝ) = ∑ j, (g l j : ℝ) * β j)
    {x y : ℝ} (hx : InSemigroupL L x) (hy : InSemigroupL L y) :
    coordVectorOfSemigroup L β g (x + y) =
      coordVectorOfSemigroup L β g x + coordVectorOfSemigroup L β g y := by
  classical
  let mx : L → ℕ := Classical.choose hx
  let my : L → ℕ := Classical.choose hy
  have hxrep : x = ∑ l : L, (mx l : ℝ) * (l : ℝ) := by
    simpa [mx] using Classical.choose_spec hx
  have hyrep : y = ∑ l : L, (my l : ℝ) * (l : ℝ) := by
    simpa [my] using Classical.choose_spec hy
  have hxy : InSemigroupL L (x + y) := InSemigroupL.add hx hy
  have hxyrep : x + y = ∑ l : L, ((mx + my) l : ℝ) * (l : ℝ) := by
    calc
      x + y = (∑ l : L, (mx l : ℝ) * (l : ℝ)) +
          ∑ l : L, (my l : ℝ) * (l : ℝ) := by rw [hxrep, hyrep]
      _ = ∑ l : L, ((mx l : ℝ) + (my l : ℝ)) * (l : ℝ) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun l _ ↦ ?_
        ring
      _ = _ := by
        refine sum_congr rfl fun l _ ↦ ?_
        simp only [Pi.add_apply, Nat.cast_add]
  have hmx := coordVectorOfSemigroup_eq_of_representation L β g hβ hgen hx mx hxrep
  have hmy := coordVectorOfSemigroup_eq_of_representation L β g hβ hgen hy my hyrep
  have hms := coordVectorOfSemigroup_eq_of_representation L β g hβ hgen hxy (mx + my) hxyrep
  funext j
  rw [hms, hmx, hmy]
  simp [Pi.add_apply, Nat.add_mul, sum_add_distrib]

/-- A generator has exactly its chosen positive integer coordinate vector. -/
theorem coordVectorOfSemigroup_generator {ι : Type*} [Fintype ι]
    (L : Finset ℝ) (β : ι → ℝ) (g : L → ι → ℕ)
    (hβ : LinearIndependent ℚ β)
    (hgen : ∀ l : L, (l : ℝ) = ∑ j, (g l j : ℝ) * β j)
    (l : L) : coordVectorOfSemigroup L β g (l : ℝ) = g l := by
  classical
  let c : L → ℕ := Pi.single l 1
  have hlrep : (l : ℝ) = ∑ l' : L, (c l' : ℝ) * (l' : ℝ) := by
    simp [c, Pi.single_apply]
  have hlsem : InSemigroupL L (l : ℝ) := ⟨c, hlrep⟩
  have hcoords := coordVectorOfSemigroup_eq_of_representation
    L β g hβ hgen hlsem c hlrep
  simpa [c, Pi.single_apply] using hcoords

/-- Every nonnegative combination of nonnegative generators is nonnegative. -/
theorem inSemigroupL_nonneg {L : Finset ℝ} {z : ℝ}
    (hL : ∀ l ∈ L, 0 ≤ l) (hz : InSemigroupL L z) : 0 ≤ z := by
  rcases hz with ⟨c, rfl⟩
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (Nat.cast_nonneg _) (hL l l.2)

/-- The normalized covering measure `δ₀ + ν` obeys the exact endpoint atom-balance identity.
This is the discrete equation from which the positive and negative coordinate generating
functions must be extracted. -/
theorem weakTiling_normalized_atom_balance {n : ℕ} (A B : Fin n → ℝ)
    (hAB : ∀ i, A i < B i) (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν) (t : ℝ) :
    (∑ j, (Measure.dirac (0 : ℝ) + ν) {t - A j}) =
      ∑ j, (Measure.dirac (0 : ℝ) + ν) {t - B j} := by
  let ρ : Measure ℝ := Measure.dirac (0 : ℝ) + ν
  haveI : IsLocallyFiniteMeasure ν := hν.2.2.1
  haveI : IsLocallyFiniteMeasure ρ := by
    dsimp [ρ]
    exact isLocallyFiniteMeasure_dirac_add ν
  have hgood : ∀ᵐ x ∂(volume : Measure ℝ), ρ (reflTranslate (unionIoo A B) x) = 1 := by
    simpa [ρ] using weakTiling_normalized hν
  simpa [ρ] using atom_identity hAB hord ρ hgood t

/-- The endpoint atom balance over `ℝ≥0∞` becomes an ordinary real recurrence for singleton
masses, with the normalized atom at zero recorded explicitly. -/
theorem weakTiling_atom_balance_toReal {n : ℕ} (A B : Fin n → ℝ)
    (hAB : ∀ i, A i < B i) (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν) (t : ℝ) :
    (∑ j, ((ν {t - A j}).toReal + if t = A j then 1 else 0)) =
      ∑ j, ((ν {t - B j}).toReal + if t = B j then 1 else 0) := by
  haveI : IsLocallyFiniteMeasure ν := hν.2.2.1
  have hfinite : ∀ x : ℝ, ν {x} ≠ ∞ := fun x ↦ isCompact_singleton.measure_lt_top.ne
  have hdirac (x : ℝ) : Measure.dirac (0 : ℝ) {x} = if x = 0 then 1 else 0 := by
    by_cases hx : x = 0
    · subst x
      simp
    · rw [Measure.dirac_apply]
      simp [Pi.single_apply, hx, eq_comm]
  have hρfinite (x : ℝ) : (Measure.dirac (0 : ℝ) + ν) {x} ≠ ∞ := by
    rw [Measure.add_apply]
    exact ENNReal.add_ne_top.mpr ⟨by rw [hdirac]; split_ifs <;> simp, hfinite x⟩
  have hbal := congrArg ENNReal.toReal
    (weakTiling_normalized_atom_balance A B hAB hord hν t)
  rw [ENNReal.toReal_sum (fun j _ ↦ hρfinite (t - A j)),
      ENNReal.toReal_sum (fun j _ ↦ hρfinite (t - B j))] at hbal
  have hleft : ∀ j, ((Measure.dirac (0 : ℝ) + ν) {t - A j}).toReal =
      (ν {t - A j}).toReal + if t = A j then 1 else 0 := by
    intro j
    rw [Measure.add_apply, hdirac, ENNReal.toReal_add (by split_ifs <;> simp) (hfinite _)]
    by_cases hj : t = A j <;> simp [sub_eq_zero, hj, add_comm]
  have hright : ∀ j, ((Measure.dirac (0 : ℝ) + ν) {t - B j}).toReal =
      (ν {t - B j}).toReal + if t = B j then 1 else 0 := by
    intro j
    rw [Measure.add_apply, hdirac, ENNReal.toReal_add (by split_ifs <;> simp) (hfinite _)]
    by_cases hj : t = B j <;> simp [sub_eq_zero, hj, add_comm]
  simpa only [hleft, hright] using hbal

/-- Once the interval endpoints are expressed in a common integer coordinate system, the
normalized atom-balance law becomes a recurrence on the full coordinate lattice. The integer
vector `u` is unrestricted; the theorem itself does not yet use the support restriction to
discard the mixed-sign orthants. -/
theorem weakTiling_coordinate_atom_balance_of_endpointCoordinates {n : ℕ}
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (a₀ : ℝ)
    (p q : Fin n → ι → ℕ)
    (hp : ∀ j, coordinateValueInt β (fun k ↦ (p j k : ℤ)) = A j - a₀)
    (hq : ∀ j, coordinateValueInt β (fun k ↦ (q j k : ℤ)) = B j - a₀) :
    ∀ u : ι → ℤ,
      (∑ j, ((ν {coordinateValueInt β (u - fun k ↦ (p j k : ℤ))}).toReal +
        if a₀ + coordinateValueInt β u = A j then 1 else 0)) =
      ∑ j, ((ν {coordinateValueInt β (u - fun k ↦ (q j k : ℤ))}).toReal +
        if a₀ + coordinateValueInt β u = B j then 1 else 0) := by
  intro u
  have hleft (j : Fin n) :
      (a₀ + coordinateValueInt β u) - A j =
        coordinateValueInt β (u - fun k ↦ (p j k : ℤ)) := by
    calc
      (a₀ + coordinateValueInt β u) - A j =
          coordinateValueInt β u - (A j - a₀) := by ring
      _ = coordinateValueInt β u -
          coordinateValueInt β (fun k ↦ (p j k : ℤ)) := by rw [← hp j]
      _ = coordinateValueInt β (u - fun k ↦ (p j k : ℤ)) :=
        (coordinateValueInt_sub β u _).symm
  have hright (j : Fin n) :
      (a₀ + coordinateValueInt β u) - B j =
        coordinateValueInt β (u - fun k ↦ (q j k : ℤ)) := by
    calc
      (a₀ + coordinateValueInt β u) - B j =
          coordinateValueInt β u - (B j - a₀) := by ring
      _ = coordinateValueInt β u -
          coordinateValueInt β (fun k ↦ (q j k : ℤ)) := by rw [← hq j]
      _ = coordinateValueInt β (u - fun k ↦ (q j k : ℤ)) :=
        (coordinateValueInt_sub β u _).symm
  simpa only [hleft, hright] using
    (weakTiling_atom_balance_toReal A B hAB hord hν
      (a₀ + coordinateValueInt β u))

/-- The atom mass of the normalized measure `δ₀ + ν` at a coordinate-lattice point. -/
noncomputable def coordinateAtomMass {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (u : ι → ℤ) : ℝ :=
  (ν {coordinateValueInt β u}).toReal + if u = 0 then 1 else 0

/-- The normalized atom weights restricted to the nonnegative coordinate orthant. -/
noncomputable def coordinateAtomPositivePart {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (u : ι → ℤ) : ℝ :=
  if ∀ k, 0 ≤ u k then coordinateAtomMass β ν u else 0

/-- The normalized atom weights restricted to the strictly negative coordinate orthant. -/
noncomputable def coordinateAtomNegativePart {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (u : ι → ℤ) : ℝ :=
  if u ≠ 0 ∧ ∀ k, u k ≤ -1 then coordinateAtomMass β ν u else 0

/-- Sum a coefficient function over all endpoint shifts in a finite family. -/
noncomputable def endpointShiftSum {n : ℕ} {ι : Type*} [Fintype ι]
    (s : Fin n → ι → ℕ) (f : (ι → ℤ) → ℝ) (u : ι → ℤ) : ℝ :=
  ∑ j, f (u - fun k ↦ (s j k : ℤ))

/-- The endpoint operator `Σ_j T_{p_j} - Σ_j T_{q_j}` acting on coefficients. -/
noncomputable def endpointShiftDifference {n : ℕ} {ι : Type*} [Fintype ι]
    (p q : Fin n → ι → ℕ) (f : (ι → ℤ) → ℝ) (u : ι → ℤ) : ℝ :=
  endpointShiftSum p f u - endpointShiftSum q f u

/-- The coordinate box with lower corner zero and coordinatewise integer upper bounds. -/
def endpointCoordinateBox {ι : Type*} (B : ι → ℤ) : Set (ι → ℤ) :=
  {u | ∀ k, 0 ≤ u k ∧ u k < B k}

/-- A finite upper bound obtained by summing the right-endpoint shifts in each coordinate. -/
noncomputable def endpointShiftBoxBound {n : ℕ} {ι : Type*} [Fintype ι]
    (q : Fin n → ι → ℕ) : ι → ℤ :=
  fun k ↦ ((∑ j : Fin n, q j k : ℕ) : ℤ) + 1

theorem endpointCoordinateBox_finite {ι : Type*} [Fintype ι] (B : ι → ℤ) :
    (endpointCoordinateBox B).Finite := by
  classical
  have hcoord : ∀ k, (Set.Ico (0 : ℤ) (B k)).Finite := fun _ ↦ Set.finite_Ico _ _
  simpa [endpointCoordinateBox, Set.mem_Ico] using
    (Set.Finite.pi' (t := fun k ↦ Set.Ico (0 : ℤ) (B k)) hcoord)

/-- The endpoint recurrence is exactly a finite-shift convolution equation for the normalized
atom masses `δ₀ + ν`. Rational independence identifies endpoint equality with equality of their
integer coordinate vectors. -/
theorem weakTiling_coordinate_measure_balance_of_endpointCoordinates {n : ℕ}
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (hβind : LinearIndependent ℚ β)
    (a₀ : ℝ) (p q : Fin n → ι → ℕ)
    (hp : ∀ j, coordinateValueInt β (fun k ↦ (p j k : ℤ)) = A j - a₀)
    (hq : ∀ j, coordinateValueInt β (fun k ↦ (q j k : ℤ)) = B j - a₀) :
    ∀ u : ι → ℤ,
      (∑ j, coordinateAtomMass β ν (u - fun k ↦ (p j k : ℤ))) =
      ∑ j, coordinateAtomMass β ν (u - fun k ↦ (q j k : ℤ)) := by
  intro u
  have hpleft (j : Fin n) :
      a₀ + coordinateValueInt β u = A j ↔
        u = fun k ↦ (p j k : ℤ) := by
    constructor
    · intro ht
      apply coordVectorInt_unique β hβind
      rw [hp j]
      linarith
    · intro hu
      subst u
      rw [hp j]
      ring
  have hqright (j : Fin n) :
      a₀ + coordinateValueInt β u = B j ↔
        u = fun k ↦ (q j k : ℤ) := by
    constructor
    · intro ht
      apply coordVectorInt_unique β hβind
      rw [hq j]
      linarith
    · intro hu
      subst u
      rw [hq j]
      ring
  have hdeltaLeft (j : Fin n) :
      (if a₀ + coordinateValueInt β u = A j then (1 : ℝ) else 0) =
        (if u - (fun k ↦ (p j k : ℤ)) = 0 then 1 else 0) := by
    by_cases ht : a₀ + coordinateValueInt β u = A j
    · have hu := (hpleft j).mp ht
      have hdiff : u - (fun k ↦ (p j k : ℤ)) = 0 := sub_eq_zero.mpr hu
      simp [ht, hdiff]
    · have hdiff : u - (fun k ↦ (p j k : ℤ)) ≠ 0 := by
        intro h
        apply ht
        exact (hpleft j).mpr (sub_eq_zero.mp h)
      simp [ht, hdiff]
  have hdeltaRight (j : Fin n) :
      (if a₀ + coordinateValueInt β u = B j then (1 : ℝ) else 0) =
        (if u - (fun k ↦ (q j k : ℤ)) = 0 then 1 else 0) := by
    by_cases ht : a₀ + coordinateValueInt β u = B j
    · have hu := (hqright j).mp ht
      have hdiff : u - (fun k ↦ (q j k : ℤ)) = 0 := sub_eq_zero.mpr hu
      simp [ht, hdiff]
    · have hdiff : u - (fun k ↦ (q j k : ℤ)) ≠ 0 := by
        intro h
        apply ht
        exact (hqright j).mpr (sub_eq_zero.mp h)
      simp [ht, hdiff]
  have hraw := weakTiling_coordinate_atom_balance_of_endpointCoordinates
    A B hAB hord hν β a₀ p q hp hq u
  calc
    (∑ j, coordinateAtomMass β ν (u - fun k ↦ (p j k : ℤ))) =
        ∑ j, ((ν {coordinateValueInt β (u - fun k ↦ (p j k : ℤ))}).toReal +
          if a₀ + coordinateValueInt β u = A j then 1 else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [coordinateAtomMass, ← hdeltaLeft j]
    _ = ∑ j, ((ν {coordinateValueInt β (u - fun k ↦ (q j k : ℤ))}).toReal +
          if a₀ + coordinateValueInt β u = B j then 1 else 0) := hraw
    _ = ∑ j, coordinateAtomMass β ν (u - fun k ↦ (q j k : ℤ)) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [coordinateAtomMass, ← hdeltaRight j]

/-- Both endpoints of every component, measured from the first left endpoint, lie in the
nonnegative length semigroup. This produces the nonnegative exponents of the denominator. -/
theorem intervalEndpointOffsets_mem_semigroup {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν) :
    (∀ j, InSemigroupL (lengthSet A B) (A j - A ⟨0, hn⟩)) ∧
      (∀ j, InSemigroupL (lengthSet A B) (B j - A ⟨0, hn⟩)) := by
  classical
  obtain ⟨hwt, hpp⟩ := weakTiling_eq_purePoint hAB hord hν
  rw [hpp] at hν
  let lam : atomSet ν → ℝ := fun k ↦ (k : ℝ)
  letI : IsLocallyFiniteMeasure (purePoint lam fun k => (ν {↑k}).toReal) := hν.2.2.1
  have hT := transCover_ae hord hwt hν
  have hls := locSum2_of_locallyFinite (A := A) (lam := lam) hwt
  have hB := chain_semigroup (lam := lam) hAB hord hn hwt hls hT
  refine ⟨?_, hB⟩
  intro j
  suffices H : ∀ t : ℕ, ∀ ht : t < n,
      InSemigroupL (lengthSet A B) (A ⟨t, ht⟩ - A ⟨0, hn⟩) from H j.val j.isLt
  intro t ht
  induction t with
  | zero =>
    simpa using (InSemigroupL.zero (lengthSet A B))
  | succ t ih =>
    have ht' : t < n := by omega
    let m : Fin n := ⟨t, ht'⟩
    have hgap : InSemigroupL (lengthSet A B) (A ⟨t + 1, ht⟩ - B m) :=
      (gap_semigroup (lam := lam) hAB hord (m := m) (by simp [m]; omega) hwt hls hT).1
    have hsum := InSemigroupL.add (hB m) hgap
    have heq : A ⟨t + 1, ht⟩ - A ⟨0, hn⟩ =
        (B m - A ⟨0, hn⟩) + (A ⟨t + 1, ht⟩ - B m) := by
      simp only [m]
      ring
    rwa [heq]

/-- The right endpoint of every component is at least one positive coordinate step beyond its
left endpoint. These componentwise bounds make the overlap region in the finite-box argument
genuinely bounded. -/
theorem intervalEndpointCoordinates_strict {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (g : lengthSet A B → ι → ℕ)
    (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) :
    ∀ j k,
      coordVectorOfSemigroup (lengthSet A B) β g (B j - A ⟨0, hn⟩) k ≥
        coordVectorOfSemigroup (lengthSet A B) β g (A j - A ⟨0, hn⟩) k + 1 := by
  classical
  have hend := intervalEndpointOffsets_mem_semigroup hn A B hAB hord hν
  intro j k
  let ell : lengthSet A B := ⟨B j - A j, mem_image.mpr ⟨j, mem_univ j, rfl⟩⟩
  have hell : InSemigroupL (lengthSet A B) (B j - A j) := InSemigroupL.of_mem ell.2
  have hadd := coordVectorOfSemigroup_add (lengthSet A B) β g hβind hgen
    (hend.1 j) hell
  have hphys : B j - A ⟨0, hn⟩ =
      (A j - A ⟨0, hn⟩) + (B j - A j) := by ring
  have hgenvec := coordVectorOfSemigroup_generator (lengthSet A B) β g hβind hgen ell
  rw [hphys, congrFun hadd k, hgenvec]
  exact Nat.add_le_add_left (hcoordpos ell k) _

/-- Canonical integer coordinates of a left endpoint, relative to the first left endpoint. -/
noncomputable def leftEndpointCoordinateVector {n : ℕ} {ι : Type*} [Fintype ι]
    (A B : Fin n → ℝ) (hn : 0 < n) (β : ι → ℝ)
    (g : lengthSet A B → ι → ℕ) (j : Fin n) : ι → ℕ :=
  coordVectorOfSemigroup (lengthSet A B) β g (A j - A ⟨0, hn⟩)

/-- Canonical integer coordinates of a right endpoint, relative to the first left endpoint. -/
noncomputable def rightEndpointCoordinateVector {n : ℕ} {ι : Type*} [Fintype ι]
    (A B : Fin n → ℝ) (hn : 0 < n) (β : ι → ℝ)
    (g : lengthSet A B → ι → ℕ) (j : Fin n) : ι → ℕ :=
  coordVectorOfSemigroup (lengthSet A B) β g (B j - A ⟨0, hn⟩)

/-- For the actual positive coordinates of the interval-length semigroup, the endpoint balance
is a finite-shift recurrence for the normalized atom masses on the integer coordinate lattice. -/
theorem weakTiling_lengthCoordinate_measure_balance {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (g : lengthSet A B → ι → ℕ)
    (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k) :
    ∀ u : ι → ℤ,
      (∑ j, coordinateAtomMass β ν
        (u - fun k ↦ (leftEndpointCoordinateVector A B hn β g j k : ℤ))) =
      ∑ j, coordinateAtomMass β ν
        (u - fun k ↦ (rightEndpointCoordinateVector A B hn β g j k : ℤ)) := by
  classical
  intro u
  let a₀ : ℝ := A ⟨0, hn⟩
  let p : Fin n → ι → ℕ := leftEndpointCoordinateVector A B hn β g
  let q : Fin n → ι → ℕ := rightEndpointCoordinateVector A B hn β g
  have hend := intervalEndpointOffsets_mem_semigroup hn A B hAB hord hν
  have hp : ∀ j, coordinateValueInt β (fun k ↦ (p j k : ℤ)) = A j - a₀ := by
    intro j
    rw [coordinateValueInt_nat]
    exact (coordVectorOfSemigroup_repr (lengthSet A B) β g hgen (hend.1 j)).symm
  have hq : ∀ j, coordinateValueInt β (fun k ↦ (q j k : ℤ)) = B j - a₀ := by
    intro j
    rw [coordinateValueInt_nat]
    exact (coordVectorOfSemigroup_repr (lengthSet A B) β g hgen (hend.2 j)).symm
  simpa only [leftEndpointCoordinateVector, rightEndpointCoordinateVector, p, q, a₀] using
    (weakTiling_coordinate_measure_balance_of_endpointCoordinates
      A B hAB hord hν β hβind a₀ p q hp hq u)

/-- The nonnegative part of the actual weak-tiling support belongs to the positive length
semigroup, using the established support theorem. -/
theorem weakTiling_nonnegative_support_mem_semigroup {n : ℕ} {A B : Fin n → ℝ}
    (hAB : ∀ i, A i < B i) (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {z : ℝ} (hz : z ∈ ν.support) (hz0 : 0 ≤ z) :
    InSemigroupL (lengthSet A B) z := by
  rcases weakTiling_support_subset hAB hord hν hz with hzpos | hzneg
  · exact hzpos
  · have hneg0 : 0 ≤ -z := inSemigroupL_nonneg
      (fun l hl ↦ (lengthSet_pos hAB hl).le) hzneg
    have hzEq : z = 0 := by linarith
    rw [hzEq]
    exact InSemigroupL.zero _

/-- Reflecting a negative support point gives an element of the positive length semigroup. -/
theorem weakTiling_negative_support_reflection_mem_semigroup {n : ℕ} {A B : Fin n → ℝ}
    (hAB : ∀ i, A i < B i) (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {z : ℝ} (hz : z ∈ ν.support) (hzneg : z < 0) :
    InSemigroupL (lengthSet A B) (-z) := by
  rcases weakTiling_support_subset hAB hord hν hz with hzpos | hzneg'
  · have hz0 : 0 ≤ z := inSemigroupL_nonneg
      (fun l hl ↦ (lengthSet_pos hAB hl).le) hzpos
    linarith
  · exact hzneg'

/-- A support point on the signed integer coordinate lattice can only lie in the positive or
negative coordinate orthant. This is the support restriction needed before comparing the two
finite-box generating functions. -/
theorem weakTiling_coordinate_support_orthants {n : ℕ} {A B : Fin n → ℝ}
    (hAB : ∀ i, A i < B i) (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (g : lengthSet A B → ι → ℕ)
    (hβ : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    {v : ι → ℤ} (hv : coordinateValueInt β v ∈ ν.support) :
    (∀ k, 0 ≤ v k) ∨ (∀ k, v k ≤ 0) := by
  classical
  let L := lengthSet A B
  rcases weakTiling_support_subset hAB hord hν hv with hpos | hneg
  · have hcanon : coordinateValueInt β
        (fun k ↦ (coordVectorOfSemigroup L β g (coordinateValueInt β v) k : ℤ)) =
        coordinateValueInt β v := by
      rw [coordinateValueInt_nat]
      exact (coordVectorOfSemigroup_repr L β g hgen hpos).symm
    have hvec := coordVectorInt_unique β hβ hcanon.symm
    left
    intro k
    rw [hvec]
    exact Int.natCast_nonneg _
  · have hminus : coordinateValueInt β (fun k ↦ -v k) =
        -coordinateValueInt β v := by
      simp [coordinateValueInt]
    have hcanon : coordinateValueInt β
        (fun k ↦ (coordVectorOfSemigroup L β g (-coordinateValueInt β v) k : ℤ)) =
        -coordinateValueInt β v := by
      rw [coordinateValueInt_nat]
      exact (coordVectorOfSemigroup_repr L β g hgen hneg).symm
    have hvec := coordVectorInt_unique β hβ (hminus.trans hcanon.symm)
    right
    intro k
    have hk : 0 ≤ -v k := by
      rw [congrFun hvec k]
      exact Int.natCast_nonneg _
    omega

/-- A nonzero semigroup point has strictly positive canonical coordinates when every generator
has strictly positive coordinates. -/
theorem coordVectorOfSemigroup_pos_of_ne_zero {ι : Type*} [Fintype ι]
    (L : Finset ℝ) (β : ι → ℝ) (g : L → ι → ℕ)
    (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : L, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : L, ∀ k, 1 ≤ g l k)
    {z : ℝ} (hz : InSemigroupL L z) (hz0 : z ≠ 0) :
    ∀ k, 1 ≤ coordVectorOfSemigroup L β g z k := by
  classical
  let m : L → ℕ := Classical.choose hz
  have hm : z = ∑ l : L, (m l : ℝ) * (l : ℝ) := by
    simpa [m] using Classical.choose_spec hz
  have hmsupp : ∃ l : L, m l ≠ 0 := by
    by_contra h
    have hmzero : m = 0 := funext fun l ↦ not_not.mp (not_exists.mp h l)
    apply hz0
    rw [hm]
    simp [hmzero]
  obtain ⟨l, hl⟩ := hmsupp
  have hcoords := coordVectorOfSemigroup_eq_of_representation
    L β g hβind hgen hz m hm
  intro k
  have hmpos : 1 ≤ m l := Nat.one_le_iff_ne_zero.mpr hl
  have hprod : 1 ≤ m l * g l k := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ m l * g l k := Nat.mul_le_mul hmpos (hcoordpos l k)
  have hsum : m l * g l k ≤ ∑ l' : L, m l' * g l' k :=
    Finset.single_le_sum (f := fun l' : L ↦ m l' * g l' k)
      (fun l' _ ↦ Nat.zero_le _) (Finset.mem_univ l)
  calc
    1 ≤ m l * g l k := hprod
    _ ≤ ∑ l' : L, m l' * g l' k := hsum
    _ = coordVectorOfSemigroup L β g z k := by rw [← congrFun hcoords k]

/-- The signed support is separated from the coordinate hyperplanes: positive support points have
all coordinates at least one, and negative support points have all coordinates at most minus one.
This strict form makes the overlap of the two endpoint convolutions a finite box. -/
theorem weakTiling_coordinate_support_strict_orthants {n : ℕ} (hn : 0 < n)
    {A B : Fin n → ℝ} (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (g : lengthSet A B → ι → ℕ)
    (hβpos : ∀ k, 0 < β k) (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k)
    {v : ι → ℤ} (hv : coordinateValueInt β v ∈ ν.support) :
    (∀ k, 1 ≤ v k) ∨ (∀ k, v k ≤ -1) := by
  classical
  let Ω := unionIoo A B
  have hopen : IsOpen Ω := isOpen_iUnion fun i ↦ isOpen_Ioo
  let i₀ : Fin n := ⟨0, hn⟩
  have hΩne : Ω.Nonempty := by
    refine ⟨(A i₀ + B i₀) / 2, Set.mem_iUnion.mpr ⟨i₀, ?_⟩⟩
    rw [Set.mem_Ioo]
    constructor <;> linarith [hAB i₀]
  have hzero : (0 : ℝ) ∉ ν.support := zero_notMem_support hν hopen hΩne
  have hx0 : coordinateValueInt β v ≠ 0 := by
    intro hx
    apply hzero
    simpa [hx] using hv
  rcases weakTiling_coordinate_support_orthants hAB hord hν β g hβind hgen hv with
    hvpos | hvneg
  · have hxnonneg : 0 ≤ coordinateValueInt β v := by
      unfold coordinateValueInt
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (by exact_mod_cast hvpos k) (hβpos k).le
    have hsem : InSemigroupL (lengthSet A B) (coordinateValueInt β v) :=
      weakTiling_nonnegative_support_mem_semigroup hAB hord hν hv hxnonneg
    have hcoords := coordVectorOfSemigroup_pos_of_ne_zero
      (lengthSet A B) β g
      hβind
      hgen hcoordpos hsem hx0
    have hcanon : coordinateValueInt β
        (fun k ↦ (coordVectorOfSemigroup (lengthSet A B) β g
          (coordinateValueInt β v) k : ℤ)) = coordinateValueInt β v := by
      rw [coordinateValueInt_nat]
      exact (coordVectorOfSemigroup_repr (lengthSet A B) β g hgen hsem).symm
    have hvec := coordVectorInt_unique β
      hβind hcanon.symm
    left
    intro k
    have hk := hcoords k
    have hvec_k : v k =
        (coordVectorOfSemigroup (lengthSet A B) β g
          (coordinateValueInt β v) k : ℤ) := by
      simpa using congrFun hvec k
    have hk_cast : (1 : ℤ) ≤
        (coordVectorOfSemigroup (lengthSet A B) β g
          (coordinateValueInt β v) k : ℤ) := by exact_mod_cast hk
    rw [hvec_k]
    exact hk_cast
  · have hsumneg : coordinateValueInt β v < 0 := by
      unfold coordinateValueInt
      obtain ⟨k, hvk⟩ : ∃ k, v k ≠ 0 := by
        by_contra h
        have hvzero : v = 0 := funext fun k ↦ not_not.mp (not_exists.mp h k)
        apply hx0
        simp [coordinateValueInt, hvzero]
      have hvknonpos := hvneg k
      have hvkneg : v k < 0 := by omega
      have hle : ∀ k ∈ Finset.univ, (v k : ℝ) * β k ≤ 0 := by
        intro k _
        exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hvneg k) (hβpos k).le
      have hlt : (v k : ℝ) * β k < 0 :=
        mul_neg_of_neg_of_pos (by exact_mod_cast hvkneg) (hβpos k)
      have hsumlt := Finset.sum_lt_sum hle ⟨k, Finset.mem_univ _, hlt⟩
      simpa using hsumlt
    have hsem : InSemigroupL (lengthSet A B) (-coordinateValueInt β v) :=
      weakTiling_negative_support_reflection_mem_semigroup hAB hord hν hv hsumneg
    have hcoords := coordVectorOfSemigroup_pos_of_ne_zero
      (lengthSet A B) β g
      hβind
      hgen hcoordpos hsem (neg_ne_zero.mpr hx0)
    have hminus : coordinateValueInt β (fun k ↦ -v k) =
        -coordinateValueInt β v := by simp [coordinateValueInt]
    have hcanon : coordinateValueInt β
        (fun k ↦ (coordVectorOfSemigroup (lengthSet A B) β g
          (-coordinateValueInt β v) k : ℤ)) = -coordinateValueInt β v := by
      rw [coordinateValueInt_nat]
      exact (coordVectorOfSemigroup_repr (lengthSet A B) β g hgen hsem).symm
    have hvec := coordVectorInt_unique β
      hβind (hminus.trans hcanon.symm)
    right
    intro k
    have hk := hcoords k
    have hcast : (1 : ℤ) ≤
        (coordVectorOfSemigroup (lengthSet A B) β g
          (-coordinateValueInt β v) k : ℤ) := by exact_mod_cast hk
    have hvec_k : -v k =
        (coordVectorOfSemigroup (lengthSet A B) β g
          (-coordinateValueInt β v) k : ℤ) := by
      simpa using congrFun hvec k
    omega

/-- A positive finite singleton mass forces its point into the measure support. -/
theorem mem_support_of_singleton_toReal_pos (ν : Measure ℝ) (x : ℝ)
    (hx : 0 < (ν {x}).toReal) : x ∈ ν.support := by
  have hxμ : 0 < ν {x} := (ENNReal.toReal_pos_iff.mp hx).1
  rw [Measure.mem_support_iff_forall]
  intro U hU
  exact lt_of_lt_of_le hxμ
    (measure_mono (Set.singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

/-- The normalized coordinate atom sequence is exactly the sum of its positive and negative
orthant pieces. The zero atom belongs to the positive piece because it comes from `δ₀`; all
nonzero atoms lie strictly inside one of the two orthants. -/
theorem coordinateAtomMass_eq_positive_add_negative {n : ℕ} (hn : 0 < n)
    {A B : Fin n → ℝ} (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (g : lengthSet A B → ι → ℕ)
    (hβpos : ∀ k, 0 < β k) (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) (u : ι → ℤ) :
    coordinateAtomMass β ν u = coordinateAtomPositivePart β ν u +
      coordinateAtomNegativePart β ν u := by
  classical
  let Ω := unionIoo A B
  have hopen : IsOpen Ω := isOpen_iUnion fun i ↦ isOpen_Ioo
  let i₀ : Fin n := ⟨0, hn⟩
  have hΩne : Ω.Nonempty := by
    refine ⟨(A i₀ + B i₀) / 2, Set.mem_iUnion.mpr ⟨i₀, ?_⟩⟩
    rw [Set.mem_Ioo]
    constructor <;> linarith [hAB i₀]
  have hzero : (0 : ℝ) ∉ ν.support := zero_notMem_support hν hopen hΩne
  have hzeroAtom : ν {(0 : ℝ)} = 0 := by
    rcases (Measure.notMem_support_iff_exists.mp hzero) with ⟨U, hU, hU0⟩
    exact measure_mono_null
      (Set.singleton_subset_iff.mpr (mem_of_mem_nhds hU)) hU0
  by_cases hu : u = 0
  · subst u
    simp [coordinateAtomMass, coordinateAtomPositivePart, coordinateAtomNegativePart,
      coordinateValueInt, hzeroAtom]
  · let x := coordinateValueInt β u
    by_cases hmasspos : 0 < (ν {x}).toReal
    · have hmem : x ∈ ν.support := mem_support_of_singleton_toReal_pos ν x hmasspos
      have hstrict := weakTiling_coordinate_support_strict_orthants
        hn hAB hord hν β g hβpos hβind hgen hcoordpos (by simpa [x] using hmem)
      have hu_ne : ∃ k, u k ≠ 0 := by
        by_contra h
        have : u = 0 := funext fun k ↦ not_not.mp (not_exists.mp h k)
        exact hu this
      rcases hstrict with hpos | hneg
      · have hnotneg : ¬ ∀ k, u k ≤ -1 := by
          obtain ⟨k, hk⟩ := hu_ne
          intro hall
          have hlow := hpos k
          have hup := hall k
          omega
        have hpos' : ∀ k, 0 ≤ u k := fun k ↦ le_trans (by omega) (hpos k)
        have hmass : coordinateAtomMass β ν u = (ν {x}).toReal := by
          simp [coordinateAtomMass, hu, x]
        have hnegCond : ¬ (u ≠ 0 ∧ ∀ k, u k ≤ -1) := by
          rintro ⟨_, hall⟩
          exact hnotneg hall
        simp only [coordinateAtomPositivePart, ite_eq_left hpos', coordinateAtomNegativePart,
          ite_eq_right hnegCond]
        rw [hmass]
        simp
      · have hnotpos : ¬ ∀ k, 0 ≤ u k := by
          obtain ⟨k, hk⟩ := hu_ne
          intro hall
          have hlow := hneg k
          have hup := hall k
          omega
        have hneg' : u ≠ 0 ∧ ∀ k, u k ≤ -1 := ⟨hu, hneg⟩
        simp only [coordinateAtomPositivePart, ite_eq_right hnotpos, coordinateAtomNegativePart,
          ite_eq_left hneg']
        simp
    · have hmasszero : (ν {x}).toReal = 0 :=
        le_antisymm (le_of_not_gt hmasspos) ENNReal.toReal_nonneg
      have hzeroMass : coordinateAtomMass β ν u = 0 := by
        simp [coordinateAtomMass, hu, x, hmasszero]
      simp [coordinateAtomPositivePart, coordinateAtomNegativePart, hzeroMass]

/-- If a coefficient sequence satisfies the endpoint recurrence and splits into two pieces,
their endpoint discrepancies cancel pointwise. -/
theorem endpointShiftDifference_parts_of_balance {n : ℕ} {ι : Type*} [Fintype ι]
    (p q : Fin n → ι → ℕ) (M f g : (ι → ℤ) → ℝ)
    (hbal : ∀ u, endpointShiftSum p M u = endpointShiftSum q M u)
    (hsplit : ∀ u, M u = f u + g u) :
    ∀ u, endpointShiftDifference p q f u = -endpointShiftDifference p q g u := by
  intro u
  have hp : endpointShiftSum p M u = endpointShiftSum p f u + endpointShiftSum p g u := by
    unfold endpointShiftSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hsplit (u - fun k ↦ (p j k : ℤ))
  have hq : endpointShiftSum q M u = endpointShiftSum q f u + endpointShiftSum q g u := by
    unfold endpointShiftSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hsplit (u - fun k ↦ (q j k : ℤ))
  have htotal := hbal u
  rw [hp, hq] at htotal
  unfold endpointShiftDifference
  linarith

/-- For the endpoint coordinates of an actual weak tiling, the positive and negative atom
generating coefficients have opposite endpoint discrepancies. This is the finite-shift form of
`P F₊ = -P F₋`, before packaging the coefficients as power series. -/
theorem weakTiling_lengthCoordinate_positive_negative_balance {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (g : lengthSet A B → ι → ℕ)
    (hβpos : ∀ k, 0 < β k) (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) :
    ∀ u,
      endpointShiftDifference (leftEndpointCoordinateVector A B hn β g)
        (rightEndpointCoordinateVector A B hn β g)
        (coordinateAtomPositivePart β ν) u =
      -endpointShiftDifference (leftEndpointCoordinateVector A B hn β g)
        (rightEndpointCoordinateVector A B hn β g)
        (coordinateAtomNegativePart β ν) u := by
  let p : Fin n → ι → ℕ := leftEndpointCoordinateVector A B hn β g
  let q : Fin n → ι → ℕ := rightEndpointCoordinateVector A B hn β g
  have hbal : ∀ u,
      endpointShiftSum p (coordinateAtomMass β ν) u =
        endpointShiftSum q (coordinateAtomMass β ν) u := by
    intro u
    simpa [endpointShiftSum, p, q] using
      (weakTiling_lengthCoordinate_measure_balance hn A B hAB hord hν β g
        hβind hgen u)
  have hsplit : ∀ u, coordinateAtomMass β ν u =
      coordinateAtomPositivePart β ν u + coordinateAtomNegativePart β ν u := by
    intro u
    exact coordinateAtomMass_eq_positive_add_negative hn hAB hord hν β g
      hβpos hβind hgen hcoordpos u
  simpa [p, q] using
    (endpointShiftDifference_parts_of_balance p q (coordinateAtomMass β ν)
      (coordinateAtomPositivePart β ν) (coordinateAtomNegativePart β ν) hbal hsplit)

theorem endpointShiftDifference_eq_zero_outside_box {n : ℕ} {ι : Type*} [Fintype ι]
    (p q : Fin n → ι → ℕ) (f g : (ι → ℤ) → ℝ) (B : ι → ℤ)
    (hbal : ∀ u, endpointShiftDifference p q f u =
      -endpointShiftDifference p q g u)
    (hf : ∀ v k, v k < 0 → f v = 0)
    (hg : ∀ v k, 0 ≤ v k → g v = 0)
    (hpB : ∀ j k, (p j k : ℤ) < B k)
    (hqB : ∀ j k, (q j k : ℤ) < B k) :
    ∀ u, (∃ k, u k < 0) ∨ (∃ k, B k ≤ u k) →
      endpointShiftDifference p q f u = 0 := by
  intro u hout
  rcases hout with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hpf : ∀ j, f (u - fun k' ↦ (p j k' : ℤ)) = 0 := by
      intro j
      apply hf _ k
      change u k - (p j k : ℤ) < 0
      have hnonneg : 0 ≤ (p j k : ℤ) := Int.natCast_nonneg _
      omega
    have hqf : ∀ j, f (u - fun k' ↦ (q j k' : ℤ)) = 0 := by
      intro j
      apply hf _ k
      change u k - (q j k : ℤ) < 0
      have hnonneg : 0 ≤ (q j k : ℤ) := Int.natCast_nonneg _
      omega
    simp [endpointShiftDifference, endpointShiftSum, hpf, hqf]
  · have hpg : ∀ j, g (u - fun k' ↦ (p j k' : ℤ)) = 0 := by
      intro j
      apply hg _ k
      change 0 ≤ u k - (p j k : ℤ)
      have hshift := hpB j k
      omega
    have hqg : ∀ j, g (u - fun k' ↦ (q j k' : ℤ)) = 0 := by
      intro j
      apply hg _ k
      change 0 ≤ u k - (q j k : ℤ)
      have hshift := hqB j k
      omega
    have hgzeroP : endpointShiftSum p g u = 0 := by
      simp [endpointShiftSum, hpg]
    have hgzeroQ : endpointShiftSum q g u = 0 := by
      simp [endpointShiftSum, hqg]
    have hzero : endpointShiftDifference p q g u = 0 := by
      simp [endpointShiftDifference, hgzeroP, hgzeroQ]
    simpa [hzero] using hbal u

theorem weakTiling_endpointDifference_vanishes_outside_box {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (g : lengthSet A B → ι → ℕ)
    (hβpos : ∀ k, 0 < β k) (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) :
    ∀ u, u ∉ endpointCoordinateBox
        (endpointShiftBoxBound (rightEndpointCoordinateVector A B hn β g)) →
      endpointShiftDifference (leftEndpointCoordinateVector A B hn β g)
        (rightEndpointCoordinateVector A B hn β g)
        (coordinateAtomPositivePart β ν) u = 0 := by
  classical
  let p : Fin n → ι → ℕ := leftEndpointCoordinateVector A B hn β g
  let q : Fin n → ι → ℕ := rightEndpointCoordinateVector A B hn β g
  let C : ι → ℤ := endpointShiftBoxBound q
  have hstrict := intervalEndpointCoordinates_strict hn A B hAB hord hν β g
    hβind hgen hcoordpos
  have hqsum (j : Fin n) (k : ι) : q j k ≤ ∑ j' : Fin n, q j' k := by
    exact Finset.single_le_sum (f := fun j' : Fin n ↦ q j' k)
      (fun j' _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have hpBound : ∀ j k, (p j k : ℤ) < C k := by
    intro j k
    have hs : q j k ≥ p j k + 1 := by
      simpa [p, q, leftEndpointCoordinateVector, rightEndpointCoordinateVector] using
        hstrict j k
    have hnat : p j k < (∑ j' : Fin n, q j' k) + 1 := by
      have hsum := hqsum j k
      omega
    dsimp [C, endpointShiftBoxBound]
    exact_mod_cast hnat
  have hqBound : ∀ j k, (q j k : ℤ) < C k := by
    intro j k
    have hnat : q j k < (∑ j' : Fin n, q j' k) + 1 := by
      have hsum := hqsum j k
      omega
    dsimp [C, endpointShiftBoxBound]
    exact_mod_cast hnat
  have hf : ∀ v k, v k < 0 → coordinateAtomPositivePart β ν v = 0 := by
    intro v k hk
    have hnot : ¬∀ k', 0 ≤ v k' := by
      intro hall
      have := hall k
      omega
    simp [coordinateAtomPositivePart, hnot]
  have hg : ∀ v k, 0 ≤ v k → coordinateAtomNegativePart β ν v = 0 := by
    intro v k hk
    have hnot : ¬(v ≠ 0 ∧ ∀ k', v k' ≤ -1) := by
      rintro ⟨_, hall⟩
      have := hall k
      omega
    simp [coordinateAtomNegativePart, hnot]
  have hbal : ∀ u, endpointShiftDifference p q (coordinateAtomPositivePart β ν) u =
      -endpointShiftDifference p q (coordinateAtomNegativePart β ν) u := by
    intro u
    simpa [p, q] using
      (weakTiling_lengthCoordinate_positive_negative_balance hn A B hAB hord hν
        β g hβpos hβind hgen hcoordpos u)
  have hvanish := endpointShiftDifference_eq_zero_outside_box
    p q (coordinateAtomPositivePart β ν) (coordinateAtomNegativePart β ν) C
    hbal hf hg hpBound hqBound
  intro u huBox
  have hout : (∃ k, u k < 0) ∨ (∃ k, C k ≤ u k) := by
    by_contra hnot
    apply huBox
    change ∀ k, 0 ≤ u k ∧ u k < C k
    intro k
    constructor
    · by_contra hk
      apply hnot
      exact Or.inl ⟨k, by omega⟩
    · by_contra hk
      apply hnot
      exact Or.inr ⟨k, by omega⟩
  exact hvanish u hout

theorem weakTiling_endpointDifference_has_finite_support {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (g : lengthSet A B → ι → ℕ)
    (hβpos : ∀ k, 0 < β k) (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) :
    (Function.support (fun u ↦ endpointShiftDifference
      (leftEndpointCoordinateVector A B hn β g)
      (rightEndpointCoordinateVector A B hn β g)
      (coordinateAtomPositivePart β ν) u)).Finite := by
  classical
  let C := endpointShiftBoxBound (rightEndpointCoordinateVector A B hn β g)
  have hfinite : (endpointCoordinateBox C).Finite := endpointCoordinateBox_finite C
  have hvanish := weakTiling_endpointDifference_vanishes_outside_box
    hn A B hAB hord hν β g hβpos hβind hgen hcoordpos
  have hsub : Function.support (fun u ↦ endpointShiftDifference
      (leftEndpointCoordinateVector A B hn β g)
      (rightEndpointCoordinateVector A B hn β g)
      (coordinateAtomPositivePart β ν) u) ⊆ endpointCoordinateBox C := by
    intro u hu
    by_contra hnot
    exact hu (by simpa [C] using hvanish u hnot)
  exact hfinite.subset hsub

/-- Package the actual finite overlap sequence as a finitely supported integer-lattice
coefficient function. Its coefficients are still defined directly from the weak-tiling measure. -/
noncomputable def weakTiling_endpointOverlapFinsupp {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (g : lengthSet A B → ι → ℕ)
    (hβpos : ∀ k, 0 < β k) (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) :
    (ι → ℤ) →₀ ℝ := by
  classical
  exact Finsupp.ofSupportFinite
    (fun u ↦ endpointShiftDifference
      (leftEndpointCoordinateVector A B hn β g)
      (rightEndpointCoordinateVector A B hn β g)
      (coordinateAtomPositivePart β ν) u)
    (weakTiling_endpointDifference_has_finite_support hn A B hAB hord hν
      β g hβpos hβind hgen hcoordpos)

@[simp]
theorem weakTiling_endpointOverlapFinsupp_apply {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (g : lengthSet A B → ι → ℕ)
    (hβpos : ∀ k, 0 < β k) (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) (u : ι → ℤ) :
    weakTiling_endpointOverlapFinsupp hn A B hAB hord hν β g hβpos hβind hgen hcoordpos u =
      endpointShiftDifference (leftEndpointCoordinateVector A B hn β g)
        (rightEndpointCoordinateVector A B hn β g)
        (coordinateAtomPositivePart β ν) u := rfl

end WeakTiling

end

end CoordinateRows

/-! ## Linear recurrences are polynomial-exponential sums -/

section PolyExp

section

open Polynomial Finset

namespace WeakTiling

/-- Polynomial-exponential sequences `n ↦ ∑_{μ ∈ S} p_μ(n) μⁿ` with frequencies in `S`. -/
def IsPolyExp (S : Finset ℂ) (a : ℕ → ℂ) : Prop :=
  ∃ p : ℂ → ℂ[X], ∀ n, a n = ∑ μ ∈ S, (p μ).eval (n : ℂ) * μ ^ n

theorem IsPolyExp.zero (S : Finset ℂ) : IsPolyExp S 0 :=
  ⟨fun _ ↦ 0, fun n ↦ by simp⟩

theorem IsPolyExp.add {S : Finset ℂ} {a b : ℕ → ℂ} (ha : IsPolyExp S a) (hb : IsPolyExp S b) :
    IsPolyExp S (a + b) := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  refine ⟨fun μ ↦ p μ + q μ, fun n ↦ ?_⟩
  simp only [Pi.add_apply, hp, hq, eval_add, add_mul, sum_add_distrib]

theorem IsPolyExp.mono {S T : Finset ℂ} {a : ℕ → ℂ} (hST : S ⊆ T) (ha : IsPolyExp S a) :
    IsPolyExp T a := by
  classical
  obtain ⟨p, hp⟩ := ha
  refine ⟨fun μ ↦ if μ ∈ S then p μ else 0, fun n ↦ ?_⟩
  rw [hp, ← sum_subset hST (fun μ _ hμ ↦ by simp [hμ])]
  exact sum_congr rfl fun μ hμ ↦ by simp [hμ]

theorem IsPolyExp.single (q : ℂ[X]) (μ : ℂ) :
    IsPolyExp {μ} (fun n ↦ q.eval (n : ℂ) * μ ^ n) :=
  ⟨fun _ ↦ q, fun n ↦ by simp⟩

theorem coeff_X_add_one_pow (m N : ℕ) : ((X + 1 : ℂ[X]) ^ m).coeff N = (m.choose N : ℂ) := by
  have : (X + 1 : ℂ[X]) = X + C 1 := by simp
  rw [this, coeff_X_add_C_pow, one_pow, one_mul]

/-- For `α ≠ β`, the operator `r ↦ α r(X+1) - β r(X)` is surjective on `ℂ[X]`. -/
theorem exists_shift_solution_of_ne {α β : ℂ} (hαβ : α ≠ β) (q : ℂ[X]) :
    ∃ p : ℂ[X], C α * p.comp (X + 1) - C β * p = q := by
  have hsub : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  suffices H : ∀ d (q : ℂ[X]), (∀ N, d ≤ N → q.coeff N = 0) →
      ∃ p : ℂ[X], C α * p.comp (X + 1) - C β * p = q by
    refine H (q.natDegree + 1) q fun N hN ↦ coeff_eq_zero_of_natDegree_lt (by omega)
  intro d
  induction d with
  | zero =>
    intro q hq
    refine ⟨0, ?_⟩
    ext N
    simp [hq N (Nat.zero_le N)]
  | succ d ih =>
    intro q hq
    set c := q.coeff d with hc
    set p₀ : ℂ[X] := C (c / (α - β)) * X ^ d with hp₀
    set r := q - (C α * p₀.comp (X + 1) - C β * p₀) with hr
    have hrc : ∀ N, d ≤ N → r.coeff N = 0 := by
      intro N hN
      simp only [hr, hp₀, coeff_sub, mul_comp, C_comp, X_pow_comp, coeff_C_mul, coeff_X_pow,
        coeff_X_add_one_pow]
      rcases hN.lt_or_eq with hlt | rfl
      · rw [hq N hlt, Nat.choose_eq_zero_of_lt hlt, ite_eq_right (Nat.ne_of_gt hlt)]
        simp
      · rw [Nat.choose_self, ite_eq_left rfl, ← hc]
        field_simp
        ring
    obtain ⟨p₁, hp₁⟩ := ih r hrc
    refine ⟨p₀ + p₁, ?_⟩
    rw [add_comp]
    have : r = q - (C α * p₀.comp (X + 1) - C β * p₀) := hr
    rw [← hp₁] at this
    linear_combination this

/-- For `α ≠ 0`, the operator `r ↦ α (r(X+1) - r(X))` is surjective on `ℂ[X]`. -/
theorem exists_shift_solution_of_eq {α : ℂ} (hα : α ≠ 0) (q : ℂ[X]) :
    ∃ p : ℂ[X], C α * p.comp (X + 1) - C α * p = q := by
  suffices H : ∀ d (q : ℂ[X]), (∀ N, d ≤ N → q.coeff N = 0) →
      ∃ p : ℂ[X], C α * p.comp (X + 1) - C α * p = q by
    refine H (q.natDegree + 1) q fun N hN ↦ coeff_eq_zero_of_natDegree_lt (by omega)
  intro d
  induction d with
  | zero =>
    intro q hq
    refine ⟨0, ?_⟩
    ext N
    simp [hq N (Nat.zero_le N)]
  | succ d ih =>
    intro q hq
    set c := q.coeff d with hc
    have hd1 : ((d + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
    set p₀ : ℂ[X] := C (c / (α * (d + 1 : ℕ))) * X ^ (d + 1) with hp₀
    set r := q - (C α * p₀.comp (X + 1) - C α * p₀) with hr
    have hrc : ∀ N, d ≤ N → r.coeff N = 0 := by
      intro N hN
      simp only [hr, hp₀, coeff_sub, mul_comp, C_comp, X_pow_comp, coeff_C_mul, coeff_X_pow,
        coeff_X_add_one_pow]
      rcases hN.lt_or_eq with hlt | rfl
      · rw [hq N hlt]
        rcases (Nat.succ_le_of_lt hlt).lt_or_eq with hlt' | heq
        · rw [Nat.choose_eq_zero_of_lt hlt', ite_eq_right (Nat.ne_of_gt hlt')]
          simp
        · rw [← heq, Nat.choose_self, ite_eq_left rfl]
          ring
      · rw [Nat.choose_succ_self_right, ite_eq_right (Nat.succ_ne_self d).symm, ← hc]
        field_simp
        push_cast
        ring
    obtain ⟨p₁, hp₁⟩ := ih r hrc
    refine ⟨p₀ + p₁, ?_⟩
    rw [add_comp]
    have : r = q - (C α * p₀.comp (X + 1) - C α * p₀) := hr
    rw [← hp₁] at this
    linear_combination this

/-- **First-order step.**  If `b` is polynomial-exponential with frequencies in `S` and
`a(n+1) = λ a(n) + b(n)` with `λ ≠ 0`, then `a` is polynomial-exponential with frequencies in
`insert λ S`. -/
theorem IsPolyExp.of_first_order {S : Finset ℂ} {a b : ℕ → ℂ} {l : ℂ} (hl : l ≠ 0)
    (hb : IsPolyExp S b) (hrec : ∀ n, a (n + 1) = l * a n + b n) :
    IsPolyExp (insert l S) a := by
  classical
  obtain ⟨q, hq⟩ := hb
  have hex : ∀ μ, ∃ r : ℂ[X], C μ * r.comp (X + 1) - C l * r = q μ := by
    intro μ
    by_cases hμ : μ = l
    · subst hμ
      exact exists_shift_solution_of_eq hl (q μ)
    · exact exists_shift_solution_of_ne hμ (q μ)
  choose r hr using hex
  set s : ℕ → ℂ := fun n ↦ ∑ μ ∈ S, (r μ).eval (n : ℂ) * μ ^ n with hs
  have hreval : ∀ μ (n : ℕ), μ * (r μ).eval ((n : ℂ) + 1) - l * (r μ).eval (n : ℂ) =
      (q μ).eval (n : ℂ) := by
    intro μ n
    have := congrArg (eval (n : ℂ)) (hr μ)
    simpa [eval_comp] using this
  have hsrec : ∀ n, s (n + 1) = l * s n + b n := by
    intro n
    simp only [hs, hq, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun μ _ ↦ ?_
    have h := hreval μ n
    push_cast
    rw [pow_succ]
    linear_combination μ ^ n * h
  -- the homogeneous remainder
  set h : ℕ → ℂ := fun n ↦ a n - s n with hh
  have hhrec : ∀ n, h (n + 1) = l * h n := fun n ↦ by
    simp only [hh, hrec, hsrec]
    ring
  have hhform : ∀ n, h n = h 0 * l ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hhrec, ih, pow_succ]; ring
  have hsPE : IsPolyExp S s := ⟨r, fun n ↦ rfl⟩
  have hhPE : IsPolyExp {l} (fun n ↦ (C (h 0)).eval (n : ℂ) * l ^ n) := IsPolyExp.single _ l
  have := (hsPE.mono (subset_insert l S)).add (hhPE.mono (by simp))
  convert this using 1
  funext n
  simp only [Pi.add_apply, eval_C]
  rw [← hhform n, hh]
  ring

/-- The shift operator `(E a)(n) = a(n+1)` on sequences. -/
def shiftOp : Module.End ℂ (ℕ → ℂ) where
  toFun a n := a (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem shiftOp_pow_apply (i : ℕ) (a : ℕ → ℂ) (n : ℕ) : (shiftOp ^ i) a n = a (n + i) := by
  induction i generalizing n a with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    rfl

theorem aeval_shiftOp_apply (p : ℂ[X]) (a : ℕ → ℂ) (n : ℕ) :
    (aeval shiftOp p) a n = ∑ i ∈ range (p.natDegree + 1), p.coeff i * a (n + i) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, shiftOp_pow_apply, smul_eq_mul]

end WeakTiling

end

end PolyExp

/-! ## Step W core: nonnegative power sums with linear partial sums are bounded -/

section RowBound

section

open Finset Complex

namespace WeakTiling

/-- Geometric partial sums of a unit phase `μ ≠ 1` are bounded by `2 / ‖1 - μ‖`. -/
theorem norm_geom_sum_le_of_unit {μ : ℂ} (hμ : ‖μ‖ = 1) (hμ1 : μ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, μ ^ n‖ ≤ 2 / ‖1 - μ‖ := by
  rw [geom_sum_eq hμ1, norm_div, norm_sub_rev μ 1]
  have hpos : 0 < ‖1 - μ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hμ1))
  gcongr
  calc ‖μ ^ N - 1‖ ≤ ‖μ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hμ, one_pow, norm_one]; norm_num

/-- Summation by parts. -/
theorem sum_mul_sub_eq_summation_by_parts (f G : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ range N, f n * (G (n + 1) - G n) =
      f N * G N - f 0 * G 0 - ∑ n ∈ range N, (f (n + 1) - f n) * G (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- A monotone nonnegative weight against a unit phase `μ ≠ 1`:
`‖∑_{n<N} f(n) μⁿ‖ ≤ 4 f(N) / ‖1 - μ‖`. -/
theorem norm_sum_monotone_mul_pow_le {μ : ℂ} (hμ : ‖μ‖ = 1) (hμ1 : μ ≠ 1) (f : ℕ → ℝ)
    (hf0 : 0 ≤ f 0) (hmono : Monotone f) (N : ℕ) :
    ‖∑ n ∈ range N, (f n : ℂ) * μ ^ n‖ ≤ 4 / ‖1 - μ‖ * f N := by
  set B := 2 / ‖1 - μ‖ with hB
  have hBnn : 0 ≤ B := by positivity
  set G : ℕ → ℂ := fun m ↦ ∑ n ∈ range m, μ ^ n with hGdef
  have hG : ∀ m, ‖G m‖ ≤ B := norm_geom_sum_le_of_unit hμ hμ1
  have hstep : ∀ n, G (n + 1) - G n = μ ^ n := fun n ↦ by
    simp [G, sum_range_succ]
  have hid := sum_mul_sub_eq_summation_by_parts (fun n ↦ (f n : ℂ)) G N
  simp only [hstep] at hid
  have hG0 : G 0 = 0 := by simp [G]
  rw [hid, hG0, mul_zero, sub_zero]
  have hfN : 0 ≤ f N := hf0.trans (hmono (Nat.zero_le N))
  have h1 : ‖(f N : ℂ) * G N‖ ≤ f N * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hfN]
    exact mul_le_mul_of_nonneg_left (hG N) hfN
  have h2 : ‖∑ n ∈ range N, ((f (n + 1) : ℂ) - f n) * G (n + 1)‖ ≤
      ∑ n ∈ range N, (f (n + 1) - f n) * B := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ ↦ ?_)
    have hd : 0 ≤ f (n + 1) - f n := sub_nonneg.mpr (hmono (Nat.le_succ n))
    rw [norm_mul, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hd]
    exact mul_le_mul_of_nonneg_left (hG _) hd
  have htel : ∑ n ∈ range N, (f (n + 1) - f n) * B = (f N - f 0) * B := by
    rw [← sum_mul, sum_range_sub]
  calc ‖(f N : ℂ) * G N - ∑ n ∈ range N, ((f (n + 1) : ℂ) - f n) * G (n + 1)‖
      ≤ f N * B + ∑ n ∈ range N, (f (n + 1) - f n) * B :=
        (norm_sub_le _ _).trans (add_le_add h1 h2)
    _ = f N * B + (f N - f 0) * B := by rw [htel]
    _ ≤ 4 / ‖1 - μ‖ * f N := by
        rw [hB]
        have : 0 ≤ f 0 * (2 / ‖1 - μ‖) := mul_nonneg hf0 (by positivity)
        have h4 : 4 / ‖1 - μ‖ = 2 * (2 / ‖1 - μ‖) := by ring
        rw [h4]
        nlinarith

/-- `‖∑_{n<N} nᵏ μⁿ‖ ≤ 4 Nᵏ / ‖1 - μ‖` for a unit phase `μ ≠ 1`. -/
theorem norm_sum_pow_mul_pow_le {μ : ℂ} (hμ : ‖μ‖ = 1) (hμ1 : μ ≠ 1) (k N : ℕ) :
    ‖∑ n ∈ range N, (n : ℂ) ^ k * μ ^ n‖ ≤ 4 / ‖1 - μ‖ * (N : ℝ) ^ k := by
  have h := norm_sum_monotone_mul_pow_le hμ hμ1 (fun n ↦ (n : ℝ) ^ k) (by positivity)
    (fun x y hxy ↦ pow_le_pow_left₀ (Nat.cast_nonneg x) (Nat.cast_le.mpr hxy) k) N
  push_cast at h
  exact h

/-- `∑_{n<N} nᵏ ≤ N^{k+1}`. -/
theorem sum_pow_le_pow_succ (k N : ℕ) : ∑ n ∈ range N, (n : ℝ) ^ k ≤ (N : ℝ) ^ (k + 1) := by
  calc ∑ n ∈ range N, (n : ℝ) ^ k ≤ ∑ _n ∈ range N, (N : ℝ) ^ k :=
        sum_le_sum fun n hn ↦ pow_le_pow_left₀ (Nat.cast_nonneg n)
          (Nat.cast_le.mpr (mem_range.mp hn).le) k
    _ = (N : ℝ) ^ (k + 1) := by rw [sum_const, card_range, nsmul_eq_mul, pow_succ]; ring

/-- `∑_{n<2M} nᵈ ≥ M^{d+1}`. -/
theorem pow_succ_le_sum_pow (d M : ℕ) :
    (M : ℝ) ^ (d + 1) ≤ ∑ n ∈ range (M + M), (n : ℝ) ^ d := by
  rw [sum_range_add]
  have h1 : 0 ≤ ∑ n ∈ range M, (n : ℝ) ^ d := sum_nonneg fun n _ ↦ by positivity
  have h2 : ∑ _n ∈ range M, (M : ℝ) ^ d ≤ ∑ n ∈ range M, ((M + n : ℕ) : ℝ) ^ d :=
    sum_le_sum fun n _ ↦ pow_le_pow_left₀ (Nat.cast_nonneg M)
      (Nat.cast_le.mpr (Nat.le_add_right M n)) d
  rw [sum_const, card_range, nsmul_eq_mul] at h2
  rw [pow_succ']
  linarith

end WeakTiling

end

end RowBound

/-! ## Step W assembled: from a linear recurrence to bounded row sums -/

section RowBoundAssembly

section

open Polynomial Finset Filter Topology

namespace WeakTiling

/-- A polynomial times a geometric sequence with ratio of modulus `< 1` is bounded. -/
theorem exists_bound_poly_mul_pow {μ : ℂ} (hμ : ‖μ‖ < 1) (p : ℂ[X]) :
    ∃ B : ℝ, ∀ n : ℕ, ‖p.eval (n : ℂ) * μ ^ n‖ ≤ B := by
  set r := ‖μ‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hdec : ∀ i : ℕ, ∃ Bi : ℝ, ∀ n : ℕ, (n : ℝ) ^ i * r ^ n ≤ Bi := by
    intro i
    have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one i (by rwa [abs_of_nonneg hr0])
    obtain ⟨Bi, hBi⟩ := ht.bddAbove_range
    exact ⟨Bi, fun n ↦ hBi ⟨n, rfl⟩⟩
  choose Bi hBi using hdec
  refine ⟨∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ * Bi i, fun n ↦ ?_⟩
  rw [eval_eq_sum_range, norm_mul]
  calc ‖∑ i ∈ range (p.natDegree + 1), p.coeff i * (n : ℂ) ^ i‖ * ‖μ ^ n‖
      ≤ (∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ * (n : ℝ) ^ i) * r ^ n := by
        refine mul_le_mul ((norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun i _ ↦ ?_)))
          (by rw [norm_pow]) (norm_nonneg _) (sum_nonneg fun i _ ↦ by positivity)
        rw [norm_mul, norm_pow, Complex.norm_natCast]
    _ = ∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ * ((n : ℝ) ^ i * r ^ n) := by
        rw [sum_mul]
        exact sum_congr rfl fun i _ ↦ by ring
    _ ≤ ∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ * Bi i :=
        sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hBi i n) (norm_nonneg _)

end WeakTiling

end

end RowBoundAssembly

/-! ## Finite Cesàro orthogonality for unit complex phases -/

section Cesaro

section

open Filter Topology Complex
open scoped BigOperators

namespace WeakTiling

set_option maxHeartbeats 800000

/-- The Cesàro average of the first `N` powers of `z`. -/
noncomputable def cesaroPowers (N : ℕ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, z ^ k

/-- A unit-modulus phase different from `1` has vanishing Cesàro power average. -/
theorem tendsto_cesaroPowers_zero {z : ℂ} (hz : z ≠ 1) (hznorm : ‖z‖ = 1) :
    Tendsto (fun N : ℕ ↦ cesaroPowers N z) atTop (𝓝 0) := by
  have hden : 0 < ‖z - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hz
  have hgeom : ∀ N : ℕ, ‖∑ k ∈ Finset.range N, z ^ k‖ ≤ 2 / ‖z - 1‖ := by
    intro N
    rw [geom_sum_eq hz, norm_div]
    have hnum : ‖z ^ N - 1‖ ≤ 2 := by
      calc
        ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hznorm, one_pow, norm_one]; norm_num
    rw [div_le_div_iff_of_pos_right hden]
    exact hnum
  have hbound : ∀ N : ℕ, 0 < N →
      ‖cesaroPowers N z‖ ≤ (2 / ‖z - 1‖) / (N : ℝ) := by
    intro N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [cesaroPowers, norm_mul, norm_inv]
    have hn : ‖(N : ℂ)‖ = (N : ℝ) := by simp
    rw [hn, inv_mul_eq_div, div_le_div_iff_of_pos_right hNpos]
    exact hgeom N
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun N : ℕ ↦ (2 / ‖z - 1‖) / (N : ℝ))
    (Eventually.of_forall fun N ↦ norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN using hbound N hN
  · exact tendsto_const_div_atTop_nhds_zero_nat _

/-- The Cesàro power average of the constant phase `1` tends to `1`. -/
theorem tendsto_cesaroPowers_one :
    Tendsto (fun N : ℕ ↦ cesaroPowers N 1) atTop (𝓝 1) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop 0] with N hN
  simp [cesaroPowers, hN.ne']

/-- The common pointwise form of Cesàro orthogonality. -/
theorem tendsto_cesaroPowers {z : ℂ} (hznorm : ‖z‖ = 1) :
    Tendsto (fun N : ℕ ↦ cesaroPowers N z) atTop
      (𝓝 (if z = 1 then 1 else 0)) := by
  by_cases hz : z = 1
  · subst z
    simpa using tendsto_cesaroPowers_one
  · simpa [hz] using tendsto_cesaroPowers_zero hz hznorm

/-- The finite double Cesàro sum attached to amplitudes `a` and phases `λ`. -/
noncomputable def finitePhaseCesaro {ι : Type*} [Fintype ι]
    (a phase : ι → ℂ) (N : ℕ) : ℂ :=
  ∑ i, ∑ j, (a i * (starRingEnd ℂ) (a j)) *
    cesaroPowers N (phase i * (starRingEnd ℂ) (phase j))

/-- Finite Cesàro orthogonality: if the phase products are `1` exactly on the diagonal and have
unit modulus, then the double average tends to the sum of squared amplitudes. -/
theorem tendsto_finitePhaseCesaro {ι : Type*} [Fintype ι]
    (a phase : ι → ℂ)
    (hdiag : ∀ i, phase i * (starRingEnd ℂ) (phase i) = 1)
    (hoff : ∀ i j, i ≠ j → phase i * (starRingEnd ℂ) (phase j) ≠ 1)
    (hnorm : ∀ i j, ‖phase i * (starRingEnd ℂ) (phase j)‖ = 1) :
    Tendsto (fun N : ℕ ↦ finitePhaseCesaro a phase N) atTop
      (𝓝 (∑ i, a i * (starRingEnd ℂ) (a i))) := by
  classical
  have hterm : ∀ i j,
      Tendsto
        (fun N : ℕ ↦ (a i * (starRingEnd ℂ) (a j)) *
          cesaroPowers N (phase i * (starRingEnd ℂ) (phase j)))
        atTop (𝓝 (if i = j then a i * (starRingEnd ℂ) (a i) else 0)) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [hdiag i] using
        (tendsto_const_nhds.mul (tendsto_cesaroPowers (hnorm i i)))
    · simpa [hij, hoff i j hij] using
        (tendsto_const_nhds.mul (tendsto_cesaroPowers (hnorm i j)))
  have hsum : Tendsto
      (fun N : ℕ ↦ ∑ i, ∑ j,
        (a i * (starRingEnd ℂ) (a j)) *
          cesaroPowers N (phase i * (starRingEnd ℂ) (phase j)))
      atTop (𝓝 (∑ i, ∑ j, if i = j then a i * (starRingEnd ℂ) (a i) else 0)) :=
    tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ hterm i j
  simpa [finitePhaseCesaro] using hsum

/-- The hypotheses of `tendsto_finitePhaseCesaro` follow from pairwise distinct unit-modulus
phases. -/
theorem tendsto_finitePhaseCesaro_of_unit_injective {ι : Type*} [Fintype ι]
    (a phase : ι → ℂ) (hunit : ∀ i, ‖phase i‖ = 1)
    (hinj : Function.Injective phase) :
    Tendsto (fun N : ℕ ↦ finitePhaseCesaro a phase N) atTop
      (𝓝 (∑ i, a i * (starRingEnd ℂ) (a i))) := by
  apply tendsto_finitePhaseCesaro a phase
  · intro i
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq, hunit i]
  · intro i j hij hprod
    apply hij
    apply hinj
    have hj : (starRingEnd ℂ) (phase j) * phase j = 1 := by
      rw [mul_comm, Complex.mul_conj]
      simp [Complex.normSq_eq_norm_sq, hunit j]
    calc
      phase i = phase i * 1 := by simp
      _ = phase i * ((starRingEnd ℂ) (phase j) * phase j) := by rw [hj]
      _ = (phase i * (starRingEnd ℂ) (phase j)) * phase j := by ring
      _ = phase j := by rw [hprod]; simp
  · intro i j
    simp [hunit i, hunit j]

/-- The actual Cesàro average of the squared modulus of a finite exponential sum. -/
noncomputable def phaseEnergyAverage {ι : Type*} [Fintype ι]
    (a phase : ι → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N,
    (∑ i, a i * phase i ^ k) *
      (starRingEnd ℂ) (∑ i, a i * phase i ^ k)

/-- Expanding the squared modulus turns the energy average into the double phase sum. -/
lemma phaseEnergyAverage_eq_finitePhaseCesaro {ι : Type*} [Fintype ι]
    (a phase : ι → ℂ) (N : ℕ) :
    phaseEnergyAverage a phase N = finitePhaseCesaro a phase N := by
  classical
  simp only [phaseEnergyAverage, finitePhaseCesaro, cesaroPowers,
    map_sum, map_mul, map_pow]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  ring_nf

/-- Cesàro energy identity for a finite family of pairwise distinct unit phases. -/
theorem tendsto_phaseEnergyAverage_of_unit_injective {ι : Type*} [Fintype ι]
    (a phase : ι → ℂ) (hunit : ∀ i, ‖phase i‖ = 1)
    (hinj : Function.Injective phase) :
    Tendsto (fun N : ℕ ↦ phaseEnergyAverage a phase N) atTop
      (𝓝 (∑ i, a i * (starRingEnd ℂ) (a i))) := by
  simpa only [phaseEnergyAverage_eq_finitePhaseCesaro] using
    tendsto_finitePhaseCesaro_of_unit_injective a phase hunit hinj

/-- The real-valued version of `phaseEnergyAverage`.  This is the form used for inequalities. -/
noncomputable def realPhaseEnergyAverage {ι : Type*} [Fintype ι]
    (a phase : ι → ℂ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, ‖∑ i, a i * phase i ^ k‖ ^ 2

/-- A complex number times its conjugate is its squared norm, viewed in `ℂ`. -/
lemma mul_conj_eq_coe_norm_sq (z : ℂ) :
    z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj]
  congr 1
  exact Complex.normSq_eq_norm_sq z

/-- The complex energy average is the coercion of the real nonnegative average. -/
lemma phaseEnergyAverage_eq_coe_realPhaseEnergyAverage {ι : Type*} [Fintype ι]
    (a phase : ι → ℂ) (N : ℕ) :
    phaseEnergyAverage a phase N = (realPhaseEnergyAverage a phase N : ℂ) := by
  classical
  rw [phaseEnergyAverage, realPhaseEnergyAverage]
  calc
    (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N,
          (∑ i, a i * phase i ^ k) * (starRingEnd ℂ) (∑ i, a i * phase i ^ k) =
        (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N,
          ((‖∑ i, a i * phase i ^ k‖ ^ 2 : ℝ) : ℂ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      exact mul_conj_eq_coe_norm_sq _
    _ = (((N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
          ‖∑ i, a i * phase i ^ k‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl

/-- Real Cesàro energy identity for pairwise distinct unit phases. -/
theorem tendsto_realPhaseEnergyAverage_of_unit_injective {ι : Type*} [Fintype ι]
    (a phase : ι → ℂ) (hunit : ∀ i, ‖phase i‖ = 1)
    (hinj : Function.Injective phase) :
    Tendsto (fun N : ℕ ↦ realPhaseEnergyAverage a phase N) atTop
      (𝓝 (∑ i, ‖a i‖ ^ 2)) := by
  rw [← Filter.tendsto_ofReal_iff]
  have hlimit :
      ((∑ i, ‖a i‖ ^ 2 : ℝ) : ℂ) = ∑ i, ((‖a i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hlimit]
  simpa only [phaseEnergyAverage_eq_coe_realPhaseEnergyAverage,
    mul_conj_eq_coe_norm_sq] using
    tendsto_phaseEnergyAverage_of_unit_injective a phase hunit hinj

/-- A uniform bound on a finite exponential sum bounds the square-sum of its amplitudes.

This is the quantitative extraction statement needed later: after a collision set has been
represented by distinct unit phases, a pointwise bound by `M` forces its Fourier--Bohr
coefficients to have total energy at most `M²`. -/
theorem sum_norm_sq_le_of_exponential_sum_bounded {ι : Type*} [Fintype ι]
    (a phase : ι → ℂ) (hunit : ∀ i, ‖phase i‖ = 1)
    (hinj : Function.Injective phase) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ k : ℕ, ‖∑ i, a i * phase i ^ k‖ ≤ M) :
    ∑ i, ‖a i‖ ^ 2 ≤ M ^ 2 := by
  apply le_of_tendsto'
    (tendsto_realPhaseEnergyAverage_of_unit_injective a phase hunit hinj)
  intro N
  by_cases hN : N = 0
  · simp [hN, realPhaseEnergyAverage, sq_nonneg M]
  · have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    have hterm : ∀ k : ℕ, ‖∑ i, a i * phase i ^ k‖ ^ 2 ≤ M ^ 2 := by
      intro k
      nlinarith [norm_nonneg (∑ i, a i * phase i ^ k), hbound k]
    have hsum :
        ∑ k ∈ Finset.range N, ‖∑ i, a i * phase i ^ k‖ ^ 2 ≤
          ∑ k ∈ Finset.range N, M ^ 2 :=
      Finset.sum_le_sum fun k _ ↦ hterm k
    rw [realPhaseEnergyAverage]
    calc
      (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, ‖∑ i, a i * phase i ^ k‖ ^ 2
          ≤ (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, M ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = M ^ 2 := by
        simp [hN]

/-- The amplitude bound only needs a uniform estimate on an arbitrary tail `k ≥ n₀`. -/
theorem sum_norm_sq_le_of_exponential_sum_bounded_from {ι : Type*} [Fintype ι]
    (a phase : ι → ℂ) (hunit : ∀ i, ‖phase i‖ = 1)
    (hinj : Function.Injective phase) (n₀ : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ k : ℕ, n₀ ≤ k → ‖∑ i, a i * phase i ^ k‖ ≤ M) :
    ∑ i, ‖a i‖ ^ 2 ≤ M ^ 2 := by
  classical
  have hshift := sum_norm_sq_le_of_exponential_sum_bounded
    (fun i ↦ a i * phase i ^ n₀) phase hunit hinj M hM
    (fun k ↦ by
      simpa only [mul_assoc, ← pow_add] using
        hbound (n₀ + k) (Nat.le_add_right n₀ k))
  simpa only [norm_mul, norm_pow, hunit, one_pow, mul_one] using hshift

end WeakTiling

end

end Cesaro

/-! ## Step W: excluding characteristic roots outside the unit disk -/

section RootExclusion

section

open Polynomial Finset Filter Topology

namespace WeakTiling

/-- A polynomial times a geometric sequence of ratio `< 1` in modulus tends to `0`. -/
theorem tendsto_poly_mul_pow_zero {z : ℂ} (hz : ‖z‖ < 1) (p : ℂ[X]) :
    Tendsto (fun n : ℕ ↦ p.eval (n : ℂ) * z ^ n) atTop (𝓝 0) := by
  set r := ‖z‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hg : Tendsto (fun n : ℕ ↦ ∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ * ((n : ℝ) ^ i * r ^ n))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (range (p.natDegree + 1)) fun i _ ↦
      (tendsto_pow_const_mul_const_pow_of_abs_lt_one i (by rwa [abs_of_nonneg hr0])).const_mul
        ‖p.coeff i‖
    simpa using this
  refine squeeze_zero_norm (fun n ↦ ?_) hg
  rw [eval_eq_sum_range, norm_mul, norm_pow]
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)).trans ?_
  rw [sum_mul]
  refine le_of_eq (sum_congr rfl fun i _ ↦ ?_)
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  ring

/-- **Cesàro vanishing.**  If `∑ⱼ cⱼ ωⱼⁿ → 0` for distinct unit phases, every `cⱼ` is zero. -/
theorem coeffs_eq_zero_of_tendsto_zero {ι : Type*} [Fintype ι] (c ω : ι → ℂ)
    (hω : ∀ i, ‖ω i‖ = 1) (hinj : Function.Injective ω)
    (h : Tendsto (fun n : ℕ ↦ ∑ i, c i * ω i ^ n) atTop (𝓝 0)) : ∀ i, c i = 0 := by
  have hS : ∀ ε > 0, ∑ i, ‖c i‖ ^ 2 ≤ ε ^ 2 := by
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.mp h) ε hε
    exact sum_norm_sq_le_of_exponential_sum_bounded_from c ω hω hinj n₀ ε hε.le fun k hk ↦ by
      have := hn₀ k hk
      rw [dist_zero_right] at this
      exact this.le
  have h0 : 0 ≤ ∑ i, ‖c i‖ ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg _
  have hzero : ∑ i, ‖c i‖ ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < ∑ i, ‖c i‖ ^ 2 := lt_of_le_of_ne h0 (Ne.symm hne)
    have := hS (Real.sqrt ((∑ i, ‖c i‖ ^ 2) / 2)) (Real.sqrt_pos.mpr (by positivity))
    rw [Real.sq_sqrt (by positivity)] at this
    linarith
  intro i
  have hi := (sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg ‖c i‖).mp hzero i (mem_univ i)
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hi)

end WeakTiling

end

end RootExclusion

/-! ## Polynomial-exponential sums with multiplicity bounds -/

section PolyExpMult

section

open Polynomial Finset

namespace WeakTiling

/-- Polynomial-exponential sums whose amplitude at `μ` has degree `< count μ s`. -/
def IsPolyExpMult (s : Multiset ℂ) (a : ℕ → ℂ) : Prop :=
  ∃ p : ℂ → ℂ[X], (∀ μ k, s.count μ ≤ k → (p μ).coeff k = 0) ∧
    ∀ n, a n = ∑ μ ∈ s.toFinset, (p μ).eval (n : ℂ) * μ ^ n

/-- The amplitudes vanish off the multiset, so the sum can be taken over any larger finset. -/
theorem sum_eq_of_count_zero {s : Multiset ℂ} {p : ℂ → ℂ[X]}
    (hp : ∀ μ k, s.count μ ≤ k → (p μ).coeff k = 0) {T : Finset ℂ} (hT : s.toFinset ⊆ T)
    (n : ℕ) : ∑ μ ∈ s.toFinset, (p μ).eval (n : ℂ) * μ ^ n =
      ∑ μ ∈ T, (p μ).eval (n : ℂ) * μ ^ n := by
  classical
  apply sum_subset hT
  intro μ _ hμ
  have hc : s.count μ = 0 := Multiset.count_eq_zero.mpr fun h ↦ hμ (Multiset.mem_toFinset.mpr h)
  have hp0 : p μ = 0 := by
    ext k
    rw [coeff_zero]
    exact hp μ k (by omega)
  simp [hp0]

/-- Degree-controlled solution of `α r(X+1) - β r(X) = q` for `α ≠ β`. -/
theorem exists_shift_solution_of_ne_deg {α β : ℂ} (hαβ : α ≠ β) :
    ∀ d (q : ℂ[X]), (∀ N, d ≤ N → q.coeff N = 0) →
      ∃ p : ℂ[X], (∀ N, d ≤ N → p.coeff N = 0) ∧ C α * p.comp (X + 1) - C β * p = q := by
  have hsub : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  intro d
  induction d with
  | zero =>
    intro q hq
    refine ⟨0, fun N _ ↦ by simp, ?_⟩
    ext N
    simp [hq N (Nat.zero_le N)]
  | succ d ih =>
    intro q hq
    set c := q.coeff d with hc
    set p₀ : ℂ[X] := C (c / (α - β)) * X ^ d with hp₀
    set r := q - (C α * p₀.comp (X + 1) - C β * p₀) with hr
    have hrc : ∀ N, d ≤ N → r.coeff N = 0 := by
      intro N hN
      simp only [hr, hp₀, coeff_sub, mul_comp, C_comp, X_pow_comp, coeff_C_mul, coeff_X_pow,
        coeff_X_add_one_pow]
      rcases hN.lt_or_eq with hlt | rfl
      · rw [hq N hlt, Nat.choose_eq_zero_of_lt hlt, ite_eq_right (Nat.ne_of_gt hlt)]
        simp
      · rw [Nat.choose_self, ite_eq_left rfl, ← hc]
        field_simp
        ring
    obtain ⟨p₁, hp₁deg, hp₁⟩ := ih r hrc
    refine ⟨p₀ + p₁, fun N hN ↦ ?_, ?_⟩
    · rw [coeff_add, hp₁deg N (by omega), hp₀, coeff_C_mul, coeff_X_pow, ite_eq_right (by omega)]
      simp
    · rw [add_comp]
      have : r = q - (C α * p₀.comp (X + 1) - C β * p₀) := hr
      rw [← hp₁] at this
      linear_combination this

/-- Degree-controlled solution of `α r(X+1) - α r(X) = q` for `α ≠ 0`. -/
theorem exists_shift_solution_of_eq_deg {α : ℂ} (hα : α ≠ 0) :
    ∀ d (q : ℂ[X]), (∀ N, d ≤ N → q.coeff N = 0) →
      ∃ p : ℂ[X], (∀ N, d + 1 ≤ N → p.coeff N = 0) ∧ C α * p.comp (X + 1) - C α * p = q := by
  intro d
  induction d with
  | zero =>
    intro q hq
    refine ⟨0, fun N _ ↦ by simp, ?_⟩
    ext N
    simp [hq N (Nat.zero_le N)]
  | succ d ih =>
    intro q hq
    set c := q.coeff d with hc
    have hd1 : ((d + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
    set p₀ : ℂ[X] := C (c / (α * (d + 1 : ℕ))) * X ^ (d + 1) with hp₀
    set r := q - (C α * p₀.comp (X + 1) - C α * p₀) with hr
    have hrc : ∀ N, d ≤ N → r.coeff N = 0 := by
      intro N hN
      simp only [hr, hp₀, coeff_sub, mul_comp, C_comp, X_pow_comp, coeff_C_mul, coeff_X_pow,
        coeff_X_add_one_pow]
      rcases hN.lt_or_eq with hlt | rfl
      · rw [hq N hlt]
        rcases (Nat.succ_le_of_lt hlt).lt_or_eq with hlt' | heq
        · rw [Nat.choose_eq_zero_of_lt hlt', ite_eq_right (Nat.ne_of_gt hlt')]
          simp
        · rw [← heq, Nat.choose_self, ite_eq_left rfl]
          ring
      · rw [Nat.choose_succ_self_right, ite_eq_right (Nat.succ_ne_self d).symm, ← hc]
        field_simp
        push_cast
        ring
    obtain ⟨p₁, hp₁deg, hp₁⟩ := ih r hrc
    refine ⟨p₀ + p₁, fun N hN ↦ ?_, ?_⟩
    · rw [coeff_add, hp₁deg N (by omega), hp₀, coeff_C_mul, coeff_X_pow, ite_eq_right (by omega)]
      simp
    · rw [add_comp]
      have : r = q - (C α * p₀.comp (X + 1) - C α * p₀) := hr
      rw [← hp₁] at this
      linear_combination this

/-- **First-order step with multiplicities.** -/
theorem IsPolyExpMult.of_first_order {t : Multiset ℂ} {a b : ℕ → ℂ} {l : ℂ} (hl : l ≠ 0)
    (hb : IsPolyExpMult t b) (hrec : ∀ n, a (n + 1) = l * a n + b n) :
    IsPolyExpMult (l ::ₘ t) a := by
  classical
  obtain ⟨q, hqdeg, hq⟩ := hb
  set s := l ::ₘ t with hs
  have hex : ∀ μ, ∃ r : ℂ[X], (∀ N, s.count μ ≤ N → r.coeff N = 0) ∧
      C μ * r.comp (X + 1) - C l * r = q μ := by
    intro μ
    by_cases hμ : μ = l
    · subst hμ
      obtain ⟨r, hrdeg, hr⟩ := exists_shift_solution_of_eq_deg hl (t.count μ) (q μ) (hqdeg μ)
      refine ⟨r, fun N hN ↦ hrdeg N ?_, hr⟩
      rw [hs, Multiset.count_cons_self] at hN
      exact hN
    · obtain ⟨r, hrdeg, hr⟩ := exists_shift_solution_of_ne_deg hμ (t.count μ) (q μ) (hqdeg μ)
      refine ⟨r, fun N hN ↦ hrdeg N ?_, hr⟩
      rw [hs, Multiset.count_cons_of_ne hμ] at hN
      exact hN
  choose r hrdeg hr using hex
  set F := s.toFinset with hF
  have hsub : t.toFinset ⊆ F := by
    intro μ hμ
    rw [hF, Multiset.mem_toFinset]
    exact Multiset.mem_cons_of_mem (Multiset.mem_toFinset.mp hμ)
  have hlF : l ∈ F := by
    rw [hF, Multiset.mem_toFinset]
    exact Multiset.mem_cons_self l t
  have hqF : ∀ n, b n = ∑ μ ∈ F, (q μ).eval (n : ℂ) * μ ^ n := fun n ↦ by
    rw [hq n, sum_eq_of_count_zero hqdeg hsub]
  set sp : ℕ → ℂ := fun n ↦ ∑ μ ∈ F, (r μ).eval (n : ℂ) * μ ^ n with hsp
  have hreval : ∀ μ (n : ℕ), μ * (r μ).eval ((n : ℂ) + 1) - l * (r μ).eval (n : ℂ) =
      (q μ).eval (n : ℂ) := by
    intro μ n
    have := congrArg (eval (n : ℂ)) (hr μ)
    simpa [eval_comp] using this
  have hsrec : ∀ n, sp (n + 1) = l * sp n + b n := by
    intro n
    simp only [hsp, hqF, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun μ _ ↦ ?_
    have h := hreval μ n
    push_cast
    rw [pow_succ]
    linear_combination μ ^ n * h
  set h : ℕ → ℂ := fun n ↦ a n - sp n with hh
  have hhrec : ∀ n, h (n + 1) = l * h n := fun n ↦ by
    simp only [hh, hrec, hsrec]
    ring
  have hhform : ∀ n, h n = h 0 * l ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hhrec, ih, pow_succ]; ring
  refine ⟨fun μ ↦ r μ + if μ = l then C (h 0) else 0, fun μ k hk ↦ ?_, fun n ↦ ?_⟩
  · rw [coeff_add, hrdeg μ k hk]
    split_ifs with hμ
    · subst hμ
      have : 1 ≤ k := by
        rw [hs, Multiset.count_cons_self] at hk
        omega
      rw [coeff_C, ite_eq_right (by omega), zero_add]
    · simp
  · have : a n = sp n + h 0 * l ^ n := by rw [← hhform n, hh]; ring
    rw [this, hsp]
    simp only [eval_add, add_mul, sum_add_distrib]
    congr 1
    rw [sum_eq_single_of_mem l hlF]
    · simp
    · intro μ _ hμ
      simp [hμ]

/-- The shift annihilated by `∏ (E - μ)`: multiplicity version. -/
theorem isPolyExpMult_of_aeval_prod_eq_zero (s : Multiset ℂ) (hs : ∀ μ ∈ s, μ ≠ 0) :
    ∀ a : ℕ → ℂ, aeval shiftOp (s.map fun μ ↦ X - C μ).prod a = 0 → IsPolyExpMult s a := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
    intro a ha
    simp only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_apply] at ha
    subst ha
    exact ⟨fun _ ↦ 0, fun μ k _ ↦ by simp, fun n ↦ by simp⟩
  | cons μ t ih =>
    intro a ha
    have hμ : μ ≠ 0 := hs μ (Multiset.mem_cons_self μ t)
    rw [Multiset.map_cons, Multiset.prod_cons, mul_comm, map_mul, Module.End.mul_apply] at ha
    set b := aeval shiftOp (X - C μ) a with hb
    have hbPE := ih (fun ν hν ↦ hs ν (Multiset.mem_cons_of_mem hν)) b ha
    have hbform : ∀ n, b n = a (n + 1) - μ * a n := by
      intro n
      simp [hb, shiftOp, Module.algebraMap_end_apply]
    exact IsPolyExpMult.of_first_order hμ hbPE fun n ↦ by rw [hbform]; ring

/-- **Linear recurrences with multiplicities.**  If `χ` is monic, `χ(0) ≠ 0` and `χ(E) a = 0`,
then `aₙ = ∑_λ p_λ(n) λⁿ` with `deg p_λ < mult_χ(λ)`. -/
theorem isPolyExpMult_of_linearRecurrence (χ : ℂ[X]) (hmon : χ.Monic) (h0 : χ.coeff 0 ≠ 0)
    (a : ℕ → ℂ) (hrec : ∀ n, ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * a (n + i) = 0) :
    IsPolyExpMult χ.roots a := by
  have hprod : (χ.roots.map fun μ ↦ X - C μ).prod = χ :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon IsAlgClosed.card_roots_eq_natDegree
  have hne : ∀ μ ∈ χ.roots, μ ≠ 0 := by
    intro μ hμ h
    subst h
    have hroot := (mem_roots hmon.ne_zero).mp hμ
    rw [IsRoot, ← coeff_zero_eq_eval_zero] at hroot
    exact h0 hroot
  apply isPolyExpMult_of_aeval_prod_eq_zero χ.roots hne a
  rw [hprod]
  funext n
  rw [aeval_shiftOp_apply, hrec n]
  rfl

end WeakTiling

end

end PolyExpMult

/-! ## Pringsheim's theorem for nonnegative power sums, and step W without the Abel hypothesis -/

section Pringsheim

section

open Polynomial Finset Filter Topology

namespace WeakTiling

/-- **Top-degree coefficients vanish, polynomial-growth form.**

Suppose `aₙ ≥ 0` has partial sums `O(N^d)` and is a power sum of degree `≤ d` over distinct unit
roots plus an absolutely summable error.  Then every coefficient of `n^d` vanishes.  This is the
comparison used in Pringsheim's theorem: a degree-`d` term on the circle would force partial sums
of size `N^{d+1}`. -/
theorem top_coeff_eq_zero_of_nonneg_growth {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {C E : ℝ}
    (hsum : ∀ N, ∑ n ∈ range N, a n ≤ C * (N + 1) ^ d)
    (lam : ι → ℂ) (hlam : ∀ j, ‖lam j‖ = 1) (hinj : Function.Injective lam)
    (c : ι → ℕ → ℂ) (ε : ℕ → ℂ) (hε : ∀ N, ∑ n ∈ range N, ‖ε n‖ ≤ E)
    (hrep : ∀ n, (a n : ℂ) =
      ∑ j, ∑ k ∈ range (d + 1), c j k * (n : ℂ) ^ k * lam j ^ n + ε n) :
    ∀ j, c j d = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j0, hj0⟩ := hcon
  have hE : 0 ≤ E := by simpa using hε 0
  set ν := (starRingEnd ℂ) (lam j0) with hνdef
  have hνnorm : ‖ν‖ = 1 := by rw [hνdef, Complex.norm_conj, hlam]
  have hν0 : ν ≠ 0 := by
    intro h
    rw [h, norm_zero] at hνnorm
    exact zero_ne_one hνnorm
  set μ : ι → ℂ := fun j ↦ lam j * ν with hμdef
  have hμnorm : ∀ j, ‖μ j‖ = 1 := fun j ↦ by rw [hμdef, norm_mul, hlam, hνnorm, one_mul]
  have hμ0 : μ j0 = 1 := by
    simp only [hμdef, hνdef]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hlam]
    simp
  have hμne : ∀ j, j ≠ j0 → μ j ≠ 1 := by
    intro j hj h
    apply hj
    apply hinj
    exact mul_right_cancel₀ hν0 (h.trans hμ0.symm)
  set T : ℂ → ℕ → ℕ → ℂ := fun z k N ↦ ∑ n ∈ range N, (n : ℂ) ^ k * z ^ n with hTdef
  -- the twisted partial sums
  have hS : ∀ N, ∑ n ∈ range N, (a n : ℂ) * ν ^ n =
      ∑ j, ∑ k ∈ range (d + 1), c j k * T (μ j) k N + ∑ n ∈ range N, ε n * ν ^ n := by
    intro N
    simp_rw [hrep, add_mul, sum_add_distrib, sum_mul]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_comm]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [hTdef, mul_sum]
    refine sum_congr rfl fun n _ ↦ ?_
    simp only [hμdef, mul_pow]
    ring
  -- upper bound from positivity
  have hup : ∀ N, ‖∑ n ∈ range N, (a n : ℂ) * ν ^ n‖ ≤ C * (N + 1) ^ d := by
    intro N
    refine (norm_sum_le _ _).trans ((sum_le_sum fun n _ ↦ ?_).trans (hsum N))
    rw [norm_mul, norm_pow, hνnorm, one_pow, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (ha n)]
  -- constants for the remainder
  set Bj : ι → ℝ := fun j ↦ if j = j0 then 1 else 4 / ‖1 - μ j‖ with hBjdef
  have hBj : ∀ j, 0 ≤ Bj j := fun j ↦ by
    simp only [hBjdef]
    split_ifs <;> positivity
  set K : ℝ := ∑ j, ∑ k ∈ range (d + 1), ‖c j k‖ * Bj j with hKdef
  have hK : 0 ≤ K := sum_nonneg fun j _ ↦ sum_nonneg fun k _ ↦
    mul_nonneg (norm_nonneg _) (hBj j)
  -- split off the top term of `j0`
  set X : ι → ℕ → ℕ → ℂ := fun j k N ↦ c j k * T (μ j) k N with hXdef
  have hsplit : ∀ N, ∑ j, ∑ k ∈ range (d + 1), X j k N =
      X j0 d N + ∑ j, ∑ k ∈ range (d + 1), (if j = j0 ∧ k = d then 0 else X j k N) := by
    intro N
    have hpt : ∀ j k, X j k N =
        (if j = j0 ∧ k = d then X j k N else 0) + (if j = j0 ∧ k = d then 0 else X j k N) :=
      fun j k ↦ by split_ifs <;> simp
    conv_lhs => enter [2, j, 2, k]; rw [hpt j k]
    simp_rw [sum_add_distrib]
    congr 1
    simp_rw [ite_and]
    rw [Fintype.sum_eq_single j0 (fun j hj ↦ by simp [hj])]
    simp only [↓reduceIte]
    rw [sum_ite_eq' (range (d + 1)) d, ite_eq_left (mem_range.mpr (Nat.lt_succ_self d))]
  have hrest : ∀ N, 1 ≤ N →
      ‖∑ j, ∑ k ∈ range (d + 1), (if j = j0 ∧ k = d then 0 else X j k N)‖ ≤ K * (N : ℝ) ^ d := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [hKdef, sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
    rw [sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k hk ↦ ?_)
    have hkd : k ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hk)
    split_ifs with hjk
    · rw [norm_zero]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (hBj j)) (by positivity)
    · simp only [hXdef, norm_mul]
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      by_cases hj : j = j0
      · subst hj
        have hkd' : k < d := lt_of_le_of_ne hkd fun h ↦ hjk ⟨rfl, h⟩
        simp only [hBjdef, ite_eq_left rfl, one_mul, hTdef, hμ0, one_pow, mul_one]
        calc ‖∑ n ∈ range N, (n : ℂ) ^ k‖ ≤ ∑ n ∈ range N, (n : ℝ) ^ k := by
              refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ ↦ ?_))
              rw [norm_pow, Complex.norm_natCast]
          _ ≤ (N : ℝ) ^ (k + 1) := sum_pow_le_pow_succ k N
          _ ≤ (N : ℝ) ^ d := pow_le_pow_right₀ hN1 hkd'
      · simp only [hBjdef, ite_eq_right hj]
        calc ‖T (μ j) k N‖ ≤ 4 / ‖1 - μ j‖ * (N : ℝ) ^ k :=
              norm_sum_pow_mul_pow_le (hμnorm j) (hμne j hj) k N
          _ ≤ 4 / ‖1 - μ j‖ * (N : ℝ) ^ d :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 hkd) (by positivity)
  have heps : ∀ N, 1 ≤ N → ‖∑ n ∈ range N, ε n * ν ^ n‖ ≤ E * (N : ℝ) ^ d := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    calc ‖∑ n ∈ range N, ε n * ν ^ n‖ ≤ ∑ n ∈ range N, ‖ε n‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ ↦ ?_))
          rw [norm_mul, norm_pow, hνnorm, one_pow, mul_one]
      _ ≤ E := hε N
      _ ≤ E * (N : ℝ) ^ d := le_mul_of_one_le_right hE (one_le_pow₀ hN1)
  -- the top term grows like `M^{d+1}`
  have htop : ∀ M : ℕ, ‖c j0 d‖ * (M : ℝ) ^ (d + 1) ≤ ‖X j0 d (M + M)‖ := by
    intro M
    simp only [hXdef, hTdef, hμ0, one_pow, mul_one, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hreal : (∑ n ∈ range (M + M), (n : ℂ) ^ d) =
        ((∑ n ∈ range (M + M), (n : ℝ) ^ d : ℝ) : ℂ) := by push_cast; rfl
    rw [hreal, Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun n _ ↦ by positivity)]
    exact pow_succ_le_sum_pow d M
  -- combine for `N = 2M` with `M ≥ 1`
  set K' : ℝ := 3 ^ d * |C| + (K + E) * 2 ^ d with hK'def
  have hmain : ∀ M : ℕ, 1 ≤ M → ‖c j0 d‖ * (M : ℝ) ≤ K' := by
    intro M hM
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hMpos : (0 : ℝ) < M := by linarith
    have hN : 1 ≤ M + M := by omega
    have hsum_eq := hS (M + M)
    rw [hsplit] at hsum_eq
    have hXeq : X j0 d (M + M) = ∑ n ∈ range (M + M), (a n : ℂ) * ν ^ n -
        (∑ j, ∑ k ∈ range (d + 1), (if j = j0 ∧ k = d then 0 else X j k (M + M))) -
        ∑ n ∈ range (M + M), ε n * ν ^ n := by
      rw [hsum_eq]
      ring
    have hbound : ‖X j0 d (M + M)‖ ≤
        C * (((M + M : ℕ) : ℝ) + 1) ^ d + K * ((M + M : ℕ) : ℝ) ^ d + E * ((M + M : ℕ) : ℝ) ^ d := by
      rw [hXeq]
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add ((norm_sub_le _ _).trans (add_le_add (hup _) (hrest _ hN))) (heps _ hN)
    have h2M : ((M + M : ℕ) : ℝ) ^ d = 2 ^ d * (M : ℝ) ^ d := by
      push_cast
      rw [← two_mul, mul_pow]
    rw [h2M] at hbound
    have hC : C * (((M + M : ℕ) : ℝ) + 1) ^ d ≤ 3 ^ d * |C| * (M : ℝ) ^ d := by
      have h3 : ((M + M : ℕ) : ℝ) + 1 ≤ 3 * (M : ℝ) := by push_cast; linarith
      have h3' : (((M + M : ℕ) : ℝ) + 1) ^ d ≤ 3 ^ d * (M : ℝ) ^ d := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) h3 d
      calc C * (((M + M : ℕ) : ℝ) + 1) ^ d ≤ |C| * (((M + M : ℕ) : ℝ) + 1) ^ d :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * (3 ^ d * (M : ℝ) ^ d) := mul_le_mul_of_nonneg_left h3' (abs_nonneg C)
        _ = 3 ^ d * |C| * (M : ℝ) ^ d := by ring
    have hfinal : ‖c j0 d‖ * (M : ℝ) ^ (d + 1) ≤ K' * (M : ℝ) ^ d := by
      calc ‖c j0 d‖ * (M : ℝ) ^ (d + 1) ≤ ‖X j0 d (M + M)‖ := htop M
        _ ≤ 3 ^ d * |C| * (M : ℝ) ^ d + K * (2 ^ d * (M : ℝ) ^ d) + E * (2 ^ d * (M : ℝ) ^ d) := by
            linarith
        _ = K' * (M : ℝ) ^ d := by rw [hK'def]; ring
    have hMd : 0 < (M : ℝ) ^ d := pow_pos hMpos d
    rw [pow_succ, ← mul_assoc, mul_comm (‖c j0 d‖ * (M : ℝ) ^ d) (M : ℝ)] at hfinal
    have : (M : ℝ) * ‖c j0 d‖ * (M : ℝ) ^ d ≤ K' * (M : ℝ) ^ d := by linarith
    have := le_of_mul_le_mul_right this hMd
    linarith
  have hcpos : 0 < ‖c j0 d‖ := norm_pos_iff.mpr hj0
  obtain ⟨M, hM⟩ := exists_nat_gt (K' / ‖c j0 d‖)
  have hM1 : 1 ≤ M + 1 := Nat.le_add_left 1 M
  have h := hmain (M + 1) hM1
  have : K' < ‖c j0 d‖ * ((M + 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ hcpos] at hM
    push_cast
    nlinarith
  linarith

/-- The norms of a polynomial times a geometric sequence of ratio `< 1` are summable. -/
theorem summable_norm_poly_mul_pow {z : ℂ} (hz : ‖z‖ < 1) (p : ℂ[X]) :
    Summable fun n : ℕ ↦ ‖p.eval (n : ℂ) * z ^ n‖ := by
  set r := ‖z‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hg : Summable fun n : ℕ ↦
      ∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ * ((n : ℝ) ^ i * r ^ n) :=
    summable_sum fun i _ ↦ by
      have hr1 : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
      have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) i hr1
      exact this.mul_left ‖p.coeff i‖
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hg
  rw [eval_eq_sum_range, norm_mul, norm_pow]
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)).trans ?_
  rw [sum_mul]
  refine le_of_eq (sum_congr rfl fun i _ ↦ ?_)
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  ring

/-- Upper bound for partial sums of a nonnegative unit-circle power sum whose degree-`d` amplitude
at the root `1` vanishes. -/
theorem sum_le_of_unit_rep {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (lam : ι → ℂ) (hlam : ∀ j, ‖lam j‖ = 1) {d : ℕ} (c : ι → ℕ → ℂ)
    (htop : ∀ j, lam j = 1 → c j d = 0) (ε : ℕ → ℂ) {E : ℝ}
    (hε : ∀ N, ∑ n ∈ range N, ‖ε n‖ ≤ E)
    (hrep : ∀ n, (b n : ℂ) =
      ∑ j, ∑ k ∈ range (d + 1), c j k * (n : ℂ) ^ k * lam j ^ n + ε n) (N : ℕ) :
    ∑ n ∈ range N, b n ≤ (∑ j, ∑ k ∈ range (d + 1),
      ‖c j k‖ * (if lam j = 1 then 1 else 4 / ‖1 - lam j‖) + E) * ((N : ℝ) + 1) ^ d := by
  have hE : 0 ≤ E := by simpa using hε 0
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hpow : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ d := one_le_pow₀ hN1
  have hex : ∑ n ∈ range N, ∑ j, ∑ k ∈ range (d + 1), c j k * (n : ℂ) ^ k * lam j ^ n =
      ∑ j, ∑ k ∈ range (d + 1), c j k * ∑ n ∈ range N, (n : ℂ) ^ k * lam j ^ n := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_comm]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [mul_sum]
    exact sum_congr rfl fun n _ ↦ by ring
  have hterm : ∀ j, ∀ k ∈ range (d + 1),
      ‖c j k * ∑ n ∈ range N, (n : ℂ) ^ k * lam j ^ n‖ ≤
        ‖c j k‖ * (if lam j = 1 then 1 else 4 / ‖1 - lam j‖) * ((N : ℝ) + 1) ^ d := by
    intro j k hk
    have hkd : k ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hk)
    by_cases h1 : lam j = 1
    · rcases hkd.lt_or_eq with hlt | heq
      · rw [norm_mul, mul_assoc, ite_eq_left h1, one_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        simp only [h1, one_pow, mul_one]
        calc ‖∑ n ∈ range N, (n : ℂ) ^ k‖ ≤ ∑ n ∈ range N, (n : ℝ) ^ k := by
              refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ ↦ ?_))
              rw [norm_pow, Complex.norm_natCast]
          _ ≤ (N : ℝ) ^ (k + 1) := sum_pow_le_pow_succ k N
          _ ≤ ((N : ℝ) + 1) ^ (k + 1) :=
              pow_le_pow_left₀ (Nat.cast_nonneg N) (by linarith) _
          _ ≤ ((N : ℝ) + 1) ^ d := pow_le_pow_right₀ hN1 hlt
      · subst heq
        rw [htop j h1, zero_mul, norm_zero]
        positivity
    · rw [norm_mul, mul_assoc, ite_eq_right h1]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖∑ n ∈ range N, (n : ℂ) ^ k * lam j ^ n‖ ≤ 4 / ‖1 - lam j‖ * (N : ℝ) ^ k :=
            norm_sum_pow_mul_pow_le (hlam j) h1 k N
        _ ≤ 4 / ‖1 - lam j‖ * ((N : ℝ) + 1) ^ d := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc (N : ℝ) ^ k ≤ ((N : ℝ) + 1) ^ k :=
                  pow_le_pow_left₀ (Nat.cast_nonneg N) (by linarith) k
              _ ≤ ((N : ℝ) + 1) ^ d := pow_le_pow_right₀ hN1 hkd
  have hsumC : ∑ n ∈ range N, (b n : ℂ) =
      ∑ j, ∑ k ∈ range (d + 1), c j k * ∑ n ∈ range N, (n : ℂ) ^ k * lam j ^ n +
        ∑ n ∈ range N, ε n := by
    simp_rw [hrep]
    rw [sum_add_distrib, hex]
  have hnorm : ∑ n ∈ range N, b n = ‖∑ n ∈ range N, (b n : ℂ)‖ := by
    rw [← Complex.ofReal_sum, Complex.norm_real,
      Real.norm_of_nonneg (sum_nonneg fun n _ ↦ hb n)]
  rw [hnorm, hsumC]
  calc ‖∑ j, ∑ k ∈ range (d + 1), c j k * ∑ n ∈ range N, (n : ℂ) ^ k * lam j ^ n +
        ∑ n ∈ range N, ε n‖
      ≤ ∑ j, ∑ k ∈ range (d + 1),
          ‖c j k‖ * (if lam j = 1 then 1 else 4 / ‖1 - lam j‖) * ((N : ℝ) + 1) ^ d +
        E * ((N : ℝ) + 1) ^ d := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦
            (norm_sum_le _ _).trans (sum_le_sum (hterm j)))
        · exact (norm_sum_le _ _).trans ((hε N).trans (le_mul_of_one_le_right hE hpow))
    _ = (∑ j, ∑ k ∈ range (d + 1),
          ‖c j k‖ * (if lam j = 1 then 1 else 4 / ‖1 - lam j‖) + E) * ((N : ℝ) + 1) ^ d := by
        rw [add_mul, sum_mul]
        congr 1
        exact sum_congr rfl fun j _ ↦ by rw [sum_mul]

/-- **Pringsheim's theorem for nonnegative polynomial-exponential sums.**

Let `aₙ ≥ 0` equal `∑_{μ ∈ S} p_μ(n) μⁿ`.  Suppose no amplitude is nonzero beyond modulus
`R > 0`, and every amplitude on `|μ| = R` has degree `≤ d`.  If some `μ₀` on that circle has a
nonzero degree-`d` coefficient, then so does the real point `μ = R`. -/
theorem pringsheim_polyExp (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (S : Finset ℂ) (p : ℂ → ℂ[X])
    (hp : ∀ n, (a n : ℂ) = ∑ μ ∈ S, (p μ).eval (n : ℂ) * μ ^ n) {R : ℝ} (hR : 0 < R)
    (hbig : ∀ μ ∈ S, R < ‖μ‖ → p μ = 0) {d : ℕ}
    (hdeg : ∀ μ ∈ S, ‖μ‖ = R → ∀ k, d < k → (p μ).coeff k = 0) {μ0 : ℂ} (hμ0 : μ0 ∈ S)
    (hμ0R : ‖μ0‖ = R) (hμ0d : (p μ0).coeff d ≠ 0) :
    (R : ℂ) ∈ S ∧ (p R).coeff d ≠ 0 := by
  classical
  by_contra hcon
  have hR1 : (R : ℂ) ∈ S → (p R).coeff d = 0 := fun h ↦ by
    by_contra h'
    exact hcon ⟨h, h'⟩
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  set S' := insert (R : ℂ) S with hS'
  set p' : ℂ → ℂ[X] := fun μ ↦ if μ ∈ S then p μ else 0 with hp'def
  -- rescaled sequence and its representation over `S'`
  set b : ℕ → ℝ := fun n ↦ a n / R ^ n with hbdef
  have hb : ∀ n, 0 ≤ b n := fun n ↦ div_nonneg (ha n) (by positivity)
  have hpb : ∀ n, (b n : ℂ) = ∑ μ ∈ S', (p' μ).eval (n : ℂ) * (μ / R) ^ n := by
    intro n
    have h1 : ∑ μ ∈ S', (p' μ).eval (n : ℂ) * (μ / R) ^ n =
        ∑ μ ∈ S, (p μ).eval (n : ℂ) * (μ / R) ^ n := by
      symm
      rw [← sum_subset (subset_insert (R : ℂ) S) (fun μ _ hμ ↦ by simp [hp'def, hμ])]
      exact sum_congr rfl fun μ hμ ↦ by simp [hp'def, hμ]
    rw [h1]
    simp only [hbdef]
    push_cast
    rw [hp n, sum_div]
    refine sum_congr rfl fun μ _ ↦ ?_
    rw [div_pow]
    ring
  set U := S'.filter fun μ ↦ ‖μ‖ = R with hU
  set lam : U → ℂ := fun j ↦ j.1 / R with hlam
  set c : U → ℕ → ℂ := fun j k ↦ (p' j.1).coeff k with hc
  set D := S'.filter fun μ ↦ ¬ ‖μ‖ = R with hD
  set ε : ℕ → ℂ := fun n ↦ ∑ μ ∈ D, (p' μ).eval (n : ℂ) * (μ / R) ^ n with hε
  have hlamn : ∀ j, ‖lam j‖ = 1 := fun j ↦ by
    rw [hlam, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, (mem_filter.mp j.2).2,
      div_self hR.ne']
  have hinj : Function.Injective lam := fun i j hij ↦
    Subtype.ext ((div_left_inj' hRne).mp hij)
  have hdeg' : ∀ j : U, (p' j.1).natDegree < d + 1 := by
    intro j
    apply Nat.lt_succ_of_le
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    by_cases hjS : j.1 ∈ S
    · simp only [hp'def, ite_eq_left hjS]
      exact hdeg j.1 hjS (mem_filter.mp j.2).2 k hk
    · simp [hp'def, hjS]
  have hrep : ∀ n, (b n : ℂ) =
      ∑ j, ∑ k ∈ range (d + 1), c j k * (n : ℂ) ^ k * lam j ^ n + ε n := by
    intro n
    rw [hpb n, ← sum_filter_add_sum_filter_not S' (fun μ ↦ ‖μ‖ = R)]
    congr 1
    rw [← sum_coe_sort (S'.filter fun μ ↦ ‖μ‖ = R)]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [eval_eq_sum_range' (hdeg' j), sum_mul]
  -- the off-circle part is absolutely summable
  have hsummable : ∀ μ ∈ D, Summable fun n : ℕ ↦ ‖(p' μ).eval (n : ℂ) * (μ / R) ^ n‖ := by
    intro μ hμ
    obtain ⟨-, hμR⟩ := mem_filter.mp hμ
    by_cases hμS : μ ∈ S
    · rcases lt_or_gt_of_ne hμR with hlt | hgt
      · have hz : ‖μ / (R : ℂ)‖ < 1 := by
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_lt_one hR]
          exact hlt
        exact summable_norm_poly_mul_pow hz _
      · simp only [hp'def, ite_eq_left hμS, hbig μ hμS hgt, eval_zero, zero_mul, norm_zero]
        exact summable_zero
    · simp only [hp'def, ite_eq_right hμS, eval_zero, zero_mul, norm_zero]
      exact summable_zero
  set g : ℕ → ℝ := fun n ↦ ∑ μ ∈ D, ‖(p' μ).eval (n : ℂ) * (μ / R) ^ n‖ with hg
  have hgsum : Summable g := summable_sum hsummable
  have hεE : ∀ N, ∑ n ∈ range N, ‖ε n‖ ≤ ∑' n, g n := by
    intro N
    refine (sum_le_sum fun n _ ↦ norm_sum_le _ _).trans ?_
    exact hgsum.sum_le_tsum _ fun n _ ↦ sum_nonneg fun μ _ ↦ norm_nonneg _
  have htop : ∀ j, lam j = 1 → c j d = 0 := by
    intro j hj
    have hjR : j.1 = R := by
      have := (div_eq_one_iff_eq hRne).mp hj
      exact this
    simp only [hc, hp'def]
    split_ifs with hjS
    · rw [hjR]
      exact hR1 (hjR ▸ hjS)
    · simp
  have hsumb := sum_le_of_unit_rep b hb lam hlamn c htop ε hεE hrep
  have hμ0U : μ0 ∈ U := mem_filter.mpr ⟨mem_insert_of_mem hμ0, hμ0R⟩
  have := top_coeff_eq_zero_of_nonneg_growth b hb hsumb lam hlamn hinj c ε hεE hrep ⟨μ0, hμ0U⟩
  simp only [hc, hp'def, ite_eq_left hμ0] at this
  exact hμ0d this

/-- **Step W from the pole conditions.**

Let `aₙ ≥ 0` satisfy `χ(E) a = 0`, where `χ` is monic with `χ(0) ≠ 0`.  Suppose `χ` has no real
root `> 1` and `1` is at most a simple root.  Then `aₙ` is bounded.  (Poles of the generating
function are reciprocals of the roots of `χ`: this says there is no pole in `(0,1)` and at most a
simple pole at `1`.) -/
theorem bounded_of_nonneg_recurrence_pringsheim (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (χ : ℂ[X])
    (hmon : χ.Monic) (h0 : χ.coeff 0 ≠ 0)
    (hrec : ∀ n, ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * (a (n + i) : ℂ) = 0)
    (hreal : ∀ r : ℝ, 1 < r → χ.eval (r : ℂ) ≠ 0) (hsimple : χ.rootMultiplicity 1 ≤ 1) :
    ∃ B : ℝ, ∀ n, a n ≤ B := by
  classical
  obtain ⟨p, hpdeg, hp⟩ := isPolyExpMult_of_linearRecurrence χ hmon h0 (fun n ↦ (a n : ℂ)) hrec
  set S := χ.roots.toFinset with hS
  have hpS : ∀ n, (a n : ℂ) = ∑ μ ∈ S, (p μ).eval (n : ℂ) * μ ^ n := hp
  have hrootS : ∀ μ ∈ S, χ.eval μ = 0 := fun μ hμ ↦
    (mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp hμ)
  -- Claim 1: no nonzero amplitude outside the closed unit disk.
  have hout : ∀ μ ∈ S, 1 < ‖μ‖ → p μ = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨μa, hμaS, hμagt, hμane⟩ := hcon
    set T := S.filter fun μ ↦ 1 < ‖μ‖ ∧ p μ ≠ 0 with hT
    obtain ⟨μ1, hμ1T, hmax⟩ := T.exists_max_image (fun μ ↦ ‖μ‖)
      ⟨μa, mem_filter.mpr ⟨hμaS, hμagt, hμane⟩⟩
    obtain ⟨hμ1S, hμ1gt, hμ1ne⟩ := mem_filter.mp hμ1T
    set R := ‖μ1‖ with hR
    have hbig : ∀ μ ∈ S, R < ‖μ‖ → p μ = 0 := by
      intro μ hμ hlt
      by_contra hne
      linarith [hmax μ (mem_filter.mpr ⟨hμ, lt_trans hμ1gt hlt, hne⟩)]
    set V := T.filter fun μ ↦ ‖μ‖ = R with hV
    obtain ⟨μ0, hμ0V, hdmax⟩ := V.exists_max_image (fun μ ↦ (p μ).natDegree)
      ⟨μ1, mem_filter.mpr ⟨hμ1T, rfl⟩⟩
    obtain ⟨hμ0T, hμ0R⟩ := mem_filter.mp hμ0V
    obtain ⟨hμ0S, -, hμ0ne⟩ := mem_filter.mp hμ0T
    have hdeg : ∀ μ ∈ S, ‖μ‖ = R → ∀ k, (p μ0).natDegree < k → (p μ).coeff k = 0 := by
      intro μ hμ hμR k hk
      by_cases hpμ : p μ = 0
      · simp [hpμ]
      · have hμV : μ ∈ V := mem_filter.mpr ⟨mem_filter.mpr ⟨hμ, hμR ▸ hμ1gt, hpμ⟩, hμR⟩
        exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdmax μ hμV) hk)
    have hlead : (p μ0).coeff (p μ0).natDegree ≠ 0 := by
      rw [← leadingCoeff]
      exact leadingCoeff_ne_zero.mpr hμ0ne
    obtain ⟨hRS, -⟩ := pringsheim_polyExp a ha S p hpS (by linarith) hbig hdeg hμ0S hμ0R hlead
    exact hreal R hμ1gt (hrootS _ hRS)
  -- Claim 2: amplitudes on the unit circle are constant.
  have hcircle : ∀ μ ∈ S, ‖μ‖ = 1 → ∀ k, 1 ≤ k → (p μ).coeff k = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨μa, hμaS, hμa1, ka, hka, hcoef⟩ := hcon
    set V := S.filter fun μ ↦ ‖μ‖ = 1 ∧ p μ ≠ 0 with hV
    have hμane : p μa ≠ 0 := fun h ↦ hcoef (by simp [h])
    obtain ⟨μ0, hμ0V, hdmax⟩ := V.exists_max_image (fun μ ↦ (p μ).natDegree)
      ⟨μa, mem_filter.mpr ⟨hμaS, hμa1, hμane⟩⟩
    obtain ⟨hμ0S, hμ01, hμ0ne⟩ := mem_filter.mp hμ0V
    have hd1 : 1 ≤ (p μ0).natDegree :=
      hka.trans ((le_natDegree_of_ne_zero hcoef).trans
        (hdmax μa (mem_filter.mpr ⟨hμaS, hμa1, hμane⟩)))
    have hdeg : ∀ μ ∈ S, ‖μ‖ = (1 : ℝ) → ∀ k, (p μ0).natDegree < k → (p μ).coeff k = 0 := by
      intro μ hμ hμ1 k hk
      by_cases hpμ : p μ = 0
      · simp [hpμ]
      · exact coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (hdmax μ (mem_filter.mpr ⟨hμ, hμ1, hpμ⟩)) hk)
    have hlead : (p μ0).coeff (p μ0).natDegree ≠ 0 := by
      rw [← leadingCoeff]
      exact leadingCoeff_ne_zero.mpr hμ0ne
    obtain ⟨-, hcoef1⟩ := pringsheim_polyExp a ha S p hpS one_pos (fun μ hμ hlt ↦ hout μ hμ hlt)
      hdeg hμ0S hμ01 hlead
    rw [Complex.ofReal_one] at hcoef1
    apply hcoef1
    apply hpdeg
    rw [count_roots]
    exact hsimple.trans hd1
  -- Bound every term.
  have hbound : ∀ μ, ∃ B : ℝ, μ ∈ S → ∀ n : ℕ, ‖(p μ).eval (n : ℂ) * μ ^ n‖ ≤ B := by
    intro μ
    by_cases hμS : μ ∈ S
    · rcases lt_trichotomy ‖μ‖ 1 with hlt | heq | hgt
      · obtain ⟨B, hB⟩ := exists_bound_poly_mul_pow hlt (p μ)
        exact ⟨B, fun _ ↦ hB⟩
      · refine ⟨‖(p μ).coeff 0‖, fun _ n ↦ ?_⟩
        have hC : p μ = C ((p μ).coeff 0) := eq_C_of_natDegree_le_zero
          (natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ hcircle μ hμS heq k hk)
        rw [hC, eval_C, coeff_C_zero, norm_mul, norm_pow, heq, one_pow, mul_one]
      · exact ⟨0, fun _ n ↦ by simp [hout μ hμS hgt]⟩
    · exact ⟨0, fun h ↦ absurd h hμS⟩
  choose B hB using hbound
  refine ⟨∑ μ ∈ S, B μ, fun n ↦ ?_⟩
  have hnorm : a n = ‖(a n : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg (ha n)]
  rw [hnorm, hpS n]
  exact (norm_sum_le _ _).trans (sum_le_sum fun μ hμ ↦ hB μ hμ n)

end WeakTiling

end

end Pringsheim

/-! ## Step W from the pole conditions on `P(x, 1)` -/

section PoleConditions

section

open Polynomial Finset

namespace WeakTiling

/-- The normalized reversal of `Q` with trailing zeros removed:
`∑_{j ≤ m - t} (Q_{m-j} / Q_t) X^j`, where `m = deg Q` and `t` is the trailing degree. -/
noncomputable def recPoly (Q : ℂ[X]) : ℂ[X] :=
  ∑ j ∈ range (Q.natDegree - Q.natTrailingDegree + 1),
    C (Q.coeff (Q.natDegree - j) / Q.coeff Q.natTrailingDegree) * X ^ j

section

variable {Q : ℂ[X]}

theorem recPoly_coeff (Q : ℂ[X]) (j : ℕ) :
    (recPoly Q).coeff j = if j < Q.natDegree - Q.natTrailingDegree + 1 then
      Q.coeff (Q.natDegree - j) / Q.coeff Q.natTrailingDegree else 0 := by
  simp only [recPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [sum_ite_eq (range _) j (fun i ↦ Q.coeff (Q.natDegree - i) / Q.coeff Q.natTrailingDegree)]
  simp only [mem_range]

theorem trailing_coeff_ne_zero (hQ : Q ≠ 0) : Q.coeff Q.natTrailingDegree ≠ 0 :=
  fun h0 ↦ hQ (trailingCoeff_eq_zero.mp h0)

theorem recPoly_natDegree (hQ : Q ≠ 0) :
    (recPoly Q).natDegree = Q.natDegree - Q.natTrailingDegree := by
  have htm := natTrailingDegree_le_natDegree Q
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [recPoly_coeff, ite_eq_right (by omega)]
  · rw [recPoly_coeff, ite_eq_left (by omega), Nat.sub_sub_self htm, div_self (trailing_coeff_ne_zero hQ)]
    exact one_ne_zero

theorem recPoly_monic (hQ : Q ≠ 0) : (recPoly Q).Monic := by
  have htm := natTrailingDegree_le_natDegree Q
  rw [Monic, leadingCoeff, recPoly_natDegree hQ, recPoly_coeff, ite_eq_left (by omega),
    Nat.sub_sub_self htm, div_self (trailing_coeff_ne_zero hQ)]

theorem recPoly_coeff_zero_ne_zero (hQ : Q ≠ 0) : (recPoly Q).coeff 0 ≠ 0 := by
  rw [recPoly_coeff, ite_eq_left (Nat.succ_pos _), Nat.sub_zero]
  exact div_ne_zero (leadingCoeff_ne_zero.mpr hQ) (trailing_coeff_ne_zero hQ)

/-- Reflection of coefficient sums: `∑_{i ≤ m} Qᵢ g(m-i) = ∑_{j ≤ m-t} Q_{m-j} g(j)`. -/
theorem sum_coeff_reflect (Q : ℂ[X]) (g : ℕ → ℂ) :
    ∑ i ∈ range (Q.natDegree + 1), Q.coeff i * g (Q.natDegree - i) =
      ∑ j ∈ range (Q.natDegree - Q.natTrailingDegree + 1), Q.coeff (Q.natDegree - j) * g j := by
  set m := Q.natDegree
  set t := Q.natTrailingDegree
  rw [← sum_range_reflect _ (m + 1)]
  have h1 : ∑ j ∈ range (m + 1), Q.coeff (m + 1 - 1 - j) * g (m - (m + 1 - 1 - j)) =
      ∑ j ∈ range (m + 1), Q.coeff (m - j) * g j := by
    refine sum_congr rfl fun j hj ↦ ?_
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [show m + 1 - 1 - j = m - j by omega, show m - (m - j) = j by omega]
  rw [h1]
  symm
  apply sum_subset (range_subset_range.mpr (by omega))
  intro j hj hnj
  have : m - j < t := by
    simp only [mem_range] at hj hnj
    omega
  rw [coeff_eq_zero_of_lt_natTrailingDegree this, zero_mul]

/-- `recPoly Q (λ) = λ^m Q(1/λ) / q₀` for `λ ≠ 0`. -/
theorem recPoly_eval (Q : ℂ[X]) {l : ℂ} (hl : l ≠ 0) :
    (recPoly Q).eval l = l ^ Q.natDegree * Q.eval l⁻¹ / Q.coeff Q.natTrailingDegree := by
  set m := Q.natDegree
  set t := Q.natTrailingDegree
  rw [recPoly, eval_finsetSum, eval_eq_sum_range, mul_sum, sum_div]
  have h1 : ∑ i ∈ range (m + 1), l ^ m * (Q.coeff i * l⁻¹ ^ i) / Q.coeff t =
      ∑ i ∈ range (m + 1), Q.coeff i * (l ^ (m - i) / Q.coeff t) := by
    refine sum_congr rfl fun i hi ↦ ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [pow_sub₀ l hl him, inv_pow]
    ring
  rw [h1, sum_coeff_reflect Q (fun j ↦ l ^ j / Q.coeff t)]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- `(recPoly Q)'(1) = (m Q(1) - Q'(1)) / q₀`. -/
theorem recPoly_derivative_eval_one (hQ : Q ≠ 0) :
    (derivative (recPoly Q)).eval 1 =
      ((Q.natDegree : ℂ) * Q.eval 1 - (derivative Q).eval 1) / Q.coeff Q.natTrailingDegree := by
  set m := Q.natDegree
  set t := Q.natTrailingDegree
  have hderiv : ∀ p : ℂ[X], ∀ n, p.natDegree < n →
      (derivative p).eval 1 = ∑ i ∈ range n, p.coeff i * i := by
    intro p n hn
    rw [derivative_eval, sum_over_range' p (fun k ↦ by simp) n hn]
    simp
  have hχ := hderiv (recPoly Q) (m - t + 1) (by rw [recPoly_natDegree hQ]; omega)
  have hQd := hderiv Q (m + 1) (Nat.lt_succ_self m)
  rw [hχ, hQd, eval_eq_sum_range, mul_sum, ← sum_sub_distrib, sum_div]
  have h1 : ∑ i ∈ range (m + 1), ((m : ℂ) * (Q.coeff i * 1 ^ i) - Q.coeff i * i) /
      Q.coeff t = ∑ i ∈ range (m + 1), Q.coeff i * (((m - i : ℕ) : ℂ) / Q.coeff t) := by
    refine sum_congr rfl fun i hi ↦ ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [Nat.cast_sub him, one_pow]
    ring
  rw [h1, sum_coeff_reflect Q (fun j ↦ (j : ℂ) / Q.coeff t)]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [recPoly_coeff, ite_eq_left (mem_range.mp hj)]
  ring

/-- A zero of `Q` at `1` that is at most simple gives a root of multiplicity `≤ 1` of
`recPoly Q` at `1`. -/
theorem recPoly_rootMultiplicity_one_le (hQ : Q ≠ 0)
    (hsimple : Q.eval 1 = 0 → (derivative Q).eval 1 ≠ 0) :
    (recPoly Q).rootMultiplicity 1 ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨h0, h1⟩ := (one_lt_rootMultiplicity_iff_isRoot (recPoly_monic hQ).ne_zero).mp h
  have hq0 := trailing_coeff_ne_zero hQ
  have hQ1 : Q.eval 1 = 0 := by
    have := h0
    rw [IsRoot, recPoly_eval Q one_ne_zero, one_pow, inv_one, one_mul] at this
    exact (div_eq_zero_iff.mp this).resolve_right hq0
  have := h1
  rw [IsRoot, recPoly_derivative_eval_one hQ, hQ1, mul_zero, zero_sub, neg_div] at this
  exact hsimple hQ1 ((div_eq_zero_iff.mp (neg_eq_zero.mp this)).resolve_right hq0)

/-- No zero of `Q` in `(0,1)` gives no real root `> 1` of `recPoly Q`. -/
theorem recPoly_eval_ne_zero_of_gt_one (hQ : Q ≠ 0)
    (hzero : ∀ x : ℝ, 0 < x → x < 1 → Q.eval (x : ℂ) ≠ 0) (r : ℝ) (hr : 1 < r) :
    (recPoly Q).eval (r : ℂ) ≠ 0 := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  rw [recPoly_eval Q hr0]
  refine div_ne_zero (mul_ne_zero (pow_ne_zero _ hr0) ?_) (trailing_coeff_ne_zero hQ)
  have := hzero r⁻¹ (inv_pos.mpr (by linarith)) (inv_lt_one_of_one_lt₀ hr)
  rwa [Complex.ofReal_inv] at this

/-- The coefficient relation `Q · A = N` gives the recurrence of `recPoly Q` eventually. -/
theorem recPoly_recurrence (hQ : Q ≠ 0) (N : ℂ[X]) (A : ℕ → ℂ)
    (h : ∀ n, ∑ ij ∈ antidiagonal n, Q.coeff ij.1 * A ij.2 = N.coeff n) (k : ℕ)
    (hk : N.natDegree + 1 ≤ k) :
    ∑ i ∈ range ((recPoly Q).natDegree + 1), (recPoly Q).coeff i * A (k + i) = 0 := by
  set m := Q.natDegree
  set t := Q.natTrailingDegree
  have hNk : N.coeff (k + m) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hk' := h (k + m)
  rw [hNk, Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hk'
  have h1 : ∑ i ∈ range (k + m + 1), Q.coeff i * A (k + m - i) =
      ∑ i ∈ range (m + 1), Q.coeff i * A (k + (m - i)) := by
    symm
    rw [show ∑ i ∈ range (m + 1), Q.coeff i * A (k + (m - i)) =
        ∑ i ∈ range (m + 1), Q.coeff i * A (k + m - i) from
      sum_congr rfl fun i hi ↦ by
        have : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
        congr 2
        omega]
    apply sum_subset (range_subset_range.mpr (by omega))
    intro i hi hni
    have : m < i := by
      simp only [mem_range] at hi hni
      omega
    rw [coeff_eq_zero_of_natDegree_lt this, zero_mul]
  have hsum0 : ∑ j ∈ range (m - t + 1), Q.coeff (m - j) * A (k + j) = 0 := by
    rw [← sum_coeff_reflect Q (fun j ↦ A (k + j)), ← h1]
    exact hk'
  rw [recPoly_natDegree hQ]
  calc ∑ i ∈ range (m - t + 1), (recPoly Q).coeff i * A (k + i)
      = ∑ i ∈ range (m - t + 1), (1 / Q.coeff t) * (Q.coeff (m - i) * A (k + i)) := by
        refine sum_congr rfl fun i hi ↦ ?_
        rw [recPoly_coeff, ite_eq_left (mem_range.mp hi)]
        ring
    _ = 0 := by rw [← mul_sum, hsum0, mul_zero]

end

/-- Pringsheim form of step W, allowing the recurrence to start at `n₀`. -/
theorem bounded_of_nonneg_eventual_recurrence_pringsheim (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (χ : ℂ[X]) (hmon : χ.Monic) (h0 : χ.coeff 0 ≠ 0) (n₀ : ℕ)
    (hrec : ∀ n, n₀ ≤ n → ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * (a (n + i) : ℂ) = 0)
    (hreal : ∀ r : ℝ, 1 < r → χ.eval (r : ℂ) ≠ 0) (hsimple : χ.rootMultiplicity 1 ≤ 1) :
    ∃ B : ℝ, ∀ n, a n ≤ B := by
  set b : ℕ → ℝ := fun n ↦ a (n + n₀) with hb
  obtain ⟨B, hB⟩ := bounded_of_nonneg_recurrence_pringsheim b (fun n ↦ ha _) χ hmon h0
    (fun n ↦ by
      simp only [hb]
      have := hrec (n + n₀) (Nat.le_add_left n₀ n)
      rw [← this]
      refine sum_congr rfl fun i _ ↦ ?_
      congr 3
      ring) hreal hsimple
  refine ⟨max B (∑ m ∈ range n₀, a m), fun n ↦ ?_⟩
  by_cases hn : n₀ ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have := hB k
    simp only [hb, add_comm k n₀] at this
    exact this.trans (le_max_left _ _)
  · exact (single_le_sum (fun m _ ↦ ha m) (mem_range.mpr (not_le.mp hn))).trans
      (le_max_right _ _)

/-- **Step W from the pole conditions.**

Let `aₙ ≥ 0` satisfy the coefficient relation `Q · A = N` with `Q ≠ 0`.  Suppose `Q` has no zero
in `(0,1)` and at most a simple zero at `1`.  Then `aₙ` is bounded. -/
theorem bounded_of_rational_pole_conditions (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (Q N : ℂ[X])
    (hQ : Q ≠ 0) (hrel : ∀ n, ∑ ij ∈ antidiagonal n, Q.coeff ij.1 * (a ij.2 : ℂ) = N.coeff n)
    (hzero : ∀ x : ℝ, 0 < x → x < 1 → Q.eval (x : ℂ) ≠ 0)
    (hsimple : Q.eval 1 = 0 → (derivative Q).eval 1 ≠ 0) :
    ∃ B : ℝ, ∀ n, a n ≤ B :=
  bounded_of_nonneg_eventual_recurrence_pringsheim a ha (recPoly Q) (recPoly_monic hQ)
    (recPoly_coeff_zero_ne_zero hQ) (N.natDegree + 1)
    (fun n hn ↦ recPoly_recurrence hQ N (fun n ↦ (a n : ℂ)) hrel n hn)
    (recPoly_eval_ne_zero_of_gt_one hQ hzero) (recPoly_rootMultiplicity_one_le hQ hsimple)

end WeakTiling

end

end PoleConditions

/-! ## From finite Laurent rays to arithmetic-progression covers -/

section APCover

section

open MeasureTheory Set

namespace WeakTiling

/-- The one-sided arithmetic ray `c + hℕ`. -/
def arithmeticRay (c h : ℝ) : Set ℝ :=
  {y | ∃ n : ℕ, y = c + (n : ℝ) * h}

/-- A one-sided arithmetic ray is contained in the corresponding two-sided progression. -/
lemma arithmeticRay_subset_arithmeticProgression (c h : ℝ) :
    arithmeticRay c h ⊆ arithmeticProgression c h := by
  rintro y ⟨n, rfl⟩
  exact ⟨(n : ℤ), by simp⟩

/-- A finite family of positive-step arithmetic rays gives the strong progression-cover predicate. -/
theorem hasFiniteArithmeticProgressionCover_of_subset_finite_arithmeticRays
    (Λ E : Set ℝ) (hE : E.Finite)
    {ι : Type*} [Fintype ι] (c h : ι → ℝ) (hh : ∀ i, 0 < h i)
    (hΛ : Λ ⊆ E ∪ ⋃ i, arithmeticRay (c i) (h i)) :
    HasFiniteArithmeticProgressionCover Λ := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨E, Fintype.card ι, fun k ↦ c (e.symm k), fun k ↦ h (e.symm k), hE, ?_, ?_⟩
  · intro k
    exact hh (e.symm k)
  · intro x hx
    rcases hΛ hx with hxE | hxRay
    · exact Or.inl hxE
    · right
      rcases Set.mem_iUnion.mp hxRay with ⟨i, hi⟩
      apply Set.mem_iUnion.mpr
      refine ⟨e i, ?_⟩
      simpa using arithmeticRay_subset_arithmeticProgression (c i) (h i) hi

/-- The set of all exponent rays produced by finitely supported Laurent amplitudes and finitely
many positive monomial steps.  The dependent index allows each phase to have its own finite set of
offsets. -/
def laurentRaySupport {κ : Type*} [Fintype κ]
    (offsets : κ → Finset ℝ) (step : κ → ℝ) : Set ℝ :=
  ⋃ ju : Σ j, ↥(offsets j), arithmeticRay (ju.2 : ℝ) (step ju.1)

/-- The intermediate structural statement supplied by finite Laurent amplitudes and monomial
phases: apart from finitely many points, the support lies in finitely many families of exponent
rays with finitely many offsets. -/
def HasFiniteLaurentRayCover (Λ : Set ℝ) : Prop :=
  ∃ (E : Set ℝ) (n : ℕ) (offsets : Fin n → Finset ℝ) (step : Fin n → ℝ),
    E.Finite ∧ (∀ j, 0 < step j) ∧ Λ ⊆ E ∪ laurentRaySupport offsets step

/-- Finite Laurent support plus positive monomial steps yields a finite progression cover. -/
theorem hasFiniteArithmeticProgressionCover_of_subset_laurentRaySupport
    (Λ E : Set ℝ) (hE : E.Finite)
    {κ : Type*} [Fintype κ] (offsets : κ → Finset ℝ) (step : κ → ℝ)
    (hstep : ∀ j, 0 < step j)
    (hΛ : Λ ⊆ E ∪ laurentRaySupport offsets step) :
    HasFiniteArithmeticProgressionCover Λ := by
  apply hasFiniteArithmeticProgressionCover_of_subset_finite_arithmeticRays
    Λ E hE
    (fun ju : Σ j, ↥(offsets j) ↦ (ju.2 : ℝ))
    (fun ju : Σ j, ↥(offsets j) ↦ step ju.1)
    (fun ju ↦ hstep ju.1)
  simpa only [laurentRaySupport] using hΛ

/-- A finite Laurent-ray cover gives the progression-cover predicate used by the density layer. -/
theorem HasFiniteLaurentRayCover.hasFiniteArithmeticProgressionCover
    {Λ : Set ℝ} (hΛ : HasFiniteLaurentRayCover Λ) :
    HasFiniteArithmeticProgressionCover Λ := by
  obtain ⟨E, n, offsets, step, hE, hstep, hsub⟩ := hΛ
  exact hasFiniteArithmeticProgressionCover_of_subset_laurentRaySupport
    Λ E hE offsets step hstep hsub

/-- A finite Laurent-ray cover has bounded density. -/
theorem HasFiniteLaurentRayCover.hasBoundedDensity
    {Λ : Set ℝ} (hΛ : HasFiniteLaurentRayCover Λ) : HasBoundedDensity Λ :=
  hΛ.hasFiniteArithmeticProgressionCover.hasBoundedDensity

/-- Finite arithmetic-progression covers are stable under finite unions. -/
theorem HasFiniteArithmeticProgressionCover.mono
    {Λ Γ : Set ℝ} (hΛ : HasFiniteArithmeticProgressionCover Λ) (hΓ : Γ ⊆ Λ) :
    HasFiniteArithmeticProgressionCover Γ := by
  rcases hΛ with ⟨E, n, c, h, hE, hh, hsub⟩
  exact ⟨E, n, c, h, hE, hh, hΓ.trans hsub⟩

/-- Finite arithmetic-progression covers are stable under finite unions. -/
theorem HasFiniteArithmeticProgressionCover.union
    {Λ Γ : Set ℝ} (hΛ : HasFiniteArithmeticProgressionCover Λ)
    (hΓ : HasFiniteArithmeticProgressionCover Γ) :
    HasFiniteArithmeticProgressionCover (Λ ∪ Γ) := by
  classical
  obtain ⟨E, n, c, h, hE, hh, hΛsub⟩ := hΛ
  obtain ⟨F, m, d, k, hF, hk, hΓsub⟩ := hΓ
  let ι := Sum (Fin n) (Fin m)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨E ∪ F, Fintype.card ι, fun j ↦ Sum.elim c d (e.symm j),
    fun j ↦ Sum.elim h k (e.symm j), hE.union hF, ?_, ?_⟩
  · intro j
    change 0 < Sum.elim h k (e.symm j)
    cases hs : e.symm j with
    | inl i => change 0 < h i; exact hh i
    | inr i => change 0 < k i; exact hk i
  · intro x hx
    rcases hx with hx | hx
    · rcases hΛsub hx with he | hr
      · exact Or.inl (Or.inl he)
      · right
        rcases Set.mem_iUnion.mp hr with ⟨i, hi⟩
        rcases hi with ⟨z, hz⟩
        refine Set.mem_iUnion.mpr ⟨e (Sum.inl i), ⟨z, ?_⟩⟩
        simpa [ι, e.apply_symm_apply] using hz
    · rcases hΓsub hx with he | hr
      · exact Or.inl (Or.inr he)
      · right
        rcases Set.mem_iUnion.mp hr with ⟨i, hi⟩
        rcases hi with ⟨z, hz⟩
        refine Set.mem_iUnion.mpr ⟨e (Sum.inr i), ⟨z, ?_⟩⟩
        simpa [ι, e.apply_symm_apply] using hz

/-- Reflecting a set preserves finite arithmetic-progression covers; the step remains positive. -/
theorem HasFiniteArithmeticProgressionCover.neg
    {Λ : Set ℝ} (hΛ : HasFiniteArithmeticProgressionCover Λ) :
    HasFiniteArithmeticProgressionCover (Neg.neg '' Λ) := by
  classical
  obtain ⟨E, n, c, h, hE, hh, hΛsub⟩ := hΛ
  refine ⟨Neg.neg '' E, n, fun i ↦ -c i, h, hE.image _, hh, ?_⟩
  intro y hy
  change ∃ x, x ∈ Λ ∧ Neg.neg x = y at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rcases hΛsub hx with he | hr
  · exact Or.inl ⟨x, he, rfl⟩
  · right
    rcases Set.mem_iUnion.mp hr with ⟨i, hi⟩
    rcases hi with ⟨z, hz⟩
    refine Set.mem_iUnion.mpr ⟨i, ⟨-z, ?_⟩⟩
    rw [hz]
    simp
    ring

/-- Two one-sided Laurent-ray covers, one for each half of a set, give the correct two-sided
arithmetic-progression cover and hence bounded density. The negative half is reflected before its
ray representation is supplied. -/
theorem hasBoundedDensity_of_twoSidedLaurentRayCovers
    {Λ : Set ℝ}
    (hpos : HasFiniteLaurentRayCover {x | x ∈ Λ ∧ 0 ≤ x})
    (hneg : HasFiniteLaurentRayCover
      (Neg.neg '' {x | x ∈ Λ ∧ x < 0})) :
    HasBoundedDensity Λ := by
  let Pos : Set ℝ := {x | x ∈ Λ ∧ 0 ≤ x}
  let NegSide : Set ℝ := {x | x ∈ Λ ∧ x < 0}
  have hposAP : HasFiniteArithmeticProgressionCover Pos := by
    exact hpos.hasFiniteArithmeticProgressionCover
  have hnegAP : HasFiniteArithmeticProgressionCover NegSide := by
    have hdouble := hneg.hasFiniteArithmeticProgressionCover.neg
    have himage : Neg.neg '' (Neg.neg '' NegSide) = NegSide := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨-x, ⟨x, hx, rfl⟩, by simp⟩
    rw [himage] at hdouble
    exact hdouble
  have hcover : HasFiniteArithmeticProgressionCover (Pos ∪ NegSide) :=
    hposAP.union hnegAP
  apply (hcover.mono ?_).hasBoundedDensity
  intro x hx
  by_cases hnonneg : 0 ≤ x
  · exact Or.inl ⟨hx, hnonneg⟩
  · exact Or.inr ⟨hx, lt_of_not_ge hnonneg⟩

/-- Exact reduction of FC Problem 4.1 to the two one-sided structural statements. The positive
and reflected-negative supports may have different finite ray families. -/
theorem problem_4_1_of_twoSidedLaurentRayCovers
    (hcover : ∀ (Ω : Set ℝ), IsFiniteUnionOfIntervals Ω →
      ∀ (ν : Measure ℝ), IsWeakTilingMeasure Ω ν →
        HasFiniteLaurentRayCover {x | x ∈ ν.support ∧ 0 ≤ x} ∧
        HasFiniteLaurentRayCover (Neg.neg '' {x | x ∈ ν.support ∧ x < 0})) :
    ∀ (Ω : Set ℝ), IsFiniteUnionOfIntervals Ω →
      ∀ (ν : Measure ℝ), IsWeakTilingMeasure Ω ν →
        HasBoundedDensity ν.support := by
  intro Ω hΩ ν hν
  obtain ⟨hpos, hneg⟩ := hcover Ω hΩ ν hν
  exact hasBoundedDensity_of_twoSidedLaurentRayCovers hpos hneg

end WeakTiling

end

end APCover

/-! ## Van der Corput estimates for nonlinear phases -/

section Oscillatory

section

open Set Complex MeasureTheory

namespace WeakTiling

/-- First-derivative van der Corput test.

If `φ'` is monotone (encoded by `0 ≤ φ''`) and stays at least `λ` away from zero on `[a,b]`, the
oscillatory integral of `exp(iφ)` is bounded by `4 / λ`, independently of the interval length. -/
theorem norm_integral_exp_phase_le_of_abs_deriv_ge
    {φ φ' φ'' : ℝ → ℝ} {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hmono : ∀ t ∈ Icc a b, 0 ≤ φ'' t)
    (hlow : ∀ t ∈ Icc a b, lam ≤ |φ' t|) :
    ‖∫ t in a..b, exp ((φ t : ℂ) * I)‖ ≤ 4 / lam := by
  have hne : ∀ t ∈ Icc a b, φ' t ≠ 0 := fun t ht h => by
    have := hlow t ht
    rw [h, abs_zero] at this
    linarith
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hcI : ∀ t ∈ Icc a b, ((φ' t : ℂ) * I) ≠ 0 := fun t ht =>
    mul_ne_zero (ofReal_ne_zero.mpr (hne t ht)) I_ne_zero
  set u : ℝ → ℂ := fun t ↦ ((φ' t : ℂ) * I)⁻¹ with hu_def
  set u' : ℝ → ℂ := fun t ↦ -((φ'' t : ℂ) * I) / ((φ' t : ℂ) * I) ^ 2 with hu'_def
  set v : ℝ → ℂ := fun t ↦ exp ((φ t : ℂ) * I) with hv_def
  set v' : ℝ → ℂ := fun t ↦ exp ((φ t : ℂ) * I) * ((φ' t : ℂ) * I) with hv'_def
  have hu : ∀ t ∈ uIcc a b, HasDerivAt u (u' t) t := by
    intro t ht
    rw [huIcc] at ht
    have h1 : HasDerivAt (fun s ↦ (φ' s : ℂ) * I) ((φ'' t : ℂ) * I) t :=
      (hφ' t ht).ofReal_comp.mul_const I
    have h2 := (hasDerivAt_inv (hcI t ht)).comp t h1
    have e : u' t = -((((φ' t : ℂ) * I) ^ 2)⁻¹) * ((φ'' t : ℂ) * I) := by
      simp only [u']
      ring
    rw [e]
    exact h2
  have hv : ∀ t ∈ uIcc a b, HasDerivAt v (v' t) t := by
    intro t ht
    rw [huIcc] at ht
    have h1 : HasDerivAt (fun s ↦ (φ s : ℂ) * I) ((φ' t : ℂ) * I) t :=
      (hφ t ht).ofReal_comp.mul_const I
    exact h1.cexp
  have hφc : ContinuousOn φ (Icc a b) := fun t ht ↦
    (hφ t ht).continuousAt.continuousWithinAt
  have hφ'c : ContinuousOn φ' (Icc a b) := fun t ht ↦
    (hφ' t ht).continuousAt.continuousWithinAt
  have hu'c : ContinuousOn u' (Icc a b) := by
    apply ContinuousOn.div
    · exact ((continuous_ofReal.comp_continuousOn hφ''c).mul continuousOn_const).neg
    · exact ((continuous_ofReal.comp_continuousOn hφ'c).mul continuousOn_const).pow 2
    · intro t ht
      exact pow_ne_zero 2 (hcI t ht)
  have hv'c : ContinuousOn v' (Icc a b) := by
    apply ContinuousOn.mul
    · exact continuous_exp.comp_continuousOn
        ((continuous_ofReal.comp_continuousOn hφc).mul continuousOn_const)
    · exact (continuous_ofReal.comp_continuousOn hφ'c).mul continuousOn_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hu'c.intervalIntegrable_of_Icc hab) (hv'c.intervalIntegrable_of_Icc hab)
  have hint : (∫ t in a..b, exp ((φ t : ℂ) * I)) = ∫ t in a..b, u t * v' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [huIcc] at ht
    simp only [u, v']
    rw [mul_left_comm, inv_mul_cancel₀ (hcI t ht), mul_one]
  have hnorm : ∀ t ∈ Icc a b, ‖u' t * v t‖ = φ'' t / φ' t ^ 2 := by
    intro t ht
    simp only [u', v, norm_mul, norm_div, norm_neg, norm_pow, norm_exp_ofReal_mul_I, norm_I,
      Complex.norm_real, Real.norm_eq_abs, mul_one, sq_abs, abs_of_nonneg (hmono t ht)]
  have hftc : ∫ t in a..b, φ'' t / φ' t ^ 2 = (φ' a)⁻¹ - (φ' b)⁻¹ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := a) (b := b) (f := fun t ↦ -(φ' t)⁻¹) (f' := fun t ↦ φ'' t / φ' t ^ 2) ?_ ?_
    · rw [h]
      ring
    · intro t ht
      rw [huIcc] at ht
      have h2 : HasDerivAt (fun s ↦ -(φ' s)⁻¹) (-(-(φ'' t) / φ' t ^ 2)) t :=
        ((hφ' t ht).inv (hne t ht)).neg
      simpa only [neg_div, neg_neg] using h2
    · exact (hφ''c.div (hφ'c.pow 2) (fun t ht ↦ pow_ne_zero 2 (hne t ht))).intervalIntegrable_of_Icc
        hab
  have hend : ∀ t ∈ Icc a b, ‖u t * v t‖ ≤ lam⁻¹ := by
    intro t ht
    have h1 : ‖u t * v t‖ = |φ' t|⁻¹ := by
      simp only [u, v, norm_mul, norm_inv, norm_exp_ofReal_mul_I, norm_I, Complex.norm_real,
        Real.norm_eq_abs, mul_one]
    rw [h1]
    exact inv_anti₀ hlam (hlow t ht)
  have hinvle : ∀ t ∈ Icc a b, |(φ' t)⁻¹| ≤ lam⁻¹ := by
    intro t ht
    rw [abs_inv]
    exact inv_anti₀ hlam (hlow t ht)
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hrest : ‖∫ t in a..b, u' t * v t‖ ≤ 2 * lam⁻¹ := by
    calc ‖∫ t in a..b, u' t * v t‖ ≤ ∫ t in a..b, ‖u' t * v t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ t in a..b, φ'' t / φ' t ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [huIcc] at ht
          exact hnorm t ht
      _ = (φ' a)⁻¹ - (φ' b)⁻¹ := hftc
      _ ≤ |(φ' a)⁻¹| + |(φ' b)⁻¹| := by
          linarith [le_abs_self (φ' a)⁻¹, neg_abs_le (φ' b)⁻¹]
      _ ≤ 2 * lam⁻¹ := by linarith [hinvle a ha, hinvle b hb]
  rw [hint, hibp]
  calc ‖u b * v b - u a * v a - ∫ t in a..b, u' t * v t‖
      ≤ ‖u b * v b‖ + ‖u a * v a‖ + ‖∫ t in a..b, u' t * v t‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ lam⁻¹ + lam⁻¹ + 2 * lam⁻¹ := by
        gcongr
        · exact hend b hb
        · exact hend a ha
    _ = 4 / lam := by ring

/-- A continuous real phase gives an interval-integrable unit exponential. -/
theorem intervalIntegrable_exp_phase {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) :
    IntervalIntegrable (fun t ↦ exp ((φ t : ℂ) * I)) volume a b :=
  (continuous_exp.comp_continuousOn
    ((continuous_ofReal.comp_continuousOn hφ).mul continuousOn_const)).intervalIntegrable_of_Icc hab

/-- The trivial estimate: a unit exponential integrates to at most the interval length. -/
theorem norm_integral_exp_phase_le_length (φ : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ‖∫ t in a..b, exp ((φ t : ℂ) * I)‖ ≤ b - a := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
    (f := fun t ↦ exp ((φ t : ℂ) * I)) (fun t _ ↦ by simp [norm_exp_ofReal_mul_I])
  rwa [one_mul, abs_of_nonneg (sub_nonneg.mpr hab)] at h

/-- If `φ'' ≥ m`, then `φ'` grows at least linearly with slope `m`. -/
theorem deriv_add_mul_le_of_second_deriv_ge
    {φ' φ'' : ℝ → ℝ} {a b m : ℝ}
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hconv : ∀ t ∈ Icc a b, m ≤ φ'' t) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hxy : x ≤ y) : φ' x + m * (y - x) ≤ φ' y := by
  have hmono : MonotoneOn (fun t ↦ φ' t - m * t) (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (f' := fun t ↦ φ'' t - m) ?_ ?_ ?_
    · intro t ht
      exact ((hφ' t ht).continuousAt.sub
        (continuousAt_const.mul continuousAt_id)).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have h := (hφ' t (Ioo_subset_Icc_self ht)).sub ((hasDerivAt_id t).const_mul m)
      rw [mul_one] at h
      exact h.hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      linarith [hconv t (Ioo_subset_Icc_self ht)]
  have h := hmono hx hy hxy
  simp only at h
  linarith

/-- Second-derivative test on an interval where `φ'` starts nonnegative. -/
theorem norm_integral_exp_phase_le_of_second_deriv_ge_of_left_nonneg
    {φ φ' φ'' : ℝ → ℝ} {a b m δ : ℝ} (hab : a ≤ b) (hm : 0 < m) (hδ : 0 < δ)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hconv : ∀ t ∈ Icc a b, m ≤ φ'' t) (h0 : 0 ≤ φ' a) :
    ‖∫ t in a..b, exp ((φ t : ℂ) * I)‖ ≤ δ / m + 4 / δ := by
  have h4 : 0 < 4 / δ := by positivity
  by_cases hc : b ≤ a + δ / m
  · linarith [norm_integral_exp_phase_le_length φ hab]
  push Not at hc
  set c := a + δ / m with hc_def
  have hδm : 0 < δ / m := div_pos hδ hm
  have hac : a ≤ c := by linarith
  have hcb : c ≤ b := hc.le
  have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc hac le_rfl
  have hφc : ContinuousOn φ (Icc a b) := fun t ht ↦ (hφ t ht).continuousAt.continuousWithinAt
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_exp_phase hac (hφc.mono (Icc_subset_Icc le_rfl hcb)))
    (intervalIntegrable_exp_phase hcb (hφc.mono hsub))]
  have h1 : ‖∫ t in a..c, exp ((φ t : ℂ) * I)‖ ≤ δ / m := by
    have := norm_integral_exp_phase_le_length φ hac
    linarith
  have h2 : ‖∫ t in c..b, exp ((φ t : ℂ) * I)‖ ≤ 4 / δ := by
    refine norm_integral_exp_phase_le_of_abs_deriv_ge hcb hδ
      (fun t ht ↦ hφ t (hsub ht)) (fun t ht ↦ hφ' t (hsub ht)) (hφ''c.mono hsub)
      (fun t ht ↦ by linarith [hconv t (hsub ht)]) ?_
    intro t ht
    have hinc := deriv_add_mul_le_of_second_deriv_ge hφ' hconv
      (left_mem_Icc.mpr hab) (hsub ht) (by linarith [ht.1])
    have hmc : m * (c - a) = δ := by
      rw [hc_def, add_sub_cancel_left]
      field_simp
    have hle : m * (c - a) ≤ m * (t - a) :=
      mul_le_mul_of_nonneg_left (by linarith [ht.1]) hm.le
    exact le_abs.mpr (Or.inl (by linarith))
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- Second-derivative test on an interval where `φ'` ends nonpositive. -/
theorem norm_integral_exp_phase_le_of_second_deriv_ge_of_right_nonpos
    {φ φ' φ'' : ℝ → ℝ} {a b m δ : ℝ} (hab : a ≤ b) (hm : 0 < m) (hδ : 0 < δ)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hconv : ∀ t ∈ Icc a b, m ≤ φ'' t) (h0 : φ' b ≤ 0) :
    ‖∫ t in a..b, exp ((φ t : ℂ) * I)‖ ≤ δ / m + 4 / δ := by
  have h4 : 0 < 4 / δ := by positivity
  by_cases hc : b - δ / m ≤ a
  · linarith [norm_integral_exp_phase_le_length φ hab]
  push Not at hc
  set c := b - δ / m with hc_def
  have hδm : 0 < δ / m := div_pos hδ hm
  have hac : a ≤ c := hc.le
  have hcb : c ≤ b := by linarith
  have hsub : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcb
  have hφc : ContinuousOn φ (Icc a b) := fun t ht ↦ (hφ t ht).continuousAt.continuousWithinAt
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_exp_phase hac (hφc.mono hsub))
    (intervalIntegrable_exp_phase hcb (hφc.mono (Icc_subset_Icc hac le_rfl)))]
  have h1 : ‖∫ t in a..c, exp ((φ t : ℂ) * I)‖ ≤ 4 / δ := by
    refine norm_integral_exp_phase_le_of_abs_deriv_ge hac hδ
      (fun t ht ↦ hφ t (hsub ht)) (fun t ht ↦ hφ' t (hsub ht)) (hφ''c.mono hsub)
      (fun t ht ↦ by linarith [hconv t (hsub ht)]) ?_
    intro t ht
    have hinc := deriv_add_mul_le_of_second_deriv_ge hφ' hconv
      (hsub ht) (right_mem_Icc.mpr hab) (by linarith [ht.2])
    have hmc : m * (b - c) = δ := by
      rw [hc_def, sub_sub_cancel]
      field_simp
    have hle : m * (b - c) ≤ m * (b - t) :=
      mul_le_mul_of_nonneg_left (by linarith [ht.2]) hm.le
    exact le_abs.mpr (Or.inr (by linarith))
  have h2 : ‖∫ t in c..b, exp ((φ t : ℂ) * I)‖ ≤ δ / m := by
    have := norm_integral_exp_phase_le_length φ hcb
    linarith
  linarith [norm_add_le (∫ t in a..c, exp ((φ t : ℂ) * I)) (∫ t in c..b, exp ((φ t : ℂ) * I))]

/-- Second-derivative test with a free splitting parameter `δ`. -/
theorem norm_integral_exp_phase_le_of_second_deriv_ge_aux
    {φ φ' φ'' : ℝ → ℝ} {a b m δ : ℝ} (hab : a ≤ b) (hm : 0 < m) (hδ : 0 < δ)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hconv : ∀ t ∈ Icc a b, m ≤ φ'' t) :
    ‖∫ t in a..b, exp ((φ t : ℂ) * I)‖ ≤ 2 * (δ / m + 4 / δ) := by
  have hpos : 0 ≤ δ / m + 4 / δ := by positivity
  by_cases ha : 0 ≤ φ' a
  · linarith [norm_integral_exp_phase_le_of_second_deriv_ge_of_left_nonneg hab hm hδ
      hφ hφ' hφ''c hconv ha]
  by_cases hb : φ' b ≤ 0
  · linarith [norm_integral_exp_phase_le_of_second_deriv_ge_of_right_nonpos hab hm hδ
      hφ hφ' hφ''c hconv hb]
  push Not at ha hb
  have hφ'c : ContinuousOn φ' (Icc a b) := fun t ht ↦
    (hφ' t ht).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab hφ'c ⟨ha.le, hb.le⟩
  have hac : a ≤ c := hc.1
  have hcb : c ≤ b := hc.2
  have hsubL : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcb
  have hsubR : Icc c b ⊆ Icc a b := Icc_subset_Icc hac le_rfl
  have hφc : ContinuousOn φ (Icc a b) := fun t ht ↦ (hφ t ht).continuousAt.continuousWithinAt
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_exp_phase hac (hφc.mono hsubL))
    (intervalIntegrable_exp_phase hcb (hφc.mono hsubR))]
  have h1 := norm_integral_exp_phase_le_of_second_deriv_ge_of_right_nonpos hac hm hδ
    (fun t ht ↦ hφ t (hsubL ht)) (fun t ht ↦ hφ' t (hsubL ht)) (hφ''c.mono hsubL)
    (fun t ht ↦ hconv t (hsubL ht)) hc0.le
  have h2 := norm_integral_exp_phase_le_of_second_deriv_ge_of_left_nonneg hcb hm hδ
    (fun t ht ↦ hφ t (hsubR ht)) (fun t ht ↦ hφ' t (hsubR ht)) (hφ''c.mono hsubR)
    (fun t ht ↦ hconv t (hsubR ht)) hc0.ge
  linarith [norm_add_le (∫ t in a..c, exp ((φ t : ℂ) * I)) (∫ t in c..b, exp ((φ t : ℂ) * I))]

/-- **Second-derivative van der Corput test.**

If `φ'' ≥ m > 0` on `[a,b]`, then `‖∫ exp(iφ)‖ ≤ 8 / √m`, independently of the interval length
and of the first derivative of `φ`. -/
theorem norm_integral_exp_phase_le_of_second_deriv_ge
    {φ φ' φ'' : ℝ → ℝ} {a b m : ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hconv : ∀ t ∈ Icc a b, m ≤ φ'' t) :
    ‖∫ t in a..b, exp ((φ t : ℂ) * I)‖ ≤ 8 / Real.sqrt m := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsq : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
  have h := norm_integral_exp_phase_le_of_second_deriv_ge_aux (δ := 2 * Real.sqrt m) hab hm
    (by positivity) hφ hφ' hφ''c hconv
  have heq : 2 * (2 * Real.sqrt m / m + 4 / (2 * Real.sqrt m)) = 8 / Real.sqrt m := by
    field_simp
    rw [hsq]
    ring
  rwa [heq] at h

/-- Reversing the phase conjugates the oscillatory integral. -/
theorem integral_exp_neg_phase_eq_conj (φ : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, exp (((-φ t : ℝ) : ℂ) * I)) =
      (starRingEnd ℂ) (∫ t in a..b, exp ((φ t : ℂ) * I)) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, ← integral_conj]
  congr 1
  ext t
  rw [← exp_conj, map_mul, conj_ofReal, conj_I]
  push_cast
  ring_nf

/-- Second-derivative test for a phase with `φ'' ≤ -m < 0`. -/
theorem norm_integral_exp_phase_le_of_second_deriv_le_neg
    {φ φ' φ'' : ℝ → ℝ} {a b m : ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hconc : ∀ t ∈ Icc a b, φ'' t ≤ -m) :
    ‖∫ t in a..b, exp ((φ t : ℂ) * I)‖ ≤ 8 / Real.sqrt m := by
  have h := norm_integral_exp_phase_le_of_second_deriv_ge (φ := fun t ↦ -φ t)
    (φ' := fun t ↦ -φ' t) (φ'' := fun t ↦ -φ'' t) hab hm
    (fun t ht ↦ (hφ t ht).neg) (fun t ht ↦ (hφ' t ht).neg) hφ''c.neg
    (fun t ht ↦ by linarith [hconc t ht])
  rwa [integral_exp_neg_phase_eq_conj φ hab, Complex.norm_conj] at h

/-- **Second-derivative van der Corput test, either sign of curvature.**

A continuous second derivative with `|φ''| ≥ m > 0` cannot change sign, so the bound `8 / √m`
holds for convex and concave phases alike. -/
theorem norm_integral_exp_phase_le_of_abs_second_deriv_ge
    {φ φ' φ'' : ℝ → ℝ} {a b m : ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hcurv : ∀ t ∈ Icc a b, m ≤ |φ'' t|) :
    ‖∫ t in a..b, exp ((φ t : ℂ) * I)‖ ≤ 8 / Real.sqrt m := by
  have hne : ∀ t ∈ Icc a b, φ'' t ≠ 0 := fun t ht h ↦ by
    have := hcurv t ht
    rw [h, abs_zero] at this
    linarith
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  rcases le_or_gt 0 (φ'' a) with hpos | hneg
  · refine norm_integral_exp_phase_le_of_second_deriv_ge hab hm hφ hφ' hφ''c ?_
    intro t ht
    rcases le_abs'.mp (hcurv t ht) with h | h
    · exfalso
      have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht.1 (hφ''c.mono hsub)
        ⟨by linarith, hpos⟩
      exact hne s (hsub hs) hs0
    · exact h
  · refine norm_integral_exp_phase_le_of_second_deriv_le_neg hab hm hφ hφ' hφ''c ?_
    intro t ht
    rcases le_abs'.mp (hcurv t ht) with h | h
    · linarith
    · exfalso
      have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht.1 (hφ''c.mono hsub)
        ⟨hneg.le, by linarith⟩
      exact hne s (hsub hs) hs0

/-- **Second-derivative test with a smooth amplitude.**

Summation by parts against `F(x) = ∫_a^x exp(iφ)` transfers the uniform bound on every partial
integral to an amplitude `ψ` with integrable derivative.  The constant is explicit:
`(‖ψ b‖ + ∫ ‖ψ'‖) · 8 / √m`.  For a cutoff vanishing at `b`, only the variation of `ψ` enters. -/
theorem norm_integral_amplitude_mul_exp_phase_le
    {φ φ' φ'' : ℝ → ℝ} {ψ ψ' : ℝ → ℂ} {a b m : ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hcurv : ∀ t ∈ Icc a b, m ≤ |φ'' t|)
    (hψ : ∀ t ∈ Icc a b, HasDerivAt ψ (ψ' t) t)
    (hψ'c : ContinuousOn ψ' (Icc a b)) :
    ‖∫ t in a..b, ψ t * exp ((φ t : ℂ) * I)‖ ≤
      (‖ψ b‖ + ∫ t in a..b, ‖ψ' t‖) * (8 / Real.sqrt m) := by
  set C : ℝ := 8 / Real.sqrt m with hC_def
  have hC : 0 ≤ C := by positivity
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  set g : ℝ → ℂ := fun t ↦ exp ((φ t : ℂ) * I) with hg_def
  set F : ℝ → ℂ := fun x ↦ ∫ t in a..x, g t with hF_def
  have hφc : ContinuousOn φ (Icc a b) := fun t ht ↦ (hφ t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) :=
    continuous_exp.comp_continuousOn
      ((continuous_ofReal.comp_continuousOn hφc).mul continuousOn_const)
  have hF : ∀ x ∈ uIcc a b, HasDerivWithinAt F (g x) (uIcc a b) x := by
    intro x hx
    rw [huIcc] at hx ⊢
    have := Fact.mk hx
    apply intervalIntegral.integral_hasDerivWithinAt_right
    · exact (hgc.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1
    · exact hgc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x
    · exact hgc.continuousWithinAt hx
  have hψw : ∀ x ∈ uIcc a b, HasDerivWithinAt ψ (ψ' x) (uIcc a b) x := fun x hx ↦
    (hψ x (huIcc ▸ hx)).hasDerivWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt hψw hF
    (hψ'c.intervalIntegrable_of_Icc hab) (hgc.intervalIntegrable_of_Icc hab)
  have hFa : F a = 0 := intervalIntegral.integral_same
  have hFbound : ∀ x ∈ Icc a b, ‖F x‖ ≤ C := by
    intro x hx
    have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
    exact norm_integral_exp_phase_le_of_abs_second_deriv_ge hx.1 hm
      (fun t ht ↦ hφ t (hsub ht)) (fun t ht ↦ hφ' t (hsub ht)) (hφ''c.mono hsub)
      (fun t ht ↦ hcurv t (hsub ht))
  have hFc : ContinuousOn F (Icc a b) := fun x hx ↦
    (hF x (huIcc ▸ hx)).continuousWithinAt.mono_of_mem_nhdsWithin
      (by rw [huIcc]; exact self_mem_nhdsWithin)
  have hrest : ‖∫ t in a..b, ψ' t * F t‖ ≤ (∫ t in a..b, ‖ψ' t‖) * C := by
    calc ‖∫ t in a..b, ψ' t * F t‖ ≤ ∫ t in a..b, ‖ψ' t * F t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ t in a..b, ‖ψ' t‖ * C := by
          apply intervalIntegral.integral_mono_on hab
          · exact (hψ'c.mul hFc).norm.intervalIntegrable_of_Icc hab
          · exact (hψ'c.norm.mul continuousOn_const).intervalIntegrable_of_Icc hab
          · intro t ht
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hFbound t ht) (norm_nonneg _)
      _ = (∫ t in a..b, ‖ψ' t‖) * C := intervalIntegral.integral_mul_const C _
  have hb : ‖ψ b * F b‖ ≤ ‖ψ b‖ * C := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hFbound b (right_mem_Icc.mpr hab)) (norm_nonneg _)
  rw [hibp, hFa, mul_zero, sub_zero]
  calc ‖ψ b * F b - ∫ t in a..b, ψ' t * F t‖
      ≤ ‖ψ b * F b‖ + ‖∫ t in a..b, ψ' t * F t‖ := norm_sub_le _ _
    _ ≤ ‖ψ b‖ * C + (∫ t in a..b, ‖ψ' t‖) * C := add_le_add hb hrest
    _ = (‖ψ b‖ + ∫ t in a..b, ‖ψ' t‖) * C := by ring

end WeakTiling

end

end Oscillatory

/-! ## One-variable phase rigidity -/

section PhaseRigidity

section

open Set Complex MeasureTheory Filter Topology

namespace WeakTiling

/-- The localized wave `ψ(t) exp(i n φ(t))`. -/
noncomputable def curvedWave (ψ : ℝ → ℂ) (φ : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ψ t * exp ((((n : ℝ) * φ t : ℝ) : ℂ) * I)

/-- For nonnegative `f` bounded by `s`, `∑ f² ≤ s ∑ f`. -/
theorem tsum_sq_le_mul_tsum {f : ℤ → ℝ} (hf0 : ∀ k, 0 ≤ f k) {s : ℝ} (hs : ∀ k, f k ≤ s)
    (hsum : Summable f) : ∑' k, f k ^ 2 ≤ s * ∑' k, f k := by
  have hpt : ∀ k, f k ^ 2 ≤ s * f k := fun k ↦ by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hs k) (hf0 k)
  have hsum' : Summable fun k ↦ s * f k := hsum.mul_left s
  have hsq : Summable fun k ↦ f k ^ 2 :=
    Summable.of_nonneg_of_le (fun k ↦ sq_nonneg _) hpt hsum'
  rw [← tsum_mul_left]
  exact hsq.tsum_le_tsum hpt hsum'

section

variable {p q a b m : ℝ} {φ φ' φ'' : ℝ → ℝ} {ψ ψ' : ℝ → ℂ}

/-- An amplitude that is differentiable on `[a,b]` and vanishes off `(a,b)` is continuous. -/
theorem continuous_of_supported
    (hψ : ∀ t ∈ Icc a b, HasDerivAt ψ (ψ' t) t) (hsupp : ∀ t, t ∉ Ioo a b → ψ t = 0) :
    Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Icc a b
  · exact (hψ x hx).continuousAt
  · have hev : ψ =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
      exact hsupp y fun h ↦ hy (Ioo_subset_Icc_self h)
    exact continuousAt_const.congr hev.symm

/-- The localized wave is continuous. -/
theorem continuous_curvedWave
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hψ : ∀ t ∈ Icc a b, HasDerivAt ψ (ψ' t) t) (hsupp : ∀ t, t ∉ Ioo a b → ψ t = 0)
    (n : ℕ) : Continuous (curvedWave ψ φ n) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Icc a b
  · exact (hψ x hx).continuousAt.mul
      (continuous_exp.continuousAt.comp
        ((continuous_ofReal.continuousAt.comp
          (continuousAt_const.mul (hφ x hx).continuousAt)).mul continuousAt_const))
  · have hev : curvedWave ψ φ n =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
      simp [curvedWave, hsupp y fun h ↦ hy (Ioo_subset_Icc_self h)]
    exact continuousAt_const.congr hev.symm

/-- **Frequency-uniform Fourier decay of a curved wave.**

Every Fourier coefficient of `ψ exp(i n φ)` on the circle `[p,q]` is at most `K / √n`, where
`K = (q-p)⁻¹ (∫ₐᵇ ‖ψ'‖) 8 / √m` does not depend on `n` or on the frequency. -/
theorem norm_fourierCoeffOn_curvedWave_le
    (hpq : p < q) (hpa : p ≤ a) (hab : a ≤ b) (hbq : b ≤ q) (hm : 0 < m)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hcurv : ∀ t ∈ Icc a b, m ≤ |φ'' t|)
    (hψ : ∀ t ∈ Icc a b, HasDerivAt ψ (ψ' t) t)
    (hψ'c : ContinuousOn ψ' (Icc a b))
    (hsupp : ∀ t, t ∉ Ioo a b → ψ t = 0)
    {n : ℕ} (hn : 0 < n) (k : ℤ) :
    ‖fourierCoeffOn hpq (curvedWave ψ φ n) k‖ ≤
      (q - p)⁻¹ * ((∫ t in a..b, ‖ψ' t‖) * (8 / Real.sqrt m)) / Real.sqrt n := by
  have hT : 0 < q - p := sub_pos.mpr hpq
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set κ : ℝ := 2 * Real.pi * k / (q - p) with hκ
  set H : ℝ → ℂ := fun x ↦ ψ x * exp ((((n : ℝ) * φ x - κ * x : ℝ) : ℂ) * I) with hH
  have hpt : ∀ x : ℝ,
      fourier (-k) (x : AddCircle (q - p)) • curvedWave ψ φ n x = H x := by
    intro x
    rw [fourier_coe_apply, smul_eq_mul, curvedWave, mul_left_comm, ← exp_add]
    simp only [H, hκ]
    congr 2
    push_cast
    field_simp
    ring
  have hzero : ∀ x, x ∉ Ioo a b → H x = 0 := fun x hx ↦ by simp [H, hsupp x hx]
  have hψc := continuous_of_supported hψ hsupp
  have hφc : ContinuousOn φ (Icc a b) := fun t ht ↦ (hφ t ht).continuousAt.continuousWithinAt
  have hHc : ContinuousOn H (Icc a b) :=
    hψc.continuousOn.mul (continuous_exp.comp_continuousOn
      ((continuous_ofReal.comp_continuousOn
        ((continuousOn_const.mul hφc).sub (continuousOn_const.mul continuousOn_id))).mul
          continuousOn_const))
  have hleft : EqOn H (fun _ ↦ 0) (Icc p a) := fun x hx ↦ hzero x fun h ↦ by
    linarith [hx.2, h.1]
  have hright : EqOn H (fun _ ↦ 0) (Icc b q) := fun x hx ↦ hzero x fun h ↦ by
    linarith [hx.1, h.2]
  have hIpa : IntervalIntegrable H volume p a :=
    (continuousOn_const.congr hleft).intervalIntegrable_of_Icc hpa
  have hIab : IntervalIntegrable H volume a b := hHc.intervalIntegrable_of_Icc hab
  have hIbq : IntervalIntegrable H volume b q :=
    (continuousOn_const.congr hright).intervalIntegrable_of_Icc hbq
  have hpa0 : ∫ x in p..a, H x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℂ)) (by
      rw [uIcc_of_le hpa]; exact hleft)]
    simp
  have hbq0 : ∫ x in b..q, H x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℂ)) (by
      rw [uIcc_of_le hbq]; exact hright)]
    simp
  have hsplit : ∫ x in p..q, H x = ∫ x in a..b, H x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hIpa (hIab.trans hIbq),
      ← intervalIntegral.integral_add_adjacent_intervals hIab hIbq, hpa0, hbq0]
    ring
  have hvdc := norm_integral_amplitude_mul_exp_phase_le
    (φ := fun t ↦ (n : ℝ) * φ t - κ * t) (φ' := fun t ↦ (n : ℝ) * φ' t - κ)
    (φ'' := fun t ↦ (n : ℝ) * φ'' t) (m := n * m) hab (mul_pos hN hm)
    (fun t ht ↦ by
      have h := ((hφ t ht).const_mul (n : ℝ)).sub ((hasDerivAt_id' t).const_mul κ)
      rwa [mul_one] at h)
    (fun t ht ↦ ((hφ' t ht).const_mul (n : ℝ)).sub_const κ)
    (continuousOn_const.mul hφ''c)
    (fun t ht ↦ by
      rw [abs_mul, abs_of_pos hN]
      exact mul_le_mul_of_nonneg_left (hcurv t ht) hN.le)
    hψ hψ'c
  have hψb : ψ b = 0 := hsupp b fun h ↦ lt_irrefl b h.2
  rw [hψb, norm_zero, zero_add] at hvdc
  rw [fourierCoeffOn_eq_integral _ _ hpq]
  simp_rw [hpt]
  rw [hsplit, norm_smul, norm_div, norm_one, Real.norm_eq_abs, abs_of_pos hT, one_div]
  have hsq : Real.sqrt ((n : ℝ) * m) = Real.sqrt n * Real.sqrt m :=
    Real.sqrt_mul hN.le m
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hN
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have heq : (∫ t in a..b, ‖ψ' t‖) * (8 / Real.sqrt (n * m)) =
      (∫ t in a..b, ‖ψ' t‖) * (8 / Real.sqrt m) / Real.sqrt n := by
    rw [hsq]
    field_simp
  rw [heq] at hvdc
  calc (q - p)⁻¹ * ‖∫ x in a..b, H x‖
      ≤ (q - p)⁻¹ * ((∫ t in a..b, ‖ψ' t‖) * (8 / Real.sqrt m) / Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hvdc (inv_nonneg.mpr hT.le)
    _ = (q - p)⁻¹ * ((∫ t in a..b, ‖ψ' t‖) * (8 / Real.sqrt m)) / Real.sqrt n := by ring

/-- **Parseval for a curved wave.**  The `ℓ²` mass of the Fourier coefficients of
`ψ exp(i n φ)` does not depend on `n`. -/
theorem hasSum_sq_fourierCoeffOn_curvedWave
    (hpq : p < q)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hψ : ∀ t ∈ Icc a b, HasDerivAt ψ (ψ' t) t) (hsupp : ∀ t, t ∉ Ioo a b → ψ t = 0)
    (n : ℕ) :
    HasSum (fun k ↦ ‖fourierCoeffOn hpq (curvedWave ψ φ n) k‖ ^ 2)
      ((q - p)⁻¹ * ∫ x in p..q, ‖ψ x‖ ^ 2) := by
  have hGc := continuous_curvedWave hφ hψ hsupp n
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := p) (b := q)).exists_bound_of_continuousOn
    hGc.continuousOn
  have hL2 : MemLp (curvedWave ψ φ n) 2 (volume.restrict (Ioc p q)) := by
    refine MemLp.of_bound hGc.aestronglyMeasurable C ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Eventually.of_forall fun x hx ↦ hC x (Ioc_subset_Icc_self hx))
  have h := hasSum_sq_fourierCoeffOn hpq hL2
  have hnorm : ∀ x, ‖curvedWave ψ φ n x‖ = ‖ψ x‖ := fun x ↦ by
    rw [curvedWave, norm_mul, norm_exp_ofReal_mul_I, mul_one]
  simp_rw [hnorm, smul_eq_mul] at h
  exact h

/-- **One-variable phase rigidity.**

If `ψ` is a nonzero `C¹` amplitude supported in `(a,b) ⊆ [p,q]` and `φ` has `|φ''| ≥ m > 0` on
`[a,b]`, then the Wiener norms `∑ₖ |ĝₙ(k)|` of `gₙ = ψ exp(i n φ)` on the circle `[p,q]` are not
uniformly bounded for all sufficiently large `n`.  This is the contradiction used to show that the surviving
characteristic phases are linear. -/
theorem not_bounded_wienerNorm_curvedWave
    (hpq : p < q) (hpa : p ≤ a) (hab : a ≤ b) (hbq : b ≤ q) (hm : 0 < m)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hcurv : ∀ t ∈ Icc a b, m ≤ |φ'' t|)
    (hψ : ∀ t ∈ Icc a b, HasDerivAt ψ (ψ' t) t)
    (hψ'c : ContinuousOn ψ' (Icc a b))
    (hsupp : ∀ t, t ∉ Ioo a b → ψ t = 0)
    (hψne : 0 < ∫ x in p..q, ‖ψ x‖ ^ 2) :
    ¬ ∃ (M : ℝ) (n₀ : ℕ), ∀ n : ℕ, n₀ ≤ n →
      Summable (fun k ↦ ‖fourierCoeffOn hpq (curvedWave ψ φ n) k‖) ∧
        ∑' k, ‖fourierCoeffOn hpq (curvedWave ψ φ n) k‖ ≤ M := by
  rintro ⟨M, n₀, hM⟩
  have hT : 0 < q - p := sub_pos.mpr hpq
  set K : ℝ := (q - p)⁻¹ * ((∫ t in a..b, ‖ψ' t‖) * (8 / Real.sqrt m)) with hK
  set c : ℝ := (q - p)⁻¹ * ∫ x in p..q, ‖ψ x‖ ^ 2 with hc
  have hcpos : 0 < c := mul_pos (inv_pos.mpr hT) hψne
  -- For every `n ≥ 1`, Parseval and the uniform decay give `c √n ≤ K M`.
  have hkey : ∀ n : ℕ, 0 < n → n₀ ≤ n → c * Real.sqrt n ≤ K * M := by
    intro n hn hn₀
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
    obtain ⟨hsum, hle⟩ := hM n hn₀
    have hdecay := norm_fourierCoeffOn_curvedWave_le hpq hpa hab hbq hm hφ hφ' hφ''c hcurv hψ
      hψ'c hsupp hn
    have hpars := (hasSum_sq_fourierCoeffOn_curvedWave hpq hφ hψ hsupp n).tsum_eq
    have h1 := tsum_sq_le_mul_tsum (fun k ↦ norm_nonneg _) hdecay hsum
    rw [hpars] at h1
    have hKn : 0 ≤ K / Real.sqrt n := le_trans (norm_nonneg _) (hdecay 0)
    have h2 : c ≤ K / Real.sqrt n * M := h1.trans (mul_le_mul_of_nonneg_left hle hKn)
    have h3 : c * Real.sqrt n ≤ K / Real.sqrt n * M * Real.sqrt n :=
      mul_le_mul_of_nonneg_right h2 hsn.le
    calc c * Real.sqrt n ≤ K / Real.sqrt n * M * Real.sqrt n := h3
      _ = K * M := by field_simp
  -- Choose `n` with `√n > K M / c`.
  set r : ℝ := K * M / c with hr
  obtain ⟨n, hn⟩ := exists_nat_gt (r ^ 2)
  set N : ℕ := max n₀ (n + 1) with hN
  have hnpos : 0 < N := lt_of_lt_of_le (Nat.succ_pos n) (le_max_right _ _)
  have hr2 : r ^ 2 < (N : ℝ) := by
    have : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (le_max_right _ _)
    push_cast at this
    linarith
  have hrt : |r| < Real.sqrt (N : ℝ) := by
    rw [Real.lt_sqrt (abs_nonneg r), sq_abs]
    exact hr2
  have hk := hkey N hnpos (le_max_left _ _)
  have : Real.sqrt (N : ℝ) ≤ r := by
    rw [hr, le_div_iff₀ hcpos]
    linarith
  linarith [le_abs_self r]

end

end WeakTiling

end

end PhaseRigidity

/-! ## Vandermonde extraction of a single characteristic root -/

section RootExtraction

section

open Polynomial Finset

namespace WeakTiling

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exponential sum `∑ᵢ Uᵢ zᵢⁿ`. -/
def expSum (U z : ι → R) (n : ℕ) : R :=
  ∑ i, U i * z i ^ n

/-- The numerator `∏_{i ≠ j} (X - zᵢ)` of the Lagrange polynomial at `j`. -/
noncomputable def lagrangeNumerator (z : ι → R) (j : ι) : R[X] :=
  ∏ i ∈ univ.erase j, (X - C (z i))

theorem eval_lagrangeNumerator_of_ne (z : ι → R) {i j : ι} (hij : i ≠ j) :
    (lagrangeNumerator z j).eval (z i) = 0 := by
  rw [lagrangeNumerator, eval_prod]
  exact prod_eq_zero (mem_erase.mpr ⟨hij, mem_univ i⟩) (by simp)

theorem eval_lagrangeNumerator_self (z : ι → R) (j : ι) :
    (lagrangeNumerator z j).eval (z j) = ∏ i ∈ univ.erase j, (z j - z i) := by
  simp [lagrangeNumerator, eval_prod]

theorem natDegree_lagrangeNumerator_lt (z : ι → R) (j : ι) :
    (lagrangeNumerator z j).natDegree < Fintype.card ι := by
  have hle : (lagrangeNumerator z j).natDegree ≤ (univ.erase j).card := by
    have h1 := natDegree_prod_le (univ.erase j) (fun i ↦ X - C (z i))
    have h2 : ∑ i ∈ univ.erase j, (X - C (z i)).natDegree ≤ ∑ _i ∈ univ.erase j, (1 : ℕ) :=
      sum_le_sum fun i _ ↦ natDegree_X_sub_C_le (z i)
    simp only [sum_const, smul_eq_mul, mul_one] at h2
    exact h1.trans h2
  have hcard : (univ.erase j).card < Fintype.card ι := by
    rw [card_erase_of_mem (mem_univ j), card_univ]
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
    omega
  exact hle.trans_lt hcard

/-- The normalized Lagrange polynomial at `j`, defined when `∏_{i ≠ j} (zⱼ - zᵢ)` is a unit. -/
noncomputable def lagrangeBasis (z : ι → R) (j : ι)
    (hD : IsUnit (∏ i ∈ univ.erase j, (z j - z i))) : R[X] :=
  C (↑hD.unit⁻¹ : R) * lagrangeNumerator z j

theorem eval_lagrangeBasis (z : ι → R) (j : ι)
    (hD : IsUnit (∏ i ∈ univ.erase j, (z j - z i))) (i : ι) :
    (lagrangeBasis z j hD).eval (z i) = if i = j then 1 else 0 := by
  rw [lagrangeBasis, eval_mul, eval_C]
  split_ifs with hij
  · subst hij
    rw [eval_lagrangeNumerator_self]
    exact hD.val_inv_mul
  · rw [eval_lagrangeNumerator_of_ne z hij, mul_zero]

theorem natDegree_lagrangeBasis_lt (z : ι → R) (j : ι)
    (hD : IsUnit (∏ i ∈ univ.erase j, (z j - z i))) :
    (lagrangeBasis z j hD).natDegree < Fintype.card ι :=
  (natDegree_C_mul_le _ _).trans_lt (natDegree_lagrangeNumerator_lt z j)

/-- The extraction weights `wᵣ = [Xʳ]Qⱼ`. -/
noncomputable def extractionWeight (z : ι → R) (j : ι)
    (hD : IsUnit (∏ i ∈ univ.erase j, (z j - z i))) (r : ℕ) : R :=
  (lagrangeBasis z j hD).coeff r

/-- **Vandermonde extraction.**  A fixed finite combination of consecutive terms of
`fₙ = ∑ᵢ Uᵢ zᵢⁿ` isolates the single wave `Uⱼ zⱼⁿ`, for every `n`. -/
theorem sum_extractionWeight_mul_expSum (U z : ι → R) (j : ι)
    (hD : IsUnit (∏ i ∈ univ.erase j, (z j - z i))) (n : ℕ) :
    ∑ r ∈ range (Fintype.card ι), extractionWeight z j hD r * expSum U z (n + r) =
      U j * z j ^ n := by
  have hQ : ∀ i, ∑ r ∈ range (Fintype.card ι), extractionWeight z j hD r * z i ^ r =
      if i = j then 1 else 0 := fun i ↦ by
    rw [← eval_lagrangeBasis z j hD i,
      eval_eq_sum_range' (natDegree_lagrangeBasis_lt z j hD)]
    rfl
  calc ∑ r ∈ range (Fintype.card ι), extractionWeight z j hD r * expSum U z (n + r)
      = ∑ i, U i * z i ^ n *
          ∑ r ∈ range (Fintype.card ι), extractionWeight z j hD r * z i ^ r := by
        simp only [expSum, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun i _ ↦ sum_congr rfl fun r _ ↦ ?_
        rw [pow_add]
        ring
    _ = ∑ i, U i * z i ^ n * (if i = j then 1 else 0) := by simp_rw [hQ]
    _ = U j * z j ^ n := by simp

end WeakTiling

end

end RootExtraction

/-! ## Wiener-norm bridge for one-variable phase rigidity -/

section WienerBridge

section

open Set Complex MeasureTheory Finset

namespace WeakTiling

variable {p q : ℝ}

/-- The character `eₖ(t) = exp(2πi k t / T)`. -/
noncomputable def circleChar (T : ℝ) (k : ℤ) (t : ℝ) : ℂ :=
  exp (2 * Real.pi * I * k * t / T)

/-- A trigonometric polynomial `∑_{k ∈ s} cₖ eₖ`. -/
noncomputable def trigPoly (T : ℝ) (s : Finset ℤ) (c : ℤ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ s, c k * circleChar T k t

theorem continuous_circleChar (T : ℝ) (k : ℤ) : Continuous (circleChar T k) := by
  unfold circleChar
  fun_prop

theorem continuous_trigPoly (T : ℝ) (s : Finset ℤ) (c : ℤ → ℂ) :
    Continuous (trigPoly T s c) := by
  unfold trigPoly
  exact continuous_finsetSum _ fun k _ ↦ continuous_const.mul (continuous_circleChar T k)

/-- Fourier coefficients on `[p,q]` written with the elementary character. -/
theorem fourierCoeffOn_eq_integral_circleChar (hpq : p < q) (f : ℝ → ℂ) (i : ℤ) :
    fourierCoeffOn hpq f i =
      (1 / (q - p)) • ∫ x in p..q, circleChar (q - p) (-i) x * f x := by
  rw [fourierCoeffOn_eq_integral _ _ hpq]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [circleChar, smul_eq_mul]
  rw [fourier_coe_apply]

/-- Fourier coefficients commute with finite sums of continuous functions. -/
theorem fourierCoeffOn_finset_sum (hpq : p < q) {α : Type*} (s : Finset α)
    (F : α → ℝ → ℂ) (hF : ∀ a ∈ s, Continuous (F a)) (i : ℤ) :
    fourierCoeffOn hpq (fun t ↦ ∑ a ∈ s, F a t) i = ∑ a ∈ s, fourierCoeffOn hpq (F a) i := by
  simp_rw [fourierCoeffOn_eq_integral_circleChar hpq, ← Finset.smul_sum, Finset.mul_sum]
  congr 1
  exact intervalIntegral.integral_finsetSum fun a ha ↦
    ((continuous_circleChar _ _).mul (hF a ha)).intervalIntegrable _ _

/-- Fourier coefficients commute with scalar multiplication. -/
theorem fourierCoeffOn_const_mul (hpq : p < q) (c : ℂ) (F : ℝ → ℂ) (i : ℤ) :
    fourierCoeffOn hpq (fun t ↦ c * F t) i = c * fourierCoeffOn hpq F i := by
  rw [fourierCoeffOn_eq_integral_circleChar hpq, fourierCoeffOn_eq_integral_circleChar hpq]
  have h : (∫ x in p..q, circleChar (q - p) (-i) x * (c * F x)) =
      c * ∫ x in p..q, circleChar (q - p) (-i) x * F x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [h, mul_smul_comm]

/-- Multiplying by a character shifts the Fourier coefficients. -/
theorem fourierCoeffOn_circleChar_mul (hpq : p < q) (k : ℤ) (F : ℝ → ℂ) (i : ℤ) :
    fourierCoeffOn hpq (fun t ↦ circleChar (q - p) k t * F t) i =
      fourierCoeffOn hpq F (i - k) := by
  simp_rw [fourierCoeffOn_eq_integral_circleChar hpq]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [circleChar]
  rw [← mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

/-- The Fourier coefficients of `h · P` for a trigonometric polynomial `P`. -/
theorem fourierCoeffOn_mul_trigPoly (hpq : p < q) {h : ℝ → ℂ} (hc : Continuous h)
    (s : Finset ℤ) (c : ℤ → ℂ) (i : ℤ) :
    fourierCoeffOn hpq (fun t ↦ h t * trigPoly (q - p) s c t) i =
      ∑ k ∈ s, c k * fourierCoeffOn hpq h (i - k) := by
  have hfun : (fun t ↦ h t * trigPoly (q - p) s c t) =
      fun t ↦ ∑ k ∈ s, c k * (circleChar (q - p) k t * h t) := by
    funext t
    rw [trigPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [hfun, fourierCoeffOn_finset_sum hpq s (fun k t ↦ c k * (circleChar (q - p) k t * h t))
    (fun k _ ↦ continuous_const.mul ((continuous_circleChar _ _).mul hc))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [fourierCoeffOn_const_mul hpq, fourierCoeffOn_circleChar_mul hpq]

/-- **Wiener bound for a product with a trigonometric polynomial.**

If `h` is continuous with absolutely summable Fourier coefficients, then so is `h P`, and
`‖h P‖_A ≤ (∑ₖ |cₖ|) ‖h‖_A`. -/
theorem wiener_mul_trigPoly_le (hpq : p < q) {h : ℝ → ℂ} (hc : Continuous h)
    (hsum : Summable fun i ↦ ‖fourierCoeffOn hpq h i‖) (s : Finset ℤ) (c : ℤ → ℂ) :
    Summable (fun i ↦ ‖fourierCoeffOn hpq (fun t ↦ h t * trigPoly (q - p) s c t) i‖) ∧
      ∑' i, ‖fourierCoeffOn hpq (fun t ↦ h t * trigPoly (q - p) s c t) i‖ ≤
        (∑ k ∈ s, ‖c k‖) * ∑' i, ‖fourierCoeffOn hpq h i‖ := by
  set B : ℤ → ℝ := fun i ↦ ∑ k ∈ s, ‖c k‖ * ‖fourierCoeffOn hpq h (i - k)‖ with hB
  have hshift : ∀ k : ℤ, Summable fun i ↦ ‖fourierCoeffOn hpq h (i - k)‖ := fun k ↦
    hsum.comp_injective (sub_left_injective (b := k))
  have hBsum : Summable B := summable_sum fun k _ ↦ (hshift k).mul_left _
  have hpt : ∀ i, ‖fourierCoeffOn hpq (fun t ↦ h t * trigPoly (q - p) s c t) i‖ ≤ B i := by
    intro i
    rw [fourierCoeffOn_mul_trigPoly hpq hc]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    rw [norm_mul]
  have hSum := Summable.of_nonneg_of_le (fun i ↦ norm_nonneg _) hpt hBsum
  refine ⟨hSum, (hSum.tsum_le_tsum hpt hBsum).trans_eq ?_⟩
  rw [hB, Summable.tsum_finsetSum fun k _ ↦ (hshift k).mul_left _, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.subRight k).tsum_eq fun i ↦ ‖fourierCoeffOn hpq h i‖

/-- **Wiener bound for a finite combination `∑ᵣ hᵣ Pᵣ`.** -/
theorem wiener_sum_mul_trigPoly_le (hpq : p < q) (d : ℕ) {h : ℕ → ℝ → ℂ}
    (hc : ∀ r, Continuous (h r)) (hsum : ∀ r, Summable fun i ↦ ‖fourierCoeffOn hpq (h r) i‖)
    (s : ℕ → Finset ℤ) (c : ℕ → ℤ → ℂ) :
    Summable (fun i ↦ ‖fourierCoeffOn hpq
        (fun t ↦ ∑ r ∈ range d, h r t * trigPoly (q - p) (s r) (c r) t) i‖) ∧
      ∑' i, ‖fourierCoeffOn hpq
          (fun t ↦ ∑ r ∈ range d, h r t * trigPoly (q - p) (s r) (c r) t) i‖ ≤
        ∑ r ∈ range d, (∑ k ∈ s r, ‖c r k‖) * ∑' i, ‖fourierCoeffOn hpq (h r) i‖ := by
  have hcoef : ∀ i, fourierCoeffOn hpq
      (fun t ↦ ∑ r ∈ range d, h r t * trigPoly (q - p) (s r) (c r) t) i =
        ∑ r ∈ range d, fourierCoeffOn hpq (fun t ↦ h r t * trigPoly (q - p) (s r) (c r) t) i :=
    fun i ↦ fourierCoeffOn_finset_sum hpq (range d) _
      (fun r _ ↦ (hc r).mul (continuous_trigPoly _ _ _)) i
  have hr := fun r ↦ wiener_mul_trigPoly_le hpq (hc r) (hsum r) (s r) (c r)
  set B : ℤ → ℝ := fun i ↦ ∑ r ∈ range d,
    ‖fourierCoeffOn hpq (fun t ↦ h r t * trigPoly (q - p) (s r) (c r) t) i‖ with hB
  have hBsum : Summable B := summable_sum fun r _ ↦ (hr r).1
  have hpt : ∀ i, ‖fourierCoeffOn hpq
      (fun t ↦ ∑ r ∈ range d, h r t * trigPoly (q - p) (s r) (c r) t) i‖ ≤ B i := fun i ↦ by
    rw [hcoef]
    exact norm_sum_le _ _
  have hSum := Summable.of_nonneg_of_le (fun i ↦ norm_nonneg _) hpt hBsum
  refine ⟨hSum, (hSum.tsum_le_tsum hpt hBsum).trans ?_⟩
  rw [hB, Summable.tsum_finsetSum fun r _ ↦ (hr r).1]
  exact Finset.sum_le_sum fun r _ ↦ (hr r).2

open Classical in
/-- **Pointwise extraction of a localized wave.**

Suppose that on `[a,b]` the row functions are exponential sums `Fₙ = ∑ᵢ Uᵢ zᵢⁿ` for `n ≥ n₀`,
that the root `zⱼ = exp(iφ)` there, and that the root differences are invertible.  Put
`ψ = χ Uⱼ` for a cutoff `χ` vanishing off `(a,b)`.  Then the localized wave `ψ exp(i n φ)`
equals `∑ᵣ hᵣ F_{n+r}` with the localized Lagrange weights `hᵣ = χ wᵣ`. -/
theorem curvedWave_eq_sum_extraction {a b : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (χ : ℝ → ℂ) (U z : ι → ℝ → ℂ) (j : ι) (φ : ℝ → ℝ) (F : ℕ → ℝ → ℂ) (n₀ : ℕ)
    (hχ : ∀ t, t ∉ Ioo a b → χ t = 0)
    (hz : ∀ t ∈ Icc a b, z j t = exp ((φ t : ℂ) * I))
    (hD : ∀ t ∈ Icc a b, IsUnit (∏ i ∈ univ.erase j, (z j t - z i t)))
    (hF : ∀ n, n₀ ≤ n → ∀ t ∈ Icc a b, F n t = expSum (fun i ↦ U i t) (fun i ↦ z i t) n)
    {n : ℕ} (hn : n₀ ≤ n) (t : ℝ) :
    curvedWave (fun t ↦ χ t * U j t) φ n t =
      ∑ r ∈ range (Fintype.card ι),
        (χ t * (if h : IsUnit (∏ i ∈ univ.erase j, (z j t - z i t)) then
          extractionWeight (fun i ↦ z i t) j h r else 0)) * F (n + r) t := by
  by_cases ht : t ∈ Ioo a b
  · have htc : t ∈ Icc a b := Ioo_subset_Icc_self ht
    simp only [dite_eq_left (hD t htc)]
    have hwave : curvedWave (fun t ↦ χ t * U j t) φ n t = χ t * (U j t * z j t ^ n) := by
      rw [curvedWave, hz t htc, ← exp_nat_mul]
      push_cast
      ring_nf
    rw [hwave, ← sum_extractionWeight_mul_expSum (fun i ↦ U i t) (fun i ↦ z i t) j (hD t htc) n,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [hF (n + r) (hn.trans (Nat.le_add_right n r)) t htc]
    ring
  · simp [curvedWave, hχ t ht]

open Classical in
/-- **One-variable step H: a curved characteristic root has zero localized amplitude.**

Let the row functions `Fₙ` be trigonometric polynomials on the circle `[p,q]` with uniformly
bounded coefficient sums (the output of step W).  Suppose that on `[a,b] ⊆ [p,q]` they are
exponential sums `∑ᵢ Uᵢ zᵢⁿ` with invertible root differences.  Take a `C¹` cutoff `χ`
supported in `(a,b)` such that `ψ = χ Uⱼ` is `C¹` and the localized weights `hᵣ = χ wᵣ` are
continuous with absolutely summable Fourier coefficients.  If the root `zⱼ = exp(iφ)` has
`|φ''| ≥ m > 0`, then `ψ = 0` almost everywhere on `[p,q]`. -/
theorem amplitude_eq_zero_of_curved_root {a b m M : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpq : p < q) (hpa : p ≤ a) (hab : a ≤ b) (hbq : b ≤ q) (hm : 0 < m)
    (χ : ℝ → ℂ) (U z : ι → ℝ → ℂ) (j : ι) {φ φ' φ'' : ℝ → ℝ} {ψ' : ℝ → ℂ}
    (s : ℕ → Finset ℤ) (c : ℕ → ℤ → ℂ) (n₀ : ℕ)
    -- step W: uniformly bounded coefficient sums of the row polynomials
    (hW : ∀ n, n₀ ≤ n → ∑ k ∈ s n, ‖c n k‖ ≤ M)
    -- local root expansion
    (hz : ∀ t ∈ Icc a b, z j t = exp ((φ t : ℂ) * I))
    (hD : ∀ t ∈ Icc a b, IsUnit (∏ i ∈ univ.erase j, (z j t - z i t)))
    (hF : ∀ n, n₀ ≤ n → ∀ t ∈ Icc a b,
      trigPoly (q - p) (s n) (c n) t = expSum (fun i ↦ U i t) (fun i ↦ z i t) n)
    -- regularity of the cutoff, the amplitude and the localized weights
    (hχ : ∀ t, t ∉ Ioo a b → χ t = 0)
    (hψ : ∀ t ∈ Icc a b, HasDerivAt (fun t ↦ χ t * U j t) (ψ' t) t)
    (hψ'c : ContinuousOn ψ' (Icc a b))
    (hwc : ∀ r, Continuous fun t ↦ χ t * (if h : IsUnit (∏ i ∈ univ.erase j, (z j t - z i t))
      then extractionWeight (fun i ↦ z i t) j h r else 0))
    (hwsum : ∀ r, Summable fun i ↦ ‖fourierCoeffOn hpq (fun t ↦ χ t *
      (if h : IsUnit (∏ i ∈ univ.erase j, (z j t - z i t))
        then extractionWeight (fun i ↦ z i t) j h r else 0)) i‖)
    -- curvature of the phase
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hcurv : ∀ t ∈ Icc a b, m ≤ |φ'' t|) :
    ∫ x in p..q, ‖χ x * U j x‖ ^ 2 = 0 := by
  set ψ : ℝ → ℂ := fun t ↦ χ t * U j t with hψdef
  set h : ℕ → ℝ → ℂ := fun r t ↦ χ t * (if h : IsUnit (∏ i ∈ univ.erase j, (z j t - z i t))
      then extractionWeight (fun i ↦ z i t) j h r else 0) with hhdef
  have hsupp : ∀ t, t ∉ Ioo a b → ψ t = 0 := fun t ht ↦ by simp [ψ, hχ t ht]
  have hnonneg : 0 ≤ ∫ x in p..q, ‖ψ x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hpq.le fun x _ ↦ sq_nonneg _
  by_contra hne
  have hpos : 0 < ∫ x in p..q, ‖ψ x‖ ^ 2 := lt_of_le_of_ne hnonneg (Ne.symm hne)
  apply not_bounded_wienerNorm_curvedWave hpq hpa hab hbq hm hφ hφ' hφ''c hcurv hψ hψ'c hsupp
    hpos
  set d := Fintype.card ι
  refine ⟨∑ r ∈ range d, M * ∑' i, ‖fourierCoeffOn hpq (h r) i‖, n₀, fun n hn ↦ ?_⟩
  have hrep : curvedWave ψ φ n =
      fun t ↦ ∑ r ∈ range d, h r t * trigPoly (q - p) (s (n + r)) (c (n + r)) t := by
    funext t
    exact curvedWave_eq_sum_extraction χ U z j φ (fun n ↦ trigPoly (q - p) (s n) (c n)) n₀
      hχ hz hD hF hn t
  have hb := wiener_sum_mul_trigPoly_le hpq d hwc hwsum (fun r ↦ s (n + r))
    (fun r ↦ c (n + r))
  rw [hrep]
  refine ⟨hb.1, hb.2.trans (Finset.sum_le_sum fun r _ ↦ ?_)⟩
  exact mul_le_mul_of_nonneg_right (hW (n + r) (hn.trans (Nat.le_add_right n r)))
    (tsum_nonneg fun i ↦ norm_nonneg _)

end WeakTiling

end

end WienerBridge

/-! ## Step I: integration on the Formal Conjectures definitions -/

section Integration

section

open MeasureTheory Polynomial Finset

namespace WeakTiling

/-- The Wiener (`ℓ¹`) norm of a multivariable polynomial: the sum of the absolute values of its
coefficients. -/
noncomputable def mvNorm1 {σ : Type*} (g : MvPolynomial σ ℂ) : ℝ :=
  ∑ s ∈ g.support, ‖g.coeff s‖

theorem mvNorm1_nonneg {σ : Type*} (g : MvPolynomial σ ℂ) : 0 ≤ mvNorm1 g :=
  sum_nonneg fun _ _ ↦ norm_nonneg _

/-- For nonnegative real coefficients, the Wiener norm is the value at `(1, …, 1)`. -/
theorem mvEval_one_eq_mvNorm1 {σ : Type*} (g : MvPolynomial σ ℂ)
    (hnn : ∀ s, 0 ≤ (g.coeff s).re ∧ (g.coeff s).im = 0) :
    MvPolynomial.eval (fun _ ↦ (1 : ℂ)) g = (mvNorm1 g : ℂ) := by
  rw [MvPolynomial.eval_eq, mvNorm1, Complex.ofReal_sum]
  refine sum_congr rfl fun s _ ↦ ?_
  simp only [one_pow, prod_const_one, mul_one]
  obtain ⟨hre, him⟩ := hnn s
  have hz : g.coeff s = ((g.coeff s).re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hz, Complex.norm_real, Real.norm_of_nonneg hre]

/-- **Output of steps M and G for one side of the support.**

Rows `fₙ` in any number of variables `σ`, with nonnegative real coefficients, satisfy
`P · ∑ₙ fₙ xⁿ = R` coefficient-wise.  The specialization `Q = P(x, 1, …, 1)` satisfies the
pole conditions. -/
structure GeneratingData (σ : Type*) where
  /-- The rows `fₙ` of the generating function. -/
  rows : ℕ → MvPolynomial σ ℂ
  /-- The denominator polynomial `P`. -/
  P : Polynomial (MvPolynomial σ ℂ)
  /-- The numerator polynomial `R`. -/
  R : Polynomial (MvPolynomial σ ℂ)
  identity : ∀ n, ∑ ij ∈ antidiagonal n, P.coeff ij.1 * rows ij.2 = R.coeff n
  nonneg : ∀ n s, 0 ≤ ((rows n).coeff s).re ∧ ((rows n).coeff s).im = 0
  spec_ne_zero : P.map (MvPolynomial.eval fun _ ↦ (1 : ℂ)) ≠ 0
  no_zero_in_unit_interval :
    ∀ x : ℝ, 0 < x → x < 1 → (P.map (MvPolynomial.eval fun _ ↦ (1 : ℂ))).eval (x : ℂ) ≠ 0
  simple_zero_at_one :
    (P.map (MvPolynomial.eval fun _ ↦ (1 : ℂ))).eval 1 = 0 →
      (derivative (P.map (MvPolynomial.eval fun _ ↦ (1 : ℂ)))).eval 1 ≠ 0

/-- **Step W, formalized.**  Generating data has uniformly bounded row norms. -/
theorem GeneratingData.rowNorm_bounded {σ : Type*} (D : GeneratingData σ) :
    ∃ B : ℝ, ∀ n, mvNorm1 (D.rows n) ≤ B := by
  set ev : MvPolynomial σ ℂ →+* ℂ := MvPolynomial.eval fun _ ↦ (1 : ℂ) with hev
  set a : ℕ → ℝ := fun n ↦ mvNorm1 (D.rows n) with ha
  have hspec : ∀ n, ∑ ij ∈ antidiagonal n,
      (D.P.map ev).coeff ij.1 * (a ij.2 : ℂ) = (D.R.map ev).coeff n := by
    intro n
    have := congrArg ev (D.identity n)
    rw [map_sum] at this
    simp only [coeff_map, map_mul] at this ⊢
    rw [← this]
    refine sum_congr rfl fun ij _ ↦ ?_
    rw [ha]
    simp only
    rw [hev, mvEval_one_eq_mvNorm1 _ (D.nonneg ij.2)]
  exact bounded_of_rational_pole_conditions a (fun n ↦ mvNorm1_nonneg _) _ _ D.spec_ne_zero
    hspec D.no_zero_in_unit_interval D.simple_zero_at_one

end WeakTiling

end

end Integration

/-! ## Rows built from the actual weak-tiling atoms -/

section MeasureGeneratingData

section

open MeasureTheory Finset

namespace WeakTiling

/-- Total coordinate degree of a multivariate natural exponent. -/
def coordinateExponentDegree {ι : Type*} [Fintype ι] (e : ι →₀ ℕ) : ℕ :=
  ∑ k, e k

/-- Total degree converts exponent-vector addition into outer-degree addition. -/
theorem coordinateExponentDegree_add {ι : Type*} [Fintype ι]
    (e f : ι →₀ ℕ) :
    coordinateExponentDegree (e + f) = coordinateExponentDegree e + coordinateExponentDegree f := by
  classical
  simp [coordinateExponentDegree, Finset.sum_add_distrib]

/-- Subtraction in the exponent vectors is additive under total degree. -/
theorem coordinateExponentDegree_sub_add {ι : Type*} [Fintype ι]
    {e s : ι →₀ ℕ} (hle : s ≤ e) :
    coordinateExponentDegree (e - s) + coordinateExponentDegree s =
      coordinateExponentDegree e := by
  have hadd : e - s + s = e := by
    ext k
    exact Nat.sub_add_cancel (hle k)
  have hdegree := congrArg coordinateExponentDegree hadd
  rw [coordinateExponentDegree_add] at hdegree
  exact hdegree

/-- Total degree subtracts additively when one exponent is coordinatewise below another. -/
theorem coordinateExponentDegree_sub {ι : Type*} [Fintype ι]
    {e s : ι →₀ ℕ} (hle : s ≤ e) :
    coordinateExponentDegree (e - s) =
      coordinateExponentDegree e - coordinateExponentDegree s := by
  have h := coordinateExponentDegree_sub_add hle
  omega

/-- For a fixed finite set of variables, only finitely many monomials have a fixed total degree. -/
theorem coordinateExponentDegree_fiber_finite {ι : Type*} [Fintype ι] (n : ℕ) :
    {e : ι →₀ ℕ | coordinateExponentDegree e = n}.Finite := by
  classical
  let E := Finsupp.equivFunOnFinite (α := ι) (M := ℕ)
  let box : Set (ι → ℕ) := {v | ∀ k, v k ≤ n}
  have hbox : box.Finite := by
    simpa [box, Set.mem_Icc] using
      (Set.Finite.pi' (t := fun _ : ι ↦ Set.Icc (0 : ℕ) n)
        (fun _ ↦ Set.finite_Icc _ _))
  have hpre : (E ⁻¹' box).Finite := hbox.preimage_embedding E.toEmbedding
  apply hpre.subset
  intro e he
  change E e ∈ box
  change coordinateExponentDegree e = n at he
  change ∀ k, E e k ≤ n
  intro k
  have hk : e k ≤ ∑ j : ι, e j :=
    Finset.single_le_sum (f := fun j : ι ↦ e j)
      (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ k)
  have hsum : (∑ j : ι, e j) = n := by simpa [coordinateExponentDegree] using he
  simpa [E, Finsupp.equivFunOnFinite] using hsum ▸ hk

/-- The total degree of a function-valued natural exponent. -/
def coordinateFunctionDegree {ι : Type*} [Fintype ι] (v : ι → ℕ) : ℕ :=
  ∑ k, v k

/-- View a function-valued exponent as the corresponding finitely supported exponent. -/
noncomputable def coordinateFunctionExponent {ι : Type*} [Fintype ι]
    (v : ι → ℕ) : ι →₀ ℕ :=
  (Finsupp.equivFunOnFinite (α := ι) (M := ℕ)).symm v

@[simp]
theorem coordinateFunctionExponent_apply {ι : Type*} [Fintype ι]
  (v : ι → ℕ) (k : ι) : coordinateFunctionExponent v k = v k := by
  simp [coordinateFunctionExponent]

/-- The function-to-exponent equivalence preserves total degree. -/
theorem coordinateFunctionExponent_degree {ι : Type*} [Fintype ι] (v : ι → ℕ) :
    coordinateExponentDegree (coordinateFunctionExponent v) = coordinateFunctionDegree v := by
  classical
  simp [coordinateExponentDegree, coordinateFunctionDegree,
    coordinateFunctionExponent, Finsupp.equivFunOnFinite]

/-- The endpoint-shift denominator: each left endpoint contributes one positive monomial and
each right endpoint contributes one negative monomial. The outer degree records the total
coordinate degree, matching the row indexing used below. -/
noncomputable def weakTilingEndpointDenominator {ι : Type*} [Fintype ι] {n : ℕ}
    (p q : Fin n → ι → ℕ) : Polynomial (MvPolynomial ι ℂ) :=
  ∑ j : Fin n,
    (Polynomial.monomial (coordinateFunctionDegree (p j))
      (MvPolynomial.monomial (coordinateFunctionExponent (p j)) (1 : ℂ)) -
    Polynomial.monomial (coordinateFunctionDegree (q j))
      (MvPolynomial.monomial (coordinateFunctionExponent (q j)) (1 : ℂ)))

/-- Specializing every multivariate variable to one forgets the endpoint shape and leaves the
one-variable denominator whose exponents are the total coordinate degrees. -/
theorem weakTilingEndpointDenominator_map_eval_one {ι : Type*} [Fintype ι] {n : ℕ}
    (p q : Fin n → ι → ℕ) :
    (weakTilingEndpointDenominator p q).map (MvPolynomial.eval fun _ ↦ (1 : ℂ)) =
      ∑ j : Fin n,
        (Polynomial.monomial (coordinateFunctionDegree (p j)) (1 : ℂ) -
          Polynomial.monomial (coordinateFunctionDegree (q j)) (1 : ℂ)) := by
  classical
  simp [weakTilingEndpointDenominator, coordinateFunctionDegree,
    coordinateFunctionExponent, Polynomial.map_sum, Polynomial.map_sub,
    Polynomial.map_monomial, MvPolynomial.eval_monomial]

/-- The outer coefficient of the endpoint denominator is the signed sum of its endpoint
monomials. -/
theorem weakTilingEndpointDenominator_coeff {ι : Type*} [Fintype ι] {n : ℕ}
    (p q : Fin n → ι → ℕ) (d : ℕ) :
    (weakTilingEndpointDenominator p q).coeff d =
      ∑ j : Fin n,
        ((if coordinateFunctionDegree (p j) = d then
            MvPolynomial.monomial (coordinateFunctionExponent (p j)) (1 : ℂ) else 0) -
          if coordinateFunctionDegree (q j) = d then
            MvPolynomial.monomial (coordinateFunctionExponent (q j)) (1 : ℂ) else 0) := by
  classical
  simp [weakTilingEndpointDenominator, Polynomial.coeff_monomial]

/-- In an outer antidiagonal convolution, one endpoint monomial selects exactly the row whose
index is the remaining total degree. -/
theorem endpointMonomial_convolution {ι : Type*} [Fintype ι]
    (s : ι →₀ ℕ) (rows : ℕ → MvPolynomial ι ℂ) (d : ℕ) :
    (∑ ij ∈ antidiagonal d,
      (if ij.1 = coordinateExponentDegree s then
        MvPolynomial.monomial s (1 : ℂ) else 0) * rows ij.2) =
      if coordinateExponentDegree s ≤ d then
        MvPolynomial.monomial s (1 : ℂ) * rows (d - coordinateExponentDegree s)
      else 0 := by
  classical
  let D := coordinateExponentDegree s
  by_cases hD : D ≤ d
  · have hpair : (D, d - D) ∈ antidiagonal d := by
      simp [Nat.add_sub_of_le hD]
    rw [Finset.sum_eq_single (D, d - D)]
    · simp [D, hD]
    · intro ij hij hne
      have hadd : ij.1 + ij.2 = d := by
        simpa [Finset.mem_antidiagonal] using hij
      by_cases hfirst : ij.1 = D
      · have hpairEq : ij = (D, d - D) := by
          rcases ij with ⟨a, b⟩
          simp only [Prod.mk.injEq]
          constructor
          · exact hfirst
          · omega
        exact (hne hpairEq).elim
      · simp [hfirst, D]
    · intro hnot
      exact (hnot hpair).elim
  · have hzero : ∀ ij ∈ antidiagonal d,
        (if ij.1 = D then MvPolynomial.monomial s (1 : ℂ) else 0) * rows ij.2 = 0 := by
      intro ij hij
      have hadd : ij.1 + ij.2 = d := by
        simpa [Finset.mem_antidiagonal] using hij
      by_cases hfirst : ij.1 = D
      · have hle : D ≤ d := by omega
        exact (hD hle).elim
      · simp [hfirst, D]
    rw [Finset.sum_eq_zero hzero]
    simp [D, hD]

/-- The full endpoint denominator acts on rows by the finite sum of its shifted rows. -/
theorem weakTilingEndpointDenominator_antidiagonal {ι : Type*} [Fintype ι] {n : ℕ}
    (p q : Fin n → ι → ℕ) (rows : ℕ → MvPolynomial ι ℂ) (d : ℕ) :
    (∑ ij ∈ antidiagonal d,
      (weakTilingEndpointDenominator p q).coeff ij.1 * rows ij.2) =
      ∑ j : Fin n,
        ((if coordinateFunctionDegree (p j) ≤ d then
            MvPolynomial.monomial (coordinateFunctionExponent (p j)) (1 : ℂ) *
              rows (d - coordinateFunctionDegree (p j)) else 0) -
          if coordinateFunctionDegree (q j) ≤ d then
            MvPolynomial.monomial (coordinateFunctionExponent (q j)) (1 : ℂ) *
              rows (d - coordinateFunctionDegree (q j)) else 0) := by
  classical
  simp_rw [weakTilingEndpointDenominator_coeff, Finset.sum_mul, sub_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_sub_distrib]
  simp_rw [← coordinateFunctionExponent_degree]
  have hp :
      (∑ j : Fin n, ∑ ij ∈ antidiagonal d,
        (if coordinateExponentDegree (coordinateFunctionExponent (p j)) = ij.1 then
          MvPolynomial.monomial (coordinateFunctionExponent (p j)) (1 : ℂ) else 0) *
            rows ij.2) =
        ∑ j : Fin n,
          (if coordinateExponentDegree (coordinateFunctionExponent (p j)) ≤ d then
            MvPolynomial.monomial (coordinateFunctionExponent (p j)) (1 : ℂ) *
              rows (d - coordinateExponentDegree (coordinateFunctionExponent (p j))) else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [eq_comm] using
      (endpointMonomial_convolution (coordinateFunctionExponent (p j)) rows d)
  have hq :
      (∑ j : Fin n, ∑ ij ∈ antidiagonal d,
        (if coordinateExponentDegree (coordinateFunctionExponent (q j)) = ij.1 then
          MvPolynomial.monomial (coordinateFunctionExponent (q j)) (1 : ℂ) else 0) *
            rows ij.2) =
        ∑ j : Fin n,
          (if coordinateExponentDegree (coordinateFunctionExponent (q j)) ≤ d then
            MvPolynomial.monomial (coordinateFunctionExponent (q j)) (1 : ℂ) *
              rows (d - coordinateExponentDegree (coordinateFunctionExponent (q j))) else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [eq_comm] using
      (endpointMonomial_convolution (coordinateFunctionExponent (q j)) rows d)
  rw [hp, hq]

/-- Convert a finitely supported integer-lattice sequence into a finite bivariate generating
polynomial. For sequences supported in the nonnegative orthant, this records each lattice point
at its total degree and its multivariate exponent. -/
noncomputable def integerLatticeFinsuppPolynomial {ι : Type*} [Fintype ι]
    (c : (ι → ℤ) →₀ ℝ) : Polynomial (MvPolynomial ι ℂ) := by
  classical
  exact ∑ u ∈ c.support,
    Polynomial.monomial (coordinateFunctionDegree (fun k ↦ (u k).toNat))
      (MvPolynomial.monomial
        (coordinateFunctionExponent (fun k ↦ (u k).toNat)) (c u : ℂ))

/-- Coefficients of the finite lattice polynomial recover the original sequence on the
nonnegative orthant. -/
theorem integerLatticeFinsuppPolynomial_coeff {ι : Type*} [Fintype ι]
    (c : (ι → ℤ) →₀ ℝ)
    (hc : ∀ u ∈ c.support, ∀ k, 0 ≤ u k)
    (n : ℕ) (e : ι →₀ ℕ) :
    ((integerLatticeFinsuppPolynomial c).coeff n).coeff e =
      if coordinateExponentDegree e = n then
        (c (fun k ↦ (e k : ℤ)) : ℂ) else 0 := by
  classical
  let u₀ : ι → ℤ := fun k ↦ (e k : ℤ)
  let exponent (u : ι → ℤ) : ι →₀ ℕ :=
    coordinateFunctionExponent (fun k ↦ (u k).toNat)
  let degree (u : ι → ℤ) : ℕ := coordinateFunctionDegree (fun k ↦ (u k).toNat)
  have hexponentFun (u : ι → ℤ) (he : exponent u = e) :
      (fun k ↦ (u k).toNat) = fun k ↦ e k := by
    have h := congrArg (Finsupp.equivFunOnFinite (α := ι) (M := ℕ)) he
    simpa [exponent, coordinateFunctionExponent, Finsupp.equivFunOnFinite] using h
  have hu_eq (u : ι → ℤ) (hu : u ∈ c.support) (he : exponent u = e) : u = u₀ := by
    have hf := hexponentFun u he
    funext k
    calc
      u k = ((u k).toNat : ℤ) := (Int.toNat_of_nonneg (hc u hu k)).symm
      _ = (e k : ℤ) := by exact_mod_cast congrFun hf k
      _ = u₀ k := rfl
  have hdegree (u : ι → ℤ) (he : exponent u = e) :
      degree u = coordinateExponentDegree e := by
    have hf := hexponentFun u he
    simp [degree, coordinateFunctionDegree, coordinateExponentDegree, hf]
  have hsum :
      ((integerLatticeFinsuppPolynomial c).coeff n).coeff e =
        ∑ u ∈ c.support,
          if degree u = n then if exponent u = e then (c u : ℂ) else 0 else 0 := by
    simp [integerLatticeFinsuppPolynomial, degree, exponent,
      Polynomial.coeff_monomial, MvPolynomial.coeff_sum, apply_ite, ite_apply]
  rw [hsum]
  by_cases hdegreeE : coordinateExponentDegree e = n
  · simp only [ite_eq_left hdegreeE]
    have hexp₀ : exponent u₀ = e := by
      simp [exponent, coordinateFunctionExponent, u₀]
    have hdeg₀ : degree u₀ = n := (hdegree u₀ hexp₀).trans hdegreeE
    by_cases hu₀ : u₀ ∈ c.support
    · rw [Finset.sum_eq_single u₀]
      · simp [hdeg₀, hexp₀, u₀]
      · intro u hu hne
        by_cases hexp : exponent u = e
        · exact (hne (hu_eq u hu hexp)).elim
        · simp [hexp]
      · intro hnot
        exact (hnot hu₀).elim
    · have hc₀ : c u₀ = 0 := by
        by_contra hne
        exact hu₀ (Finsupp.mem_support_iff.mpr hne)
      have hsum_zero :
          (∑ u ∈ c.support,
            if degree u = n then if exponent u = e then (c u : ℂ) else 0 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        by_cases hexp : exponent u = e
        · have huu₀ := hu_eq u hu hexp
          subst u
          simp [hc₀, hdeg₀, hexp₀]
        · simp [hexp]
      rw [hsum_zero]
      exact (congrArg (fun r : ℝ ↦ (r : ℂ)) hc₀).symm
  · have hsum_zero :
        (∑ u ∈ c.support,
          if degree u = n then if exponent u = e then (c u : ℂ) else 0 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      by_cases hexp : exponent u = e
      · have hdegU := hdegree u hexp
        simp [hdegU, hdegreeE]
      · simp [hexp]
    rw [hsum_zero]
    simp [hdegreeE]

/-- The normalized atom mass at a coordinate point is nonnegative. -/
theorem coordinateAtomMass_nonneg {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (u : ι → ℤ) :
    0 ≤ coordinateAtomMass β ν u := by
  unfold coordinateAtomMass
  apply add_nonneg ENNReal.toReal_nonneg
  split_ifs <;> positivity

/-- The degree-`n` row of actual normalized weak-tiling atom masses, as a multivariate
polynomial. Exponents outside the degree fiber have coefficient zero. -/
noncomputable def weakTilingCoordinateRow {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (n : ℕ) : MvPolynomial ι ℂ := by
  classical
  exact ⟨Finsupp.ofSupportFinite
    (fun e ↦ if coordinateExponentDegree e = n then
      (coordinateAtomMass β ν (fun k ↦ (e k : ℤ)) : ℂ) else 0)
    (by
      apply (coordinateExponentDegree_fiber_finite n).subset
      intro e he
      change (if coordinateExponentDegree e = n then
        (coordinateAtomMass β ν (fun k ↦ (e k : ℤ)) : ℂ) else 0) ≠ 0 at he
      change coordinateExponentDegree e = n
      by_contra hne
      simp [hne] at he)⟩

@[simp]
theorem weakTilingCoordinateRow_coeff {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (n : ℕ) (e : ι →₀ ℕ) :
    (weakTilingCoordinateRow β ν n).coeff e =
      if coordinateExponentDegree e = n then
        (coordinateAtomMass β ν (fun k ↦ (e k : ℤ)) : ℂ) else 0 := by
  classical
  rfl

/-- On a natural exponent vector, the orthant restriction is inactive. -/
@[simp]
theorem coordinateAtomPositivePart_nat {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (e : ι →₀ ℕ) :
    coordinateAtomPositivePart β ν (fun k ↦ (e k : ℤ)) =
      coordinateAtomMass β ν (fun k ↦ (e k : ℤ)) := by
  simp [coordinateAtomPositivePart]

/-- The row coefficients are exactly the positive-orthant atom weights, indexed by total degree. -/
theorem weakTilingCoordinateRow_coeff_eq_positivePart {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (n : ℕ) (e : ι →₀ ℕ) :
    (weakTilingCoordinateRow β ν n).coeff e =
      if coordinateExponentDegree e = n then
        (coordinateAtomPositivePart β ν (fun k ↦ (e k : ℤ)) : ℂ) else 0 := by
  rw [weakTilingCoordinateRow_coeff, coordinateAtomPositivePart_nat]

theorem weakTilingCoordinateRow_nonneg {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (n : ℕ) (e : ι →₀ ℕ) :
    0 ≤ ((weakTilingCoordinateRow β ν n).coeff e).re ∧
      ((weakTilingCoordinateRow β ν n).coeff e).im = 0 := by
  rw [weakTilingCoordinateRow_coeff]
  split_ifs with h
  · constructor
    · simpa using coordinateAtomMass_nonneg β ν (fun k ↦ (e k : ℤ))
    · simp
  · simp

/-- Multiplication by an endpoint monomial shifts the row coefficients by that endpoint, with
zero exactly when the shifted exponent leaves the natural orthant. -/
theorem weakTilingCoordinateRow_shift_coeff {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (m : ℕ) (s e : ι →₀ ℕ) :
    (MvPolynomial.monomial s (1 : ℂ) * weakTilingCoordinateRow β ν m).coeff e =
      if s ≤ e then
        if coordinateExponentDegree (e - s) = m then
          (coordinateAtomPositivePart β ν
            (fun k ↦ ((e - s) k : ℤ)) : ℂ) else 0
      else 0 := by
  classical
  rw [MvPolynomial.coeff_monomial_mul']
  by_cases hle : s ≤ e
  · simp only [ite_eq_left hle, one_mul]
    rw [weakTilingCoordinateRow_coeff_eq_positivePart]
  · simp [hle]

/-- A shifted homogeneous row contributes only on the degree fiber of the original row, where
its coefficient is the positive-part atom at the residual lattice point. -/
theorem endpointMonomialRow_coeff {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (d : ℕ) (s e : ι →₀ ℕ) :
    (if coordinateExponentDegree s ≤ d then
        MvPolynomial.monomial s (1 : ℂ) *
          weakTilingCoordinateRow β ν (d - coordinateExponentDegree s) else 0).coeff e =
      if coordinateExponentDegree e = d then
        if s ≤ e then
          (coordinateAtomPositivePart β ν
            (fun k ↦ ((e - s) k : ℤ)) : ℂ) else 0
      else 0 := by
  classical
  by_cases hs : coordinateExponentDegree s ≤ d
  · rw [ite_eq_left hs, weakTilingCoordinateRow_shift_coeff]
    by_cases hle : s ≤ e
    · by_cases he : coordinateExponentDegree e = d
      · have hsum := coordinateExponentDegree_sub_add hle
        have hrow : coordinateExponentDegree (e - s) = d - coordinateExponentDegree s := by
          rw [coordinateExponentDegree_sub hle, he]
        simp [he, hle, hrow]
      · have hrow : coordinateExponentDegree (e - s) ≠ d - coordinateExponentDegree s := by
          intro hrow
          have hsum := coordinateExponentDegree_sub_add hle
          omega
        simp [he, hle, hrow]
    · simp [hle]
  · rw [ite_eq_right hs]
    simp only [MvPolynomial.coeff_zero]
    by_cases he : coordinateExponentDegree e = d
    · by_cases hle : s ≤ e
      · have hsum := coordinateExponentDegree_sub_add hle
        exact (hs (by omega)).elim
      · simp [he, hle]
    · simp [he]

/-- The finite function-to-Finsupp equivalence preserves the coordinatewise order. -/
theorem coordinateFunctionExponent_le_iff {ι : Type*} [Fintype ι]
    (v : ι → ℕ) (e : ι →₀ ℕ) :
    coordinateFunctionExponent v ≤ e ↔ ∀ k, v k ≤ e k := by
  have happly (k : ι) : coordinateFunctionExponent v k = v k := by
    exact coordinateFunctionExponent_apply v k
  constructor
  · intro h k
    have hk := h k
    simpa [happly k] using hk
  · intro h k
    have hk := h k
    simpa [happly k] using hk

/-- In function coordinates, a shifted row coefficient is the positive-part atom at the integer
coordinate difference; if the endpoint cannot be subtracted in the natural orthant, that atom is
zero by definition of the positive part. -/
theorem endpointFunctionMonomialRow_coeff {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ν : Measure ℝ) (d : ℕ) (v : ι → ℕ) (e : ι →₀ ℕ) :
    (if coordinateFunctionDegree v ≤ d then
        MvPolynomial.monomial (coordinateFunctionExponent v) (1 : ℂ) *
          weakTilingCoordinateRow β ν (d - coordinateFunctionDegree v) else 0).coeff e =
      if coordinateExponentDegree e = d then
        (coordinateAtomPositivePart β ν
          (fun k ↦ (e k : ℤ) - (v k : ℤ)) : ℂ) else 0 := by
  classical
  simp_rw [← coordinateFunctionExponent_degree]
  rw [endpointMonomialRow_coeff]
  by_cases hle : coordinateFunctionExponent v ≤ e
  · have hpoint : ∀ k, v k ≤ e k :=
      (coordinateFunctionExponent_le_iff v e).mp hle
    have hdiff : (fun k ↦ ((e - coordinateFunctionExponent v) k : ℤ)) =
        (fun k ↦ (e k : ℤ) - (v k : ℤ)) := by
      funext k
      have hk := hpoint k
      change ((e k - coordinateFunctionExponent v k : ℕ) : ℤ) =
        (e k : ℤ) - (v k : ℤ)
      rw [coordinateFunctionExponent_apply]
      exact Nat.cast_sub hk
    rw [hdiff]
    simp [hle]
  · have hnotpoint : ¬∀ k, v k ≤ e k := by
      simpa [coordinateFunctionExponent_le_iff] using hle
    have hzero : coordinateAtomPositivePart β ν
        (fun k ↦ (e k : ℤ) - (v k : ℤ)) = 0 := by
      unfold coordinateAtomPositivePart
      by_cases hnonneg : ∀ k, 0 ≤ (e k : ℤ) - (v k : ℤ)
      · exfalso
        obtain ⟨k, hk⟩ := not_forall.mp hnotpoint
        have hltNat : e k < v k := Nat.lt_of_not_ge hk
        have hlt : (e k : ℤ) - (v k : ℤ) < 0 := by omega
        have := hnonneg k
        omega
      · change (if ∀ k, 0 ≤ (e k : ℤ) - (v k : ℤ) then
          coordinateAtomMass β ν (fun k ↦ (e k : ℤ) - (v k : ℤ)) else 0) = 0
        exact ite_eq_right hnonneg
    simp [hle, hzero]

/-- Every coefficient of the endpoint-denominator convolution is the endpoint discrepancy of the
positive-orthant atom weights, on the matching total-degree fiber. -/
theorem weakTilingEndpointConvolution_coeff {ι : Type*} [Fintype ι] {n : ℕ}
    (p q : Fin n → ι → ℕ) (β : ι → ℝ) (ν : Measure ℝ)
    (d : ℕ) (e : ι →₀ ℕ) :
    (∑ ij ∈ antidiagonal d,
      (weakTilingEndpointDenominator p q).coeff ij.1 *
        weakTilingCoordinateRow β ν ij.2).coeff e =
      if coordinateExponentDegree e = d then
        (endpointShiftDifference p q (coordinateAtomPositivePart β ν)
          (fun k ↦ (e k : ℤ)) : ℂ) else 0 := by
  classical
  rw [weakTilingEndpointDenominator_antidiagonal]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_sub]
  simp_rw [endpointFunctionMonomialRow_coeff]
  by_cases hd : coordinateExponentDegree e = d
  · simp [hd, endpointShiftDifference, endpointShiftSum, Complex.ofReal_sum]
    rfl
  · simp [hd]

/-- The finite endpoint-overlap numerator is supported only on nonnegative lattice points. -/
theorem weakTilingEndpointOverlapFinsupp_support_nonneg {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (g : lengthSet A B → ι → ℕ) (hβpos : ∀ k, 0 < β k)
    (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k)
    (u : ι → ℤ)
    (hu : u ∈ (weakTiling_endpointOverlapFinsupp hn A B hAB hord hν β g
      hβpos hβind hgen hcoordpos).support) :
    ∀ k, 0 ≤ u k := by
  classical
  have huval : endpointShiftDifference
      (leftEndpointCoordinateVector A B hn β g)
      (rightEndpointCoordinateVector A B hn β g)
      (coordinateAtomPositivePart β ν) u ≠ 0 := by
    simpa only [Finsupp.mem_support_iff, weakTiling_endpointOverlapFinsupp_apply] using hu
  have hvanish := weakTiling_endpointDifference_vanishes_outside_box
    hn A B hAB hord hν β g hβpos hβind hgen hcoordpos
  have hbox : u ∈ endpointCoordinateBox
      (endpointShiftBoxBound (rightEndpointCoordinateVector A B hn β g)) := by
    by_contra hnot
    exact huval (hvanish u hnot)
  intro k
  exact (hbox k).1

/-- The actual finite numerator obtained from the endpoint discrepancy of `δ₀ + ν`. -/
noncomputable def weakTilingEndpointNumerator {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (g : lengthSet A B → ι → ℕ) (hβpos : ∀ k, 0 < β k)
    (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) :
    Polynomial (MvPolynomial ι ℂ) :=
  integerLatticeFinsuppPolynomial
    (weakTiling_endpointOverlapFinsupp hn A B hAB hord hν β g
      hβpos hβind hgen hcoordpos)

/-- The numerator coefficients are exactly the finite endpoint discrepancy supplied by the
weak-tiling recurrence. -/
theorem weakTilingEndpointNumerator_coeff {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (g : lengthSet A B → ι → ℕ) (hβpos : ∀ k, 0 < β k)
    (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k)
    (d : ℕ) (e : ι →₀ ℕ) :
    ((weakTilingEndpointNumerator hn A B hAB hord hν β g
      hβpos hβind hgen hcoordpos).coeff d).coeff e =
      if coordinateExponentDegree e = d then
        (endpointShiftDifference
          (leftEndpointCoordinateVector A B hn β g)
          (rightEndpointCoordinateVector A B hn β g)
          (coordinateAtomPositivePart β ν) (fun k ↦ (e k : ℤ)) : ℂ) else 0 := by
  classical
  let c := weakTiling_endpointOverlapFinsupp hn A B hAB hord hν β g
    hβpos hβind hgen hcoordpos
  have hc : ∀ u ∈ c.support, ∀ k, 0 ≤ u k := by
    intro u hu k
    exact weakTilingEndpointOverlapFinsupp_support_nonneg hn A B hAB hord hν
      β g hβpos hβind hgen hcoordpos u (by simpa [c] using hu) k
  have hcoeff := integerLatticeFinsuppPolynomial_coeff c hc d e
  simpa [weakTilingEndpointNumerator, c,
    weakTiling_endpointOverlapFinsupp_apply] using hcoeff

/-- The actual positive-coordinate rows satisfy the finite-polynomial generating identity, with
the finite endpoint-overlap polynomial as numerator. -/
theorem weakTilingEndpointGeneratingIdentity {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (g : lengthSet A B → ι → ℕ) (hβpos : ∀ k, 0 < β k)
    (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) (d : ℕ) :
    (∑ ij ∈ antidiagonal d,
      (weakTilingEndpointDenominator
        (leftEndpointCoordinateVector A B hn β g)
        (rightEndpointCoordinateVector A B hn β g)).coeff ij.1 *
        weakTilingCoordinateRow β ν ij.2) =
      (weakTilingEndpointNumerator hn A B hAB hord hν β g
        hβpos hβind hgen hcoordpos).coeff d := by
  classical
  apply MvPolynomial.ext
  intro e
  rw [weakTilingEndpointConvolution_coeff, weakTilingEndpointNumerator_coeff]

/-- Every interval endpoint shift strictly raises the total coordinate degree. -/
theorem weakTiling_endpointDegrees_strict {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (g : lengthSet A B → ι → ℕ) (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) (j : Fin n) :
    coordinateFunctionDegree (leftEndpointCoordinateVector A B hn β g j) <
      coordinateFunctionDegree (rightEndpointCoordinateVector A B hn β g j) := by
  classical
  have hι : Nonempty ι := by
    by_contra hne
    haveI : IsEmpty ι := not_nonempty_iff.mp hne
    let j₀ : Fin n := ⟨0, hn⟩
    let ℓ : lengthSet A B := ⟨B j₀ - A j₀,
      Finset.mem_image.mpr ⟨j₀, Finset.mem_univ _, rfl⟩⟩
    have hℓpos : 0 < (ℓ : ℝ) := by
      dsimp [ℓ]
      exact sub_pos.mpr (hAB j₀)
    rw [hgen ℓ] at hℓpos
    simp at hℓpos
  have hcoord := intervalEndpointCoordinates_strict hn A B hAB hord hν β g
    hβind hgen hcoordpos
  have hsum : (∑ k, (leftEndpointCoordinateVector A B hn β g j k + 1)) ≤
      ∑ k, rightEndpointCoordinateVector A B hn β g j k := by
    apply Finset.sum_le_sum
    intro k hk
    have hk'' : rightEndpointCoordinateVector A B hn β g j k ≥
        leftEndpointCoordinateVector A B hn β g j k + 1 := by
      simpa [leftEndpointCoordinateVector, rightEndpointCoordinateVector] using hcoord j k
    exact hk''
  have hsum' : (∑ k, leftEndpointCoordinateVector A B hn β g j k) +
      Fintype.card ι ≤ ∑ k, rightEndpointCoordinateVector A B hn β g j k := by
    simpa [Finset.sum_add_distrib] using hsum
  have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hι
  unfold coordinateFunctionDegree
  omega

/-- Strict increase at every endpoint makes the sum of the left endpoint degrees strictly smaller
than the sum of the right endpoint degrees. -/
theorem endpointDegreeSum_strict {n : ℕ} (hn : 0 < n) (p q : Fin n → ℕ)
    (hdeg : ∀ j, p j < q j) : (∑ j, p j) < ∑ j, q j := by
  have hsum : (∑ j : Fin n, (p j + 1)) ≤ ∑ j, q j := by
    apply Finset.sum_le_sum
    intro j hj
    exact Nat.succ_le_of_lt (hdeg j)
  have hsum' : (∑ j : Fin n, p j) + n ≤ ∑ j, q j := by
    simpa [Finset.sum_add_distrib] using hsum
  omega

/-- The univariate specialization of the endpoint denominator is strictly positive on `(0,1)`. -/
theorem weakTilingEndpointDenominator_eval_pos {ι : Type*} [Fintype ι] {n : ℕ}
    (hn : 0 < n) (p q : Fin n → ι → ℕ)
    (hdeg : ∀ j, coordinateFunctionDegree (p j) < coordinateFunctionDegree (q j))
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < (((weakTilingEndpointDenominator p q).map
      (MvPolynomial.eval fun _ ↦ (1 : ℂ))).eval (x : ℂ)).re := by
  rw [weakTilingEndpointDenominator_map_eval_one]
  have hterm (j : Fin n) :
      0 < x ^ coordinateFunctionDegree (p j) - x ^ coordinateFunctionDegree (q j) := by
    let a := coordinateFunctionDegree (p j)
    let b := coordinateFunctionDegree (q j)
    have hab : a < b := hdeg j
    have hr : 0 < b - a := Nat.sub_pos_of_lt hab
    have hpow : x ^ b = x ^ a * x ^ (b - a) := by
      calc
        x ^ b = x ^ (a + (b - a)) := by rw [Nat.add_sub_of_le (Nat.le_of_lt hab)]
        _ = x ^ a * x ^ (b - a) := by rw [pow_add]
    have hpowlt : x ^ (b - a) < 1 := pow_lt_one₀ hx0.le hx1 hr.ne'
    rw [hpow]
    calc
      x ^ a - x ^ a * x ^ (b - a) = x ^ a * (1 - x ^ (b - a)) := by ring
      _ > 0 := mul_pos (pow_pos hx0 a) (sub_pos.mpr hpowlt)
  have hsum : 0 < ∑ j : Fin n,
      (x ^ coordinateFunctionDegree (p j) - x ^ coordinateFunctionDegree (q j)) := by
    apply Finset.sum_pos (fun j _ ↦ hterm j)
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have heval :
      (((∑ j : Fin n,
          (Polynomial.monomial (coordinateFunctionDegree (p j)) (1 : ℂ) -
            Polynomial.monomial (coordinateFunctionDegree (q j)) (1 : ℂ))).eval (x : ℂ)).re) =
        ∑ j : Fin n,
          (x ^ coordinateFunctionDegree (p j) - x ^ coordinateFunctionDegree (q j)) := by
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_sub, Polynomial.eval_monomial, one_mul]
    simp only [Complex.re_sum, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [heval]
  exact hsum

/-- The derivative of the specialized endpoint denominator at one is the strict negative degree
sum difference, so its zero there is simple. -/
theorem weakTilingEndpointDenominator_derivative_eval_one_ne_zero
    {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (p q : Fin n → ι → ℕ)
    (hdeg : ∀ j, coordinateFunctionDegree (p j) < coordinateFunctionDegree (q j)) :
    (Polynomial.derivative ((weakTilingEndpointDenominator p q).map
      (MvPolynomial.eval fun _ ↦ (1 : ℂ)))).eval 1 ≠ 0 := by
  have hsum : (∑ j : Fin n, coordinateFunctionDegree (p j)) <
      ∑ j : Fin n, coordinateFunctionDegree (q j) :=
    endpointDegreeSum_strict hn (fun j ↦ coordinateFunctionDegree (p j))
      (fun j ↦ coordinateFunctionDegree (q j)) hdeg
  have hformula :
      (Polynomial.derivative
        (∑ j : Fin n,
          (Polynomial.monomial (coordinateFunctionDegree (p j)) (1 : ℂ) -
            Polynomial.monomial (coordinateFunctionDegree (q j)) (1 : ℂ)))).eval 1 =
        (∑ j : Fin n, (coordinateFunctionDegree (p j) : ℂ)) -
          (∑ j : Fin n, (coordinateFunctionDegree (q j) : ℂ)) := by
    simp [Polynomial.derivative_sub,
      Polynomial.derivative_monomial, Polynomial.eval_sub, Polynomial.eval_monomial,
      Polynomial.eval_finsetSum, Finset.sum_sub_distrib]
  rw [weakTilingEndpointDenominator_map_eval_one, hformula]
  apply sub_ne_zero.mpr
  exact_mod_cast (Nat.ne_of_lt hsum)

/-- A strictly positive real part of the specialization certifies that the complex value is
nonzero. -/
theorem weakTilingEndpointDenominator_eval_ne_zero {ι : Type*} [Fintype ι] {n : ℕ}
    (hn : 0 < n) (p q : Fin n → ι → ℕ)
    (hdeg : ∀ j, coordinateFunctionDegree (p j) < coordinateFunctionDegree (q j))
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (((weakTilingEndpointDenominator p q).map
      (MvPolynomial.eval fun _ ↦ (1 : ℂ))).eval (x : ℂ)) ≠ 0 := by
  have hpos := weakTilingEndpointDenominator_eval_pos hn p q hdeg hx0 hx1
  intro hzero
  have hreal :
      (((weakTilingEndpointDenominator p q).map
        (MvPolynomial.eval fun _ ↦ (1 : ℂ))).eval (x : ℂ)).re = 0 := by
    simp [hzero]
  rw [hreal] at hpos
  exact (lt_irrefl 0 hpos)

/-- The positive orthant of the actual normalized atom masses is packaged as generating data with
the endpoint denominator and the finite-overlap numerator. -/
noncomputable def weakTilingPositiveGeneratingData {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (g : lengthSet A B → ι → ℕ) (hβpos : ∀ k, 0 < β k)
    (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) :
    GeneratingData ι := by
  classical
  let p : Fin n → ι → ℕ := leftEndpointCoordinateVector A B hn β g
  let q : Fin n → ι → ℕ := rightEndpointCoordinateVector A B hn β g
  have hdeg : ∀ j, coordinateFunctionDegree (p j) < coordinateFunctionDegree (q j) := by
    intro j
    simpa [p, q] using weakTiling_endpointDegrees_strict hn A B hAB hord hν
      β g hβind hgen hcoordpos j
  refine
    { rows := weakTilingCoordinateRow β ν
      P := weakTilingEndpointDenominator p q
      R := weakTilingEndpointNumerator hn A B hAB hord hν β g
        hβpos hβind hgen hcoordpos
      identity := ?_
      nonneg := ?_
      spec_ne_zero := ?_
      no_zero_in_unit_interval := ?_
      simple_zero_at_one := ?_ }
  · intro d
    simpa [p, q] using weakTilingEndpointGeneratingIdentity hn A B hAB hord hν
      β g hβpos hβind hgen hcoordpos d
  · intro d e
    exact weakTilingCoordinateRow_nonneg β ν d e
  · intro hzero
    have hhalf := weakTilingEndpointDenominator_eval_ne_zero hn p q hdeg
      (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    apply hhalf
    rw [hzero]
    simp
  · intro x hx0 hx1
    exact weakTilingEndpointDenominator_eval_ne_zero hn p q hdeg hx0 hx1
  · intro hzero
    exact weakTilingEndpointDenominator_derivative_eval_one_ne_zero hn p q hdeg

/-- The Wiener norms of the actual nonnegative-coordinate rows are uniformly bounded by the
generating-data pole argument. -/
theorem weakTiling_positiveCoordinateRows_norm_bounded {n : ℕ} (hn : 0 < n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i < B i)
    (hord : ∀ i j : Fin n, i < j → B i < A j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo A B) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (g : lengthSet A B → ι → ℕ) (hβpos : ∀ k, 0 < β k)
    (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) :
    ∃ C : ℝ, ∀ d, mvNorm1 (weakTilingCoordinateRow β ν d) ≤ C := by
  change ∃ C : ℝ, ∀ d,
    mvNorm1 ((weakTilingPositiveGeneratingData hn A B hAB hord hν β g
      hβpos hβind hgen hcoordpos).rows d) ≤ C
  exact GeneratingData.rowNorm_bounded
    (weakTilingPositiveGeneratingData hn A B hAB hord hν β g
      hβpos hβind hgen hcoordpos)

end WeakTiling

end

end MeasureGeneratingData

/-! ## The negative side by reflection -/

section NegativeSide

section

open MeasureTheory Set

namespace WeakTiling

variable {n : ℕ} {a b : Fin n → ℝ}

theorem reflTranslate_preimage_neg (Ω : Set ℝ) (x : ℝ) :
    Neg.neg ⁻¹' reflTranslate (Neg.neg ⁻¹' Ω) x = reflTranslate Ω (-x) := by
  ext t
  show -(x - -t) ∈ Ω ↔ -x - t ∈ Ω
  rw [show -(x - -t) = -x - t by ring]

theorem isLocallyFiniteMeasure_map_neg (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (ν.map Neg.neg) :=
  ⟨fun x ↦ ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), by
    rw [Measure.map_apply measurable_neg measurableSet_Ioo]
    exact (measure_mono fun t (ht : -t ∈ Ioo (x - 1) (x + 1)) ↦
      (⟨by linarith [ht.2], by linarith [ht.1]⟩ : t ∈ Ioo (-x - 1) (-x + 1))).trans_lt
      measure_Ioo_lt_top⟩⟩

/-- **Reflection of a weak tiling.** -/
theorem IsWeakTilingMeasure.neg {Ω : Set ℝ} {ν : Measure ℝ} (h : IsWeakTilingMeasure Ω ν) :
    IsWeakTilingMeasure (Neg.neg ⁻¹' Ω) (ν.map Neg.neg) := by
  obtain ⟨hbd, hmeas, hlf, hae⟩ := h
  have hmeas' : MeasurableSet (Neg.neg ⁻¹' Ω) := measurable_neg hmeas
  refine ⟨?_, hmeas', isLocallyFiniteMeasure_map_neg ν, ?_⟩
  · obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hbd
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨r, fun t ht ↦ ?_⟩
    have := hr ht
    rwa [mem_closedBall_zero_iff, norm_neg, ← mem_closedBall_zero_iff] at this
  · have hae' :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hae
    filter_upwards [hae'] with x hx
    rw [integral_indicator_translate hmeas', Measure.map_apply measurable_neg
      (measurableSet_reflTranslate hmeas' x), reflTranslate_preimage_neg,
      ← integral_indicator_translate hmeas ν (-x), hx]
    by_cases hxΩ : -x ∈ Ω <;> simp [hxΩ]

/-- Left endpoints of the reflected union. -/
def reflA (_a b : Fin n → ℝ) : Fin n → ℝ := fun i ↦ -b (Fin.rev i)

/-- Right endpoints of the reflected union. -/
def reflB (a _b : Fin n → ℝ) : Fin n → ℝ := fun i ↦ -a (Fin.rev i)

theorem reflA_lt_reflB (hab : ∀ i, a i < b i) (i : Fin n) : reflA a b i < reflB a b i :=
  neg_lt_neg (hab _)

theorem reflB_lt_reflA (hord : ∀ i j : Fin n, i < j → b i < a j) (i j : Fin n) (hij : i < j) :
    reflB a b i < reflA a b j :=
  neg_lt_neg (hord _ _ (Fin.rev_lt_rev.mpr hij))

theorem unionIoo_refl : unionIoo (reflA a b) (reflB a b) = Neg.neg ⁻¹' unionIoo a b := by
  ext t
  simp only [unionIoo, mem_iUnion, mem_preimage, mem_Ioo, reflA, reflB]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨Fin.rev i, by linarith, by linarith⟩
  · rintro ⟨i, h1, h2⟩
    exact ⟨Fin.rev i, by rw [Fin.rev_rev]; linarith, by rw [Fin.rev_rev]; linarith⟩

theorem lengthSet_refl : lengthSet (reflA a b) (reflB a b) = lengthSet a b := by
  ext l
  simp only [lengthSet, Finset.mem_image, Finset.mem_univ, true_and, reflA, reflB]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.rev i, by ring⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.rev i, by rw [Fin.rev_rev]; ring⟩

/-- The reflected measure is a weak tiling of the reflected ordered union. -/
theorem IsWeakTilingMeasure.refl {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo a b) ν) :
    IsWeakTilingMeasure (unionIoo (reflA a b) (reflB a b)) (ν.map Neg.neg) := by
  rw [unionIoo_refl]
  exact hν.neg

/-- **Step W on the negative side.**  The coordinate rows of the reflected measure have uniformly
bounded Wiener norms. The coordinates are the same as on the positive side. -/
theorem weakTiling_negativeCoordinateRows_norm_bounded (hn : 0 < n)
    (hab : ∀ i, a i < b i) (hord : ∀ i j : Fin n, i < j → b i < a j)
    {ν : Measure ℝ} (hν : IsWeakTilingMeasure (unionIoo a b) ν)
    {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (g : lengthSet a b → ι → ℕ) (hβpos : ∀ k, 0 < β k)
    (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet a b, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet a b, ∀ k, 1 ≤ g l k) :
    ∃ C : ℝ, ∀ d, mvNorm1 (weakTilingCoordinateRow β (ν.map Neg.neg) d) ≤ C := by
  have hmem : ∀ l : lengthSet (reflA a b) (reflB a b), (l : ℝ) ∈ lengthSet a b :=
    fun l ↦ lengthSet_refl (a := a) (b := b) ▸ l.2
  exact weakTiling_positiveCoordinateRows_norm_bounded hn (reflA a b) (reflB a b)
    (reflA_lt_reflB hab) (reflB_lt_reflA hord) hν.refl β (fun l ↦ g ⟨l, hmem l⟩) hβpos hβind
    (fun l ↦ hgen ⟨l, hmem l⟩) (fun l ↦ hcoordpos ⟨l, hmem l⟩)

end WeakTiling

end

end NegativeSide

/-! ## Step 0: the lattice interface for steps H and A -/

section LatticeCore

section

open MeasureTheory Set

namespace WeakTiling

theorem mem_support_of_measure_singleton_ne_zero {ν : Measure ℝ} {s : ℝ} (hs : ν {s} ≠ 0) :
    s ∈ ν.support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hs)
    (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

theorem measure_singleton_eq_zero_of_notMem_support {ν : Measure ℝ} {s : ℝ}
    (hs : s ∉ ν.support) : ν {s} = 0 := by
  by_contra h
  exact hs (mem_support_of_measure_singleton_ne_zero h)

/-- **Every support point of a weak tiling measure is an atom.** -/
theorem weakTiling_support_atom {n : ℕ} {a b : Fin n → ℝ} (hab : ∀ i, a i < b i)
    (hord : ∀ i j : Fin n, i < j → b i < a j) {ν : Measure ℝ}
    (hν : IsWeakTilingMeasure (unionIoo a b) ν) {z : ℝ} (hz : z ∈ ν.support) : ν {z} ≠ 0 := by
  have : IsLocallyFiniteMeasure ν := hν.2.2.1
  have := isLocallyFiniteMeasure_dirac_add ν
  obtain ⟨j0⟩ := exists_component (weakTiling_normalized hν)
  have hn : 0 < n := Fin.pos j0
  obtain ⟨-, hpp⟩ := weakTiling_eq_purePoint hab hord hν
  have hsub : atomSet ν ⊆
      {z | InSemigroupL (lengthSet a b) z ∨ InSemigroupL (lengthSet a b) (-z)} :=
    fun s hs ↦ weakTiling_support_subset hab hord hν (mem_support_of_measure_singleton_ne_zero hs)
  have hcl : closure (Set.range fun k : atomSet ν ↦ (k : ℝ)) ⊆ atomSet ν := by
    refine closure_subset_of_locallyFinite (by rintro _ ⟨k, rfl⟩; exact k.2) fun x ↦ ?_
    refine (signedSemigroup_finite _ (minLength_pos hn hab) (fun l hl ↦ ?_) x).subset
      (inter_subset_inter_left _ hsub)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hl
    exact minLength_le hn i
  have hsupp := support_purePoint_subset (fun k : atomSet ν ↦ (k : ℝ))
    fun k ↦ (ν {(k : ℝ)}).toReal
  rw [← hpp] at hsupp
  exact hcl (hsupp hz)

/-- Support points of a weak tiling measure carry positive finite mass. -/
theorem weakTiling_support_toReal_pos {n : ℕ} {a b : Fin n → ℝ} (hab : ∀ i, a i < b i)
    (hord : ∀ i j : Fin n, i < j → b i < a j) {ν : Measure ℝ}
    (hν : IsWeakTilingMeasure (unionIoo a b) ν) {z : ℝ} (hz : z ∈ ν.support) :
    0 < (ν {z}).toReal := by
  have : IsLocallyFiniteMeasure ν := hν.2.2.1
  exact ENNReal.toReal_pos (weakTiling_support_atom hab hord hν hz)
    isCompact_singleton.measure_lt_top.ne

theorem coordinateAtomMass_map_neg {ι : Type*} [Fintype ι] (β : ι → ℝ) (ν : Measure ℝ)
    (u : ι → ℤ) : coordinateAtomMass β (ν.map Neg.neg) u = coordinateAtomMass β ν (-u) := by
  unfold coordinateAtomMass
  rw [Measure.map_apply measurable_neg (measurableSet_singleton _)]
  have h1 : Neg.neg ⁻¹' {coordinateValueInt β u} = {coordinateValueInt β (-u)} := by
    ext t
    simp only [mem_preimage, mem_singleton_iff, coordinateValueInt, Pi.neg_apply, Int.cast_neg,
      neg_mul, Finset.sum_neg_distrib]
    constructor <;> intro h <;> linarith
  rw [h1]
  by_cases hu : u = 0 <;> simp [hu]

theorem coordinateAtomMass_ge_toReal {ι : Type*} [Fintype ι] (β : ι → ℝ) (ν : Measure ℝ)
    (u : ι → ℤ) : (ν {coordinateValueInt β u}).toReal ≤ coordinateAtomMass β ν u := by
  unfold coordinateAtomMass
  exact le_add_of_nonneg_right (by split_ifs <;> norm_num)

theorem sum_norm_coeff_le_mvNorm1 {σ : Type*} (g : MvPolynomial σ ℂ) (T : Finset (σ →₀ ℕ)) :
    ∑ s ∈ T, ‖g.coeff s‖ ≤ mvNorm1 g := by
  classical
  rw [← Finset.sum_filter_ne_zero]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ norm_nonneg _
  intro s hs
  rw [Finset.mem_filter] at hs
  exact MvPolynomial.mem_support_iff.mpr fun h ↦ hs.2 (by rw [h, norm_zero])

/-- A finite part of one row is bounded by the Wiener norm of the row. -/
theorem sum_coordinateAtomMass_le_mvNorm1 {ι : Type*} [Fintype ι] (β : ι → ℝ) (ν : Measure ℝ)
    (d : ℕ) (S : Finset (ι → ℕ)) (hS : ∀ e ∈ S, ∑ k, e k = d) :
    ∑ e ∈ S, coordinateAtomMass β ν (fun k ↦ (e k : ℤ)) ≤
      mvNorm1 (weakTilingCoordinateRow β ν d) := by
  classical
  calc ∑ e ∈ S, coordinateAtomMass β ν (fun k ↦ (e k : ℤ))
      = ∑ e ∈ S, ‖(weakTilingCoordinateRow β ν d).coeff (coordinateFunctionExponent e)‖ := by
        refine Finset.sum_congr rfl fun e he ↦ ?_
        have hdeg : coordinateExponentDegree (coordinateFunctionExponent e) = d := by
          rw [coordinateFunctionExponent_degree]
          exact hS e he
        rw [weakTilingCoordinateRow_coeff, ite_eq_left hdeg]
        simp only [coordinateFunctionExponent_apply]
        rw [Complex.norm_real, Real.norm_of_nonneg (coordinateAtomMass_nonneg β ν _)]
    _ = ∑ s ∈ S.image coordinateFunctionExponent,
          ‖(weakTilingCoordinateRow β ν d).coeff s‖ := by
        rw [Finset.sum_image]
        intro x _ y _ h
        funext k
        simpa using congrArg (fun f : ι →₀ ℕ ↦ f k) h
    _ ≤ _ := sum_norm_coeff_le_mvNorm1 _ _

/-- **The coordinate-lattice form of a weak tiling.**  `M u` is the normalized atom mass of
`δ₀ + ν` at the lattice point `u`, and `p j, q j` are the coordinates of the endpoints `aⱼ - a₀`
and `bⱼ - a₀`.  With `P = ∑ⱼ (z^{pⱼ} - z^{qⱼ})`, `balance` says `P · M = 0`.  Together with
`orthants` this gives `P F₊ = R = -P F₋` for a polynomial `R` with finite support. -/
structure LatticeTilingData (ι : Type) [Fintype ι] where
  /-- Number of intervals. -/
  n : ℕ
  n_pos : 0 < n
  /-- Coordinates of the left endpoints, relative to the first one. -/
  p : Fin n → ι → ℕ
  /-- Coordinates of the right endpoints, relative to the first left endpoint. -/
  q : Fin n → ι → ℕ
  p_zero : p ⟨0, n_pos⟩ = 0
  endpoint_lt : ∀ j k, p j k < q j k
  /-- Normalized atom masses on the coordinate lattice. -/
  M : (ι → ℤ) → ℝ
  nonneg : ∀ u, 0 ≤ M u
  zero : M 0 = 1
  balance : ∀ u, ∑ j, M (u - fun k ↦ (p j k : ℤ)) = ∑ j, M (u - fun k ↦ (q j k : ℤ))
  orthants : ∀ u, M u ≠ 0 → u = 0 ∨ (∀ k, 1 ≤ u k) ∨ (∀ k, u k ≤ -1)
  /-- Rows of total degree `d` on the positive side have uniformly bounded mass. -/
  rows_pos : ∃ C : ℝ, ∀ (d : ℕ) (S : Finset (ι → ℕ)), (∀ e ∈ S, ∑ k, e k = d) →
    ∑ e ∈ S, M (fun k ↦ (e k : ℤ)) ≤ C
  /-- Rows of total degree `d` on the reflected negative side have uniformly bounded mass. -/
  rows_neg : ∃ C : ℝ, ∀ (d : ℕ) (S : Finset (ι → ℕ)), (∀ e ∈ S, ∑ k, e k = d) →
    ∑ e ∈ S, M (fun k ↦ -(e k : ℤ)) ≤ C

/-- The lattice ray `w + ℕ v`. -/
def latticeRay {ι : Type*} (w : ι → ℤ) (v : ι → ℕ) : Set (ι → ℤ) :=
  {u | ∃ m : ℕ, u = w + fun k ↦ (m : ℤ) * v k}

/-- Finitely many exceptional points and finitely many lattice rays with nonzero directions. -/
def HasFiniteLatticeRayCover {ι : Type*} (S : Set (ι → ℤ)) : Prop :=
  ∃ (E : Set (ι → ℤ)) (J : ℕ) (w : Fin J → ι → ℤ) (v : Fin J → ι → ℕ),
    E.Finite ∧ (∀ j, v j ≠ 0) ∧ S ⊆ E ∪ ⋃ j, latticeRay (w j) (v j)

/-- **Steps H and A as one lattice statement.**  The positive part and the reflected negative part
of the support of every lattice tiling datum have finite lattice-ray covers. -/
def LatticeCoreHypothesis : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : LatticeTilingData ι),
    HasFiniteLatticeRayCover {u | (∀ k, 0 ≤ u k) ∧ D.M u ≠ 0} ∧
    HasFiniteLatticeRayCover {u | (∀ k, 0 ≤ u k) ∧ D.M (-u) ≠ 0}

/-- **Every weak tiling produces lattice tiling data**, with the atom masses of `ν` itself. -/
theorem exists_latticeTilingData {n : ℕ} (hn : 0 < n) {A B : Fin n → ℝ}
    (hAB : ∀ i, A i < B i) (hord : ∀ i j : Fin n, i < j → B i < A j) {ν : Measure ℝ}
    (hν : IsWeakTilingMeasure (unionIoo A B) ν) {ι : Type} [Fintype ι] (β : ι → ℝ)
    (g : lengthSet A B → ι → ℕ) (hβpos : ∀ k, 0 < β k) (hβind : LinearIndependent ℚ β)
    (hgen : ∀ l : lengthSet A B, (l : ℝ) = ∑ k, (g l k : ℝ) * β k)
    (hcoordpos : ∀ l : lengthSet A B, ∀ k, 1 ≤ g l k) :
    ∃ D : LatticeTilingData ι, D.M = coordinateAtomMass β ν := by
  classical
  obtain ⟨Cp, hCp⟩ := weakTiling_positiveCoordinateRows_norm_bounded hn A B hAB hord hν β g
    hβpos hβind hgen hcoordpos
  obtain ⟨Cn, hCn⟩ := weakTiling_negativeCoordinateRows_norm_bounded hn hAB hord hν β g
    hβpos hβind hgen hcoordpos
  have hopen : IsOpen (unionIoo A B) := isOpen_iUnion fun i ↦ isOpen_Ioo
  have hne : (unionIoo A B).Nonempty :=
    ⟨(A ⟨0, hn⟩ + B ⟨0, hn⟩) / 2, mem_iUnion.mpr ⟨⟨0, hn⟩, by
      constructor <;> linarith [hAB ⟨0, hn⟩]⟩⟩
  have hzero : ν {0} = 0 :=
    measure_singleton_eq_zero_of_notMem_support (zero_notMem_support hν hopen hne)
  refine ⟨{
      n := n
      n_pos := hn
      p := leftEndpointCoordinateVector A B hn β g
      q := rightEndpointCoordinateVector A B hn β g
      p_zero := ?_
      endpoint_lt := ?_
      M := coordinateAtomMass β ν
      nonneg := coordinateAtomMass_nonneg β ν
      zero := ?_
      balance := ?_
      orthants := ?_
      rows_pos := ⟨Cp, ?_⟩
      rows_neg := ⟨Cn, ?_⟩ }, rfl⟩
  · have hz : InSemigroupL (lengthSet A B) (A ⟨0, hn⟩ - A ⟨0, hn⟩) := by
      rw [sub_self]
      exact InSemigroupL.zero _
    have hrep := coordVectorOfSemigroup_repr (lengthSet A B) β g hgen hz
    show coordVectorOfSemigroup (lengthSet A B) β g (A ⟨0, hn⟩ - A ⟨0, hn⟩) = 0
    exact coordVector_unique β hβind (by rw [← hrep, sub_self]; simp)
  · exact fun j k ↦ intervalEndpointCoordinates_strict hn A B hAB hord hν β g hβind hgen
      hcoordpos j k
  · simp [coordinateAtomMass, coordinateValueInt, hzero]
  · exact fun u ↦ weakTiling_lengthCoordinate_measure_balance hn A B hAB hord hν β g hβind
      hgen u
  · intro u hu
    by_cases hu0 : u = 0
    · exact Or.inl hu0
    right
    have hmass : coordinateAtomMass β ν u = (ν {coordinateValueInt β u}).toReal := by
      simp [coordinateAtomMass, hu0]
    rw [hmass] at hu
    exact weakTiling_coordinate_support_strict_orthants hn hAB hord hν β g hβpos hβind hgen
      hcoordpos (mem_support_of_singleton_toReal_pos ν _
        (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hu)))
  · intro d S hS
    exact (sum_coordinateAtomMass_le_mvNorm1 β ν d S hS).trans (hCp d)
  · intro d S hS
    refine le_trans (le_of_eq ?_)
      ((sum_coordinateAtomMass_le_mvNorm1 β (ν.map Neg.neg) d S hS).trans (hCn d))
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [coordinateAtomMass_map_neg]
    rfl

theorem coordinateValueInt_ray {ι : Type*} [Fintype ι] (β : ι → ℝ) (w : ι → ℤ) (v : ι → ℕ)
    (m : ℕ) :
    coordinateValueInt β (w + fun k ↦ (m : ℤ) * v k) =
      coordinateValueInt β w + (m : ℝ) * coordinateValueInt β (fun k ↦ (v k : ℤ)) := by
  simp only [coordinateValueInt, Pi.add_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ ↦ by ring

theorem coordinateValueInt_pos {ι : Type*} [Fintype ι] {β : ι → ℝ} (hβpos : ∀ k, 0 < β k)
    {v : ι → ℕ} (hv : v ≠ 0) : 0 < coordinateValueInt β (fun k ↦ (v k : ℤ)) := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  rw [coordinateValueInt_nat]
  refine Finset.sum_pos' (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (hβpos j).le)
    ⟨k, Finset.mem_univ k, mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)) (hβpos k)⟩

/-- **Lattice rays give real arithmetic rays** under a positive coordinate map. -/
theorem hasFiniteLaurentRayCover_of_lattice {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (hβpos : ∀ k, 0 < β k) {S : Set (ι → ℤ)} (hS : HasFiniteLatticeRayCover S) {Λ : Set ℝ}
    (hΛ : ∀ z ∈ Λ, ∃ u ∈ S, z = coordinateValueInt β u) : HasFiniteLaurentRayCover Λ := by
  classical
  obtain ⟨E, J, w, v, hE, hv, hcov⟩ := hS
  refine ⟨coordinateValueInt β '' E, J, fun j ↦ {coordinateValueInt β (w j)},
    fun j ↦ coordinateValueInt β (fun k ↦ (v j k : ℤ)), hE.image _,
    fun j ↦ coordinateValueInt_pos hβpos (hv j), fun z hz ↦ ?_⟩
  obtain ⟨u, hu, rfl⟩ := hΛ z hz
  rcases hcov hu with huE | huR
  · exact Or.inl ⟨u, huE, rfl⟩
  · obtain ⟨j, m, rfl⟩ := mem_iUnion.mp huR
    refine Or.inr (mem_iUnion.mpr ⟨⟨j, ⟨coordinateValueInt β (w j), Finset.mem_singleton_self _⟩⟩,
      m, ?_⟩)
    exact coordinateValueInt_ray β (w j) (v j) m

/-- **FC Problem 4.1 from the lattice core hypothesis.**  Everything except steps H and A is a
theorem: coordinates, pure atomicity, the support theorem, the lattice data with bounded rows on
both sides, the passage from lattice rays to real rays, and the exit to bounded density. -/
theorem problem_4_1_of_latticeCore (hcore : LatticeCoreHypothesis) :
    ∀ (Ω : Set ℝ), IsFiniteUnionOfIntervals Ω →
      ∀ (ν : Measure ℝ), IsWeakTilingMeasure Ω ν → HasBoundedDensity ν.support := by
  refine problem_4_1_of_twoSidedLaurentRayCovers fun Ω hΩ ν hν ↦ ?_
  obtain ⟨n, a, b, hab, hord, rfl⟩ := hΩ
  obtain ⟨j0⟩ := exists_component (weakTiling_normalized hν)
  have hn : 0 < n := Fin.pos j0
  obtain ⟨ι, _, β, g, hβpos, hβind, -, hg1, hgen⟩ :=
    exists_positive_integer_coordinates (fun l : lengthSet a b ↦ (l : ℝ))
      fun l ↦ lengthSet_pos hab l.2
  obtain ⟨D, hDM⟩ := exists_latticeTilingData hn hab hord hν β g hβpos hβind hgen hg1
  obtain ⟨hpos, hneg⟩ := hcore ι D
  constructor
  · refine hasFiniteLaurentRayCover_of_lattice β hβpos hpos ?_
    rintro z ⟨hz, hz0⟩
    have hsg := weakTiling_nonnegative_support_mem_semigroup hab hord hν hz hz0
    set u : ι → ℤ := fun k ↦ (coordVectorOfSemigroup (lengthSet a b) β g z k : ℤ)
    have hzu : z = coordinateValueInt β u := by
      rw [coordinateValueInt_nat]
      exact coordVectorOfSemigroup_repr (lengthSet a b) β g hgen hsg
    refine ⟨u, ⟨fun k ↦ Int.natCast_nonneg _, ?_⟩, hzu⟩
    rw [hDM]
    refine (lt_of_lt_of_le ?_ (coordinateAtomMass_ge_toReal β ν u)).ne'
    rw [← hzu]
    exact weakTiling_support_toReal_pos hab hord hν hz
  · refine hasFiniteLaurentRayCover_of_lattice β hβpos hneg ?_
    rintro _ ⟨x, ⟨hx, hx0⟩, rfl⟩
    have hsg := weakTiling_negative_support_reflection_mem_semigroup hab hord hν hx hx0
    set u : ι → ℤ := fun k ↦ (coordVectorOfSemigroup (lengthSet a b) β g (-x) k : ℤ)
    have hxu : -x = coordinateValueInt β u := by
      rw [coordinateValueInt_nat]
      exact coordVectorOfSemigroup_repr (lengthSet a b) β g hgen hsg
    refine ⟨u, ⟨fun k ↦ Int.natCast_nonneg _, ?_⟩, hxu⟩
    rw [hDM]
    refine (lt_of_lt_of_le ?_ (coordinateAtomMass_ge_toReal β ν (-u))).ne'
    have hneg' : coordinateValueInt β (-u) = x := by
      have : coordinateValueInt β (-u) = -coordinateValueInt β u := by
        simp [coordinateValueInt]
      rw [this, ← hxu, neg_neg]
    rw [hneg']
    exact weakTiling_support_toReal_pos hab hord hν hx

/-- **The exact FC answer form, assuming only the lattice form of steps H and A.** -/
theorem problem_4_1_answer_true_of_latticeCore (hcore : LatticeCoreHypothesis) :
    True ↔ ∀ (Ω : Set ℝ) (_ : IsFiniteUnionOfIntervals Ω)
      (ν : Measure ℝ) (_ : IsWeakTilingMeasure Ω ν), HasBoundedDensity ν.support :=
  ⟨fun _ ↦ problem_4_1_of_latticeCore hcore, fun _ ↦ trivial⟩

end WeakTiling

end

end LatticeCore

/-! ## Bounded two-sided solutions of linear recurrences -/

section TwoSidedRecurrence

section

open Polynomial Finset Filter Topology
open scoped fwdDiff

namespace WeakTiling

/-- The shift `f ↦ (x ↦ f (x + 1))` as a `ℂ`-linear endomorphism of `ℂ → ℂ`. -/
def cshift : Module.End ℂ (ℂ → ℂ) where
  toFun f := fun x ↦ f (x + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cshift_apply (f : ℂ → ℂ) (x : ℂ) : cshift f x = f (x + 1) := rfl

theorem cshift_pow_apply (i : ℕ) (f : ℂ → ℂ) (x : ℂ) : (cshift ^ i) f x = f (x + i) := by
  induction i generalizing f x with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Module.End.mul_apply, ih, cshift_apply]
    congr 1
    push_cast
    ring

theorem cshift_sub_one_pow (k : ℕ) (f : ℂ → ℂ) : ((cshift - 1) ^ k) f = (fwdDiff (1 : ℂ))^[k] f := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply']
    funext x
    simp [cshift_apply, fwdDiff]

theorem aeval_cshift_smul_apply (χ : ℂ[X]) (l : ℂ) (f : ℂ → ℂ) (x : ℂ) :
    aeval (l • cshift) χ f x = ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * (l ^ i * f (x + i)) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [LinearMap.smul_apply, _root_.smul_pow, Pi.smul_apply, cshift_pow_apply, smul_eq_mul]

/-- **Polynomial-exponential terms solve the recurrence.**  If `(X - μ)^k ∣ χ` and `deg q < k`, then
`∑ᵢ χᵢ μ^i q(x+i) = 0` for every `x`. -/
theorem sum_coeff_shift_eq_zero (χ : ℂ[X]) {l : ℂ} {k : ℕ} (hdvd : (X - C l) ^ k ∣ χ)
    {q : ℂ[X]} (hq : ∀ j, k ≤ j → q.coeff j = 0) (x : ℂ) :
    ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * (l ^ i * q.eval (x + i)) = 0 := by
  by_cases hq0 : q = 0
  · simp [hq0]
  have hdeg : q.natDegree < k := by
    by_contra h
    exact hq0 (leadingCoeff_eq_zero.mp (hq _ (not_lt.mp h)))
  obtain ⟨ψ, hψ⟩ := hdvd
  have hχ : χ = ψ * (X - C l) ^ k := by rw [hψ, mul_comm]
  have hΔ : aeval (l • cshift) ((X - C l) ^ k) (fun y ↦ q.eval y) = 0 := by
    have hop : aeval (l • cshift) (X - C l) = l • (cshift - 1) := by
      rw [map_sub, aeval_X, aeval_C, smul_sub, Algebra.algebraMap_eq_smul_one]
    rw [map_pow, hop, _root_.smul_pow, LinearMap.smul_apply, cshift_sub_one_pow,
      Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg, smul_zero]
  calc ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * (l ^ i * q.eval (x + i))
      = aeval (l • cshift) χ (fun y ↦ q.eval y) x :=
        (aeval_cshift_smul_apply χ l (fun y ↦ q.eval y) x).symm
    _ = 0 := by
      rw [hχ, map_mul, Module.End.mul_apply, hΔ, map_zero]
      rfl

/-- `a` satisfies `∑ᵢ χᵢ a(m+i) = 0` at every integer `m`. -/
def IsZRecurrence (χ : ℂ[X]) (a : ℤ → ℂ) : Prop :=
  ∀ m : ℤ, ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * a (m + i) = 0

/-- **Uniqueness to the left.**  Two-sided solutions that agree on `ℕ` agree everywhere. -/
theorem eq_of_isZRecurrence (χ : ℂ[X]) (h0 : χ.coeff 0 ≠ 0) {a b : ℤ → ℂ}
    (ha : IsZRecurrence χ a) (hb : IsZRecurrence χ b) (hab : ∀ n : ℕ, a n = b n) : a = b := by
  set e : ℤ → ℂ := fun m ↦ a m - b m with he_def
  have he : ∀ m : ℤ, ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * e (m + i) = 0 := by
    intro m
    simp only [e, mul_sub, sum_sub_distrib, ha m, hb m, sub_zero]
  have key : ∀ N : ℕ, ∀ m : ℤ, -(N : ℤ) ≤ m → e m = 0 := by
    intro N
    induction N with
    | zero =>
      intro m hm
      lift m to ℕ using (by simpa using hm)
      simp [e, hab m]
    | succ N ih =>
      intro m hm
      by_cases hmN : -(N : ℤ) ≤ m
      · exact ih m hmN
      have hrec := he m
      rw [sum_range_succ'] at hrec
      have hrest : ∑ i ∈ range χ.natDegree, χ.coeff (i + 1) * e (m + ((i + 1 : ℕ) : ℤ)) = 0 :=
        sum_eq_zero fun i _ ↦ by
          rw [ih (m + ((i + 1 : ℕ) : ℤ)) (by push_cast at hm ⊢; omega), mul_zero]
      rw [hrest, zero_add] at hrec
      simpa [h0] using hrec
  funext m
  have := key m.natAbs m (by omega)
  simpa [e, sub_eq_zero] using this

theorem tendsto_natCast_pow_div_pow {k K : ℕ} (hk : k < K) :
    Tendsto (fun n : ℕ ↦ (n : ℂ) ^ k / (n : ℂ) ^ K) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  have hsplit : (n : ℝ) ^ K = (n : ℝ) ^ k * (n : ℝ) ^ (K - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk.le]
  rw [hsplit, div_mul_eq_div_div, div_self (pow_ne_zero _ hpos.ne'), one_div]
  exact inv_anti₀ hpos (le_self_pow₀ hn' (by omega))

theorem tendsto_eval_div_pow (q : ℂ[X]) {K : ℕ} (hK : q.natDegree ≤ K) :
    Tendsto (fun n : ℕ ↦ q.eval (n : ℂ) / (n : ℂ) ^ K) atTop (𝓝 (q.coeff K)) := by
  have hrep : ∀ n : ℕ, 1 ≤ n → q.eval (n : ℂ) / (n : ℂ) ^ K =
      q.coeff K + ∑ k ∈ range K, q.coeff k * ((n : ℂ) ^ k / (n : ℂ) ^ K) := by
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hK), sum_range_succ, add_div, sum_div,
      mul_div_assoc (q.coeff K), div_self (pow_ne_zero _ hn0), mul_one, add_comm]
    congr 1
    exact sum_congr rfl fun k _ ↦ mul_div_assoc _ _ _
  have hlim : Tendsto (fun n : ℕ ↦ q.coeff K + ∑ k ∈ range K, q.coeff k * ((n : ℂ) ^ k /
      (n : ℂ) ^ K)) atTop (𝓝 (q.coeff K + ∑ k ∈ range K, q.coeff k * 0)) :=
    tendsto_const_nhds.add (tendsto_finsetSum _ fun k hk ↦
      tendsto_const_nhds.mul (tendsto_natCast_pow_div_pow (mem_range.mp hk)))
  simp only [mul_zero, sum_const_zero, add_zero] at hlim
  exact hlim.congr' (eventually_atTop.mpr ⟨1, fun n hn ↦ (hrep n hn).symm⟩)

/-- **Top coefficients on the outer circle vanish.**  If no component lies outside the circle of
radius `R`, those on it have degree `≤ K`, and the sum divided by `n^K Rⁿ` tends to zero, then
the `K`-th coefficients on the circle vanish. -/
theorem polyExp_top_coeff_eq_zero (S : Finset ℂ) (p : ℂ → ℂ[X]) {R : ℝ} (hR : 0 < R) (K : ℕ)
    (hbig : ∀ μ ∈ S, R < ‖μ‖ → p μ = 0) (hdeg : ∀ μ ∈ S, ‖μ‖ = R → (p μ).natDegree ≤ K)
    (hlim : Tendsto (fun n : ℕ ↦ (∑ μ ∈ S, (p μ).eval (n : ℂ) * μ ^ n) /
      ((n : ℂ) ^ K * (R : ℂ) ^ n)) atTop (𝓝 0)) :
    ∀ μ ∈ S, ‖μ‖ = R → (p μ).coeff K = 0 := by
  classical
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  set U := S.filter fun μ ↦ ‖μ‖ = R with hU
  set V := S.filter fun μ ↦ ¬ ‖μ‖ = R with hV
  have hnormU : ∀ μ ∈ U, ‖μ / (R : ℂ)‖ = 1 := fun μ hμ ↦ by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, (mem_filter.mp hμ).2,
      div_self hR.ne']
  have hsplit : ∀ n : ℕ, (∑ μ ∈ S, (p μ).eval (n : ℂ) * μ ^ n) / ((n : ℂ) ^ K * (R : ℂ) ^ n) =
      ∑ μ ∈ U, (p μ).coeff K * (μ / R) ^ n +
      ∑ μ ∈ U, ((p μ).eval (n : ℂ) / (n : ℂ) ^ K - (p μ).coeff K) * (μ / R) ^ n +
      ∑ μ ∈ V, (p μ).eval (n : ℂ) / (n : ℂ) ^ K * (μ / R) ^ n := by
    intro n
    rw [← sum_filter_add_sum_filter_not S (fun μ ↦ ‖μ‖ = R), add_div, sum_div, sum_div,
      ← sum_add_distrib]
    congr 1
    · refine sum_congr rfl fun μ _ ↦ ?_
      rw [div_pow, mul_div_mul_comm]
      ring
    · refine sum_congr rfl fun μ _ ↦ ?_
      rw [div_pow, mul_div_mul_comm]
  have h1 : Tendsto (fun n : ℕ ↦ ∑ μ ∈ U, ((p μ).eval (n : ℂ) / (n : ℂ) ^ K - (p μ).coeff K) *
      (μ / R) ^ n) atTop (𝓝 0) := by
    have hterm : ∀ μ ∈ U, Tendsto (fun n : ℕ ↦ ((p μ).eval (n : ℂ) / (n : ℂ) ^ K -
        (p μ).coeff K) * (μ / R) ^ n) atTop (𝓝 0) := by
      intro μ hμ
      have hsub : Tendsto (fun n : ℕ ↦ (p μ).eval (n : ℂ) / (n : ℂ) ^ K - (p μ).coeff K) atTop
          (𝓝 0) := by
        have h := (tendsto_eval_div_pow (p μ)
          (hdeg μ (mem_filter.mp hμ).1 (mem_filter.mp hμ).2)).sub_const ((p μ).coeff K)
        rwa [sub_self] at h
      have hconv : Tendsto (fun n : ℕ ↦ ‖(p μ).eval (n : ℂ) / (n : ℂ) ^ K - (p μ).coeff K‖)
          atTop (𝓝 0) := by
        simpa using hsub.norm
      refine squeeze_zero_norm (fun n ↦ le_of_eq ?_) hconv
      rw [norm_mul, norm_pow, hnormU μ hμ, one_pow, mul_one]
    simpa using tendsto_finsetSum U hterm
  have h2 : Tendsto (fun n : ℕ ↦ ∑ μ ∈ V, (p μ).eval (n : ℂ) / (n : ℂ) ^ K * (μ / R) ^ n)
      atTop (𝓝 0) := by
    have hterm : ∀ μ ∈ V, Tendsto (fun n : ℕ ↦ (p μ).eval (n : ℂ) / (n : ℂ) ^ K * (μ / R) ^ n)
        atTop (𝓝 0) := by
      intro μ hμ
      obtain ⟨hμS, hμR⟩ := mem_filter.mp hμ
      rcases lt_or_gt_of_ne hμR with hlt | hgt
      · have hz : ‖μ / (R : ℂ)‖ < 1 := by
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_lt_one hR]
          exact hlt
        have hbase := (tendsto_poly_mul_pow_zero hz (p μ)).norm
        rw [norm_zero] at hbase
        refine squeeze_zero_norm' ?_ hbase
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn' : (1 : ℝ) ≤ ‖(n : ℂ) ^ K‖ := by
          rw [norm_pow, Complex.norm_natCast]
          exact one_le_pow₀ (by exact_mod_cast hn)
        rw [div_mul_eq_mul_div, norm_div]
        exact div_le_self (norm_nonneg _) hn'
      · simp only [hbig μ hμS hgt, eval_zero, zero_div, zero_mul]
        exact tendsto_const_nhds
    simpa using tendsto_finsetSum V hterm
  have hmain : Tendsto (fun n : ℕ ↦ ∑ i : U, (p i.1).coeff K * (i.1 / (R : ℂ)) ^ n) atTop
      (𝓝 0) := by
    have := (hlim.sub h1).sub h2
    simp only [sub_zero] at this
    refine this.congr fun n ↦ ?_
    rw [hsplit n, sum_coe_sort U (fun μ ↦ (p μ).coeff K * (μ / (R : ℂ)) ^ n)]
    ring
  have hzero := coeffs_eq_zero_of_tendsto_zero (fun i : U ↦ (p i.1).coeff K)
    (fun i : U ↦ i.1 / (R : ℂ)) (fun i ↦ hnormU i.1 i.2)
    (fun i j hij ↦ Subtype.ext ((div_left_inj' hRne).mp hij)) hmain
  intro μ hμ hμR
  exact hzero ⟨μ, mem_filter.mpr ⟨hμ, hμR⟩⟩

/-- **Bounded polynomial-exponential sums.**  No component with `|μ| > 1`, and no nonconstant
component with `|μ| = 1`, survives in a bounded sum `∑_{μ ∈ S} p_μ(n) μⁿ`. -/
theorem polyExp_bounded (S : Finset ℂ) (p : ℂ → ℂ[X]) {B : ℝ}
    (hB : ∀ n : ℕ, ‖∑ μ ∈ S, (p μ).eval (n : ℂ) * μ ^ n‖ ≤ B) :
    ∀ μ ∈ S, (1 < ‖μ‖ → p μ = 0) ∧ (‖μ‖ = 1 → ∀ k, 1 ≤ k → (p μ).coeff k = 0) := by
  classical
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  suffices hno : ¬ ∃ μ ∈ S, p μ ≠ 0 ∧ (1 < ‖μ‖ ∨ (‖μ‖ = 1 ∧ 1 ≤ (p μ).natDegree)) by
    intro μ hμ
    refine ⟨fun hgt ↦ ?_, fun hone k hk ↦ ?_⟩
    · by_contra hne
      exact hno ⟨μ, hμ, hne, Or.inl hgt⟩
    · by_contra hne
      have hp : p μ ≠ 0 := fun h ↦ hne (by rw [h, coeff_zero])
      exact hno ⟨μ, hμ, hp, Or.inr ⟨hone, hk.trans (le_natDegree_of_ne_zero hne)⟩⟩
  rintro ⟨μ0, hμ0S, hμ0ne, hμ0⟩
  set T := S.filter fun μ ↦ p μ ≠ 0 with hT
  have hμ0T : μ0 ∈ T := mem_filter.mpr ⟨hμ0S, hμ0ne⟩
  obtain ⟨μ1, hμ1T, hmax⟩ := T.exists_max_image (fun μ ↦ ‖μ‖) ⟨μ0, hμ0T⟩
  set R := ‖μ1‖ with hRdef
  have hμ0R := hmax μ0 hμ0T
  have hR1 : 1 ≤ R := by
    rcases hμ0 with h | h
    · linarith
    · linarith [h.1]
  have hR0 : 0 < R := by linarith
  have hbig : ∀ μ ∈ S, R < ‖μ‖ → p μ = 0 := fun μ hμ hlt ↦ by
    by_contra hne
    linarith [hmax μ (mem_filter.mpr ⟨hμ, hne⟩)]
  set U := T.filter fun μ ↦ ‖μ‖ = R with hU
  set K := U.sup fun μ ↦ (p μ).natDegree with hK
  have hdeg : ∀ μ ∈ S, ‖μ‖ = R → (p μ).natDegree ≤ K := fun μ hμ hμR ↦ by
    by_cases hp : p μ = 0
    · simp [hp]
    · exact le_sup (f := fun μ ↦ (p μ).natDegree) (mem_filter.mpr ⟨mem_filter.mpr ⟨hμ, hp⟩, hμR⟩)
  have hcase : 1 < R ∨ 1 ≤ K := by
    rcases hμ0 with h | ⟨h1, hdeg0⟩
    · exact Or.inl (lt_of_lt_of_le h hμ0R)
    · by_cases hR' : 1 < R
      · exact Or.inl hR'
      · right
        have hRe : R = 1 := le_antisymm (not_lt.mp hR') hR1
        exact hdeg0.trans (hdeg μ0 hμ0S (by rw [h1, hRe]))
  have hc : Tendsto (fun n : ℕ ↦ B * ((n : ℝ) ^ K * R ^ n)⁻¹) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = B * 0 by ring]
    refine Tendsto.const_mul B ?_
    rcases hcase with hR' | hK'
    · refine squeeze_zero' (Eventually.of_forall fun n ↦ inv_nonneg.mpr
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hR0.le _))) ?_
        (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hR0.le) (inv_lt_one_of_one_lt₀ hR'))
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [inv_pow]
      exact inv_anti₀ (pow_pos hR0 _)
        (le_mul_of_one_le_left (pow_nonneg hR0.le _) (one_le_pow₀ hn'))
    · refine squeeze_zero' (Eventually.of_forall fun n ↦ inv_nonneg.mpr
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hR0.le _))) ?_
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpos : (0 : ℝ) < n := by linarith
      exact inv_anti₀ hpos ((le_self_pow₀ hn' (by omega)).trans
        (le_mul_of_one_le_right (pow_nonneg hpos.le _) (one_le_pow₀ hR1)))
  have hlim : Tendsto (fun n : ℕ ↦ (∑ μ ∈ S, (p μ).eval (n : ℂ) * μ ^ n) /
      ((n : ℂ) ^ K * (R : ℂ) ^ n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) hc
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hR0.le, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hB n) (inv_nonneg.mpr
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hR0.le _)))
  have htop := polyExp_top_coeff_eq_zero S p hR0 K hbig hdeg hlim
  have hUne : U.Nonempty := ⟨μ1, mem_filter.mpr ⟨hμ1T, rfl⟩⟩
  obtain ⟨μ2, hμ2U, hμ2K⟩ := U.exists_mem_eq_sup hUne fun μ ↦ (p μ).natDegree
  obtain ⟨hμ2T, hμ2R⟩ := mem_filter.mp hμ2U
  obtain ⟨hμ2S, hμ2ne⟩ := mem_filter.mp hμ2T
  have hc2 := htop μ2 hμ2S hμ2R
  rw [hK, hμ2K, coeff_natDegree] at hc2
  exact hμ2ne (leadingCoeff_eq_zero.mp hc2)

/-- **Bounded two-sided solutions are sums of unimodular exponentials.** -/
theorem twoSided_bounded_recurrence (χ : ℂ[X]) (hmon : χ.Monic) (h0 : χ.coeff 0 ≠ 0)
    {a : ℤ → ℂ} (hrec : IsZRecurrence χ a) {B : ℝ} (hB : ∀ m, ‖a m‖ ≤ B) :
    ∃ c : ℂ → ℂ, ∀ m : ℤ,
      a m = ∑ μ ∈ χ.roots.toFinset.filter (fun μ ↦ ‖μ‖ = 1), c μ * μ ^ m := by
  classical
  set S := χ.roots.toFinset with hS
  have hne : ∀ μ ∈ S, μ ≠ 0 := by
    intro μ hμ h
    subst h
    have hroot := (mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp hμ)
    rw [IsRoot, ← coeff_zero_eq_eval_zero] at hroot
    exact h0 hroot
  -- forward representation with multiplicity bounds
  have hfwd : ∀ n : ℕ, ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * a ((n + i : ℕ) : ℤ) = 0 := by
    intro n
    have := hrec n
    push_cast at this ⊢
    exact this
  obtain ⟨p, hpdeg, hp⟩ := isPolyExpMult_of_linearRecurrence χ hmon h0
    (fun n ↦ a (n : ℤ)) hfwd
  -- the two-sided extension
  set G : ℤ → ℂ := fun m ↦ ∑ μ ∈ S, (p μ).eval (m : ℂ) * μ ^ m with hG
  have hGrec : IsZRecurrence χ G := by
    intro m
    simp only [hG, mul_sum]
    rw [sum_comm]
    refine sum_eq_zero fun μ hμ ↦ ?_
    have hμ0 := hne μ hμ
    have hdvd : (X - C μ) ^ χ.roots.count μ ∣ χ := by
      rw [count_roots]
      exact pow_rootMultiplicity_dvd χ μ
    have hkey := sum_coeff_shift_eq_zero χ hdvd (hpdeg μ) (m : ℂ)
    calc ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * ((p μ).eval (((m + i : ℤ)) : ℂ) *
          μ ^ (m + i : ℤ))
        = μ ^ m * ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * (μ ^ i * (p μ).eval ((m : ℂ) + i)) := by
          rw [mul_sum]
          refine sum_congr rfl fun i _ ↦ ?_
          rw [zpow_add₀ hμ0, zpow_natCast]
          push_cast
          ring
      _ = 0 := by rw [hkey, mul_zero]
  have haG : a = G := eq_of_isZRecurrence χ h0 hrec hGrec fun n ↦ by
    have h := hp n
    simp only at h
    rw [h]
    simp [hG, hS]
  -- forward boundedness
  have hfwdB := polyExp_bounded S p (B := B) fun n ↦ by
    rw [← hp n]
    exact hB n
  -- backward boundedness
  set p' : ℂ → ℂ[X] := fun ν ↦ (p ν⁻¹).comp (-X) with hp'
  have hbwd := polyExp_bounded (S.image fun μ ↦ μ⁻¹) p' (B := B) fun n ↦ by
    have hval : a (-(n : ℤ)) = ∑ ν ∈ S.image (fun μ ↦ μ⁻¹), (p' ν).eval (n : ℂ) * ν ^ n := by
      rw [haG, sum_image fun x _ y _ h ↦ inv_injective h]
      refine sum_congr rfl fun μ hμ ↦ ?_
      simp only [hp', inv_inv, eval_comp, eval_neg, eval_X, inv_pow, zpow_neg, zpow_natCast]
      push_cast
      ring
    rw [← hval]
    exact hB _
  refine ⟨fun μ ↦ (p μ).coeff 0, fun m ↦ ?_⟩
  rw [haG, hG]
  simp only
  rw [← sum_filter_add_sum_filter_not S (fun μ ↦ ‖μ‖ = 1)]
  have hoff : ∑ μ ∈ S.filter (fun μ ↦ ¬ ‖μ‖ = 1), (p μ).eval (m : ℂ) * μ ^ m = 0 := by
    refine sum_eq_zero fun μ hμ ↦ ?_
    obtain ⟨hμS, hμ1⟩ := mem_filter.mp hμ
    rcases lt_or_gt_of_ne hμ1 with hlt | hgt
    · -- `|μ| < 1`: killed on the left
      have hμ0 := hne μ hμS
      have hgt' : 1 < ‖μ⁻¹‖ := by
        rw [norm_inv]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hμ0, hlt⟩
      have hz := (hbwd μ⁻¹ (mem_image_of_mem _ hμS)).1 hgt'
      have hpz : p μ = 0 := by
        have hcomp : ((p μ).comp (-X)).comp (-X) = p μ := by
          rw [comp_assoc, neg_comp, X_comp, neg_neg, comp_X]
        rw [← hcomp]
        simp only [hp', inv_inv] at hz
        rw [hz, zero_comp]
      simp [hpz]
    · simp [(hfwdB μ hμS).1 hgt]
  rw [hoff, add_zero]
  refine sum_congr rfl fun μ hμ ↦ ?_
  obtain ⟨hμS, hμ1⟩ := mem_filter.mp hμ
  have hconst : p μ = C ((p μ).coeff 0) := by
    ext k
    rcases k with _ | k
    · simp
    · rw [coeff_C, ite_eq_right (Nat.succ_ne_zero k)]
      exact (hfwdB μ hμS).2 hμ1 (k + 1) (Nat.succ_pos k)
  rw [hconst, eval_C, coeff_C_zero]

end WeakTiling

end

end TwoSidedRecurrence

/-! ## Step H, first part: the degree slices of lattice tiling data are unimodular exponential sums -/

section LatticeSlices

section

open Polynomial Finset

namespace WeakTiling

variable {ι : Type} [Fintype ι]

/-- Total degree of a lattice point. -/
def latticeDeg (u : ι → ℤ) : ℤ := ∑ k, u k

/-- The Laurent monomial `z^u`. -/
noncomputable def latticeMono (z : ι → ℂ) (u : ι → ℤ) : ℂ := ∏ k, z k ^ u k

theorem latticeDeg_add (u v : ι → ℤ) : latticeDeg (u + v) = latticeDeg u + latticeDeg v := by
  simp [latticeDeg, sum_add_distrib]

theorem latticeMono_add {z : ι → ℂ} (hz : ∀ k, z k ≠ 0) (u v : ι → ℤ) :
    latticeMono z (u + v) = latticeMono z u * latticeMono z v := by
  rw [latticeMono, latticeMono, latticeMono, ← prod_mul_distrib]
  exact prod_congr rfl fun k _ ↦ zpow_add₀ (hz k) _ _

theorem norm_latticeMono {z : ι → ℂ} (hz : ∀ k, ‖z k‖ = 1) (u : ι → ℤ) :
    ‖latticeMono z u‖ = 1 := by
  simp [latticeMono, norm_prod, norm_zpow, hz]

/-- The degree-`m` slice `a_m(z) = ∑_{deg u = m} M(u) z^u`. -/
noncomputable def latticeSlice (D : LatticeTilingData ι) (z : ι → ℂ) (m : ℤ) : ℂ :=
  ∑' u, if latticeDeg u = m then (D.M u : ℂ) * latticeMono z u else 0

/-- The box `[min m 0, max m 0]^ι`, which contains every support point of degree `m`. -/
noncomputable def sliceBox (m : ℤ) : Finset (ι → ℤ) := by
  classical
  exact Fintype.piFinset fun _ ↦ Finset.Icc (min m 0) (max m 0)

theorem mem_sliceBox_of_ne_zero (D : LatticeTilingData ι) {u : ι → ℤ} (hu : D.M u ≠ 0) :
    u ∈ sliceBox (latticeDeg u) := by
  classical
  rw [sliceBox, Fintype.mem_piFinset]
  intro k
  rw [Finset.mem_Icc]
  rcases D.orthants u hu with rfl | hpos | hneg
  · simp [latticeDeg]
  · have hle : u k ≤ latticeDeg u :=
      single_le_sum (f := u) (fun j _ ↦ by linarith [hpos j]) (mem_univ k)
    exact ⟨(min_le_right _ _).trans (by linarith [hpos k]), hle.trans (le_max_left _ _)⟩
  · have hle : latticeDeg u ≤ u k := by
      have h := single_le_sum (f := fun j ↦ -u j) (fun j _ ↦ by linarith [hneg j]) (mem_univ k)
      simp only [sum_neg_distrib] at h
      unfold latticeDeg
      linarith
    exact ⟨(min_le_left _ _).trans hle, (by linarith [hneg k] : u k ≤ 0).trans (le_max_right _ _)⟩

theorem sliceTerm_eq_zero (D : LatticeTilingData ι) (z : ι → ℂ) (m : ℤ) {u : ι → ℤ}
    (hu : u ∉ sliceBox m) :
    (if latticeDeg u = m then (D.M u : ℂ) * latticeMono z u else 0) = 0 := by
  split_ifs with hdeg
  · by_cases hM : D.M u = 0
    · simp [hM]
    · exact absurd (hdeg ▸ mem_sliceBox_of_ne_zero D hM) hu
  · rfl

theorem latticeSlice_eq_sum (D : LatticeTilingData ι) (z : ι → ℂ) (m : ℤ) :
    latticeSlice D z m = ∑ u ∈ sliceBox m,
      if latticeDeg u = m then (D.M u : ℂ) * latticeMono z u else 0 :=
  tsum_eq_sum fun _ hu ↦ sliceTerm_eq_zero D z m hu

/-- The shifted slice `∑_{deg u = m} M(u - s) z^u`. -/
noncomputable def shiftedSlice (D : LatticeTilingData ι) (z : ι → ℂ) (m : ℤ) (s : ι → ℤ) : ℂ :=
  ∑' u, if latticeDeg u = m then (D.M (u - s) : ℂ) * latticeMono z u else 0

theorem shiftedSlice_eq (D : LatticeTilingData ι) {z : ι → ℂ} (hz : ∀ k, z k ≠ 0) (m : ℤ)
    (s : ι → ℤ) :
    shiftedSlice D z m s = latticeMono z s * latticeSlice D z (m - latticeDeg s) := by
  rw [shiftedSlice, latticeSlice, ← tsum_mul_left, ← (Equiv.addRight s).tsum_eq]
  refine tsum_congr fun v ↦ ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, latticeDeg_add, latticeMono_add hz]
  by_cases h : latticeDeg v = m - latticeDeg s
  · rw [ite_eq_left (by rw [h]; ring), ite_eq_left h]
    ring
  · rw [ite_eq_right (by intro h'; apply h; linarith), ite_eq_right h, mul_zero]

theorem summable_shiftedSliceTerm (D : LatticeTilingData ι) (z : ι → ℂ) (m : ℤ) (s : ι → ℤ) :
    Summable fun u ↦ if latticeDeg u = m then (D.M (u - s) : ℂ) * latticeMono z u else 0 := by
  classical
  refine summable_of_ne_finset_zero (s := (sliceBox (m - latticeDeg s)).image (· + s)) ?_
  intro u hu
  split_ifs with hdeg
  · by_cases hM : D.M (u - s) = 0
    · simp [hM]
    · exfalso
      apply hu
      refine mem_image.mpr ⟨u - s, ?_, sub_add_cancel u s⟩
      have hmem := mem_sliceBox_of_ne_zero D hM
      have hd : latticeDeg (u - s) = m - latticeDeg s := by
        have := latticeDeg_add (u - s) s
        rw [sub_add_cancel] at this
        linarith
      rwa [hd] at hmem
  · rfl

/-- **The slice recurrence.**  The balance `P · M = 0` in each degree. -/
theorem latticeSlice_balance (D : LatticeTilingData ι) {z : ι → ℂ} (hz : ∀ k, z k ≠ 0)
    (m : ℤ) :
    ∑ j, latticeMono z (fun k ↦ (D.p j k : ℤ)) *
        latticeSlice D z (m - latticeDeg fun k ↦ (D.p j k : ℤ)) =
      ∑ j, latticeMono z (fun k ↦ (D.q j k : ℤ)) *
        latticeSlice D z (m - latticeDeg fun k ↦ (D.q j k : ℤ)) := by
  simp only [← shiftedSlice_eq D hz]
  unfold shiftedSlice
  rw [← Summable.tsum_finsetSum fun j _ ↦ summable_shiftedSliceTerm D z m _,
    ← Summable.tsum_finsetSum fun j _ ↦ summable_shiftedSliceTerm D z m _]
  refine tsum_congr fun u ↦ ?_
  split_ifs with hdeg
  · rw [← sum_mul, ← sum_mul]
    congr 1
    exact_mod_cast D.balance u
  · simp

theorem rows_pos_nonneg (D : LatticeTilingData ι) {C : ℝ}
    (hC : ∀ (d : ℕ) (S : Finset (ι → ℕ)), (∀ e ∈ S, ∑ k, e k = d) →
      ∑ e ∈ S, D.M (fun k ↦ (e k : ℤ)) ≤ C) : 0 ≤ C := by
  simpa using hC 0 ∅ (by simp)

/-- **Mass of a degree fiber.**  The atoms of degree `m` carry uniformly bounded total mass. -/
theorem fiber_mass_le (D : LatticeTilingData ι) [Nonempty ι] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℤ,
      ∑ u ∈ (sliceBox m).filter (fun u ↦ latticeDeg u = m ∧ D.M u ≠ 0), D.M u ≤ B := by
  classical
  obtain ⟨Cp, hCp⟩ := D.rows_pos
  obtain ⟨Cn, hCn⟩ := D.rows_neg
  have hCp0 : 0 ≤ Cp := rows_pos_nonneg D hCp
  have hCn0 : 0 ≤ Cn := by simpa using hCn 0 ∅ (by simp)
  refine ⟨Cp + Cn, by linarith, fun m ↦ ?_⟩
  set F := (sliceBox m).filter fun u ↦ latticeDeg u = m ∧ D.M u ≠ 0 with hF
  obtain ⟨k0⟩ := ‹Nonempty ι›
  rcases le_or_gt 0 m with hm | hm
  · -- nonnegative degree: every support point lies in the positive orthant
    have hpos : ∀ u ∈ F, ∀ k, 0 ≤ u k := by
      intro u hu k
      obtain ⟨-, hdeg, hM⟩ := mem_filter.mp hu
      rcases D.orthants u hM with rfl | hp | hn
      · simp
      · linarith [hp k]
      · exfalso
        have : latticeDeg u ≤ u k0 := by
          have h := single_le_sum (f := fun j ↦ -u j) (fun j _ ↦ by linarith [hn j])
            (mem_univ k0)
          simp only [sum_neg_distrib] at h
          unfold latticeDeg
          linarith
        linarith [hn k0]
    set S := F.image fun u k ↦ (u k).toNat with hS
    have hinj : ∀ u ∈ F, ∀ v ∈ F, (fun k ↦ (u k).toNat) = (fun k ↦ (v k).toNat) → u = v := by
      intro u hu v hv h
      funext k
      have := congrFun h k
      rw [← Int.toNat_of_nonneg (hpos u hu k), ← Int.toNat_of_nonneg (hpos v hv k), this]
    have hsum : ∑ e ∈ S, D.M (fun k ↦ (e k : ℤ)) = ∑ u ∈ F, D.M u := by
      rw [hS, sum_image hinj]
      refine sum_congr rfl fun u hu ↦ ?_
      congr 1
      funext k
      exact Int.toNat_of_nonneg (hpos u hu k)
    have hdegS : ∀ e ∈ S, ∑ k, e k = m.toNat := by
      intro e he
      obtain ⟨u, hu, rfl⟩ := mem_image.mp he
      have hdeg := (mem_filter.mp hu).2.1
      have hcast : ((∑ k, (u k).toNat : ℕ) : ℤ) = m := by
        push_cast
        rw [← hdeg]
        exact sum_congr rfl fun k _ ↦ Int.toNat_of_nonneg (hpos u hu k)
      show ∑ k, (u k).toNat = m.toNat
      omega
    rw [← hsum]
    linarith [hCp m.toNat S hdegS]
  · -- negative degree: every support point lies in the negative orthant
    have hneg : ∀ u ∈ F, ∀ k, u k ≤ 0 := by
      intro u hu k
      obtain ⟨-, hdeg, hM⟩ := mem_filter.mp hu
      rcases D.orthants u hM with rfl | hp | hn
      · simp [latticeDeg] at hdeg
        omega
      · exfalso
        have : u k0 ≤ latticeDeg u :=
          single_le_sum (f := u) (fun j _ ↦ by linarith [hp j]) (mem_univ k0)
        linarith [hp k0]
      · linarith [hn k]
    set S := F.image fun u k ↦ (-u k).toNat with hS
    have hinj : ∀ u ∈ F, ∀ v ∈ F, (fun k ↦ (-u k).toNat) = (fun k ↦ (-v k).toNat) → u = v := by
      intro u hu v hv h
      funext k
      have := congrFun h k
      have h1 := Int.toNat_of_nonneg (neg_nonneg.mpr (hneg u hu k))
      have h2 := Int.toNat_of_nonneg (neg_nonneg.mpr (hneg v hv k))
      rw [this] at h1
      linarith
    have hsum : ∑ e ∈ S, D.M (fun k ↦ -(e k : ℤ)) = ∑ u ∈ F, D.M u := by
      rw [hS, sum_image hinj]
      refine sum_congr rfl fun u hu ↦ ?_
      congr 1
      funext k
      rw [Int.toNat_of_nonneg (neg_nonneg.mpr (hneg u hu k)), neg_neg]
    have hdegS : ∀ e ∈ S, ∑ k, e k = (-m).toNat := by
      intro e he
      obtain ⟨u, hu, rfl⟩ := mem_image.mp he
      have hdeg := (mem_filter.mp hu).2.1
      have hcast : ((∑ k, (-u k).toNat : ℕ) : ℤ) = -m := by
        push_cast
        rw [← hdeg]
        unfold latticeDeg
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun k _ ↦ Int.toNat_of_nonneg (neg_nonneg.mpr (hneg u hu k))
      show ∑ k, (-u k).toNat = (-m).toNat
      omega
    rw [← hsum]
    linarith [hCn (-m).toNat S hdegS]

/-- On the torus the slices are bounded on both sides. -/
theorem norm_latticeSlice_le (D : LatticeTilingData ι) [Nonempty ι] :
    ∃ B : ℝ, ∀ {z : ι → ℂ}, (∀ k, ‖z k‖ = 1) → ∀ m, ‖latticeSlice D z m‖ ≤ B := by
  classical
  obtain ⟨B, -, hB⟩ := fiber_mass_le D
  refine ⟨B, fun {z} hz m ↦ ?_⟩
  set F := (sliceBox m).filter fun u ↦ latticeDeg u = m ∧ D.M u ≠ 0 with hF
  have hnorm : ‖latticeSlice D z m‖ ≤ ∑ u ∈ F, D.M u := by
    rw [latticeSlice_eq_sum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    rw [hF, sum_filter]
    refine sum_congr rfl fun u _ ↦ ?_
    by_cases hdeg : latticeDeg u = m
    · by_cases hM : D.M u = 0
      · simp [hdeg, hM]
      · rw [ite_eq_left hdeg, ite_eq_left ⟨hdeg, hM⟩, norm_mul, norm_latticeMono hz, mul_one,
          Complex.norm_real, Real.norm_of_nonneg (D.nonneg u)]
    · simp [hdeg]
  exact hnorm.trans (hB m)

/-- The largest right-endpoint degree `E = maxⱼ |qⱼ|`. -/
def sliceTop (D : LatticeTilingData ι) : ℕ := univ.sup fun j ↦ ∑ k, D.q j k

theorem q_deg_le_sliceTop (D : LatticeTilingData ι) (j : Fin D.n) :
    ∑ k, D.q j k ≤ sliceTop D :=
  le_sup (f := fun j ↦ ∑ k, D.q j k) (mem_univ j)

theorem p_deg_lt_q_deg (D : LatticeTilingData ι) [Nonempty ι] (j : Fin D.n) :
    ∑ k, D.p j k < ∑ k, D.q j k :=
  sum_lt_sum (fun k _ ↦ (D.endpoint_lt j k).le)
    ⟨Classical.arbitrary ι, mem_univ _, D.endpoint_lt j _⟩

/-- The reversed characteristic polynomial `∑ⱼ (z^{pⱼ} X^{E-|pⱼ|} - z^{qⱼ} X^{E-|qⱼ|})`. -/
noncomputable def sliceXi (D : LatticeTilingData ι) (z : ι → ℂ) : ℂ[X] :=
  ∑ j, (C (latticeMono z fun k ↦ (D.p j k : ℤ)) * X ^ (sliceTop D - ∑ k, D.p j k) -
    C (latticeMono z fun k ↦ (D.q j k : ℤ)) * X ^ (sliceTop D - ∑ k, D.q j k))

theorem sliceXi_coeff (D : LatticeTilingData ι) (z : ι → ℂ) (i : ℕ) :
    (sliceXi D z).coeff i =
      ∑ j, ((if i = sliceTop D - ∑ k, D.p j k then latticeMono z fun k ↦ (D.p j k : ℤ) else 0) -
        (if i = sliceTop D - ∑ k, D.q j k then latticeMono z fun k ↦ (D.q j k : ℤ) else 0)) := by
  simp only [sliceXi, finsetSum_coeff, coeff_sub, coeff_C_mul_X_pow]

theorem sliceXi_natDegree_le (D : LatticeTilingData ι) (z : ι → ℂ) :
    (sliceXi D z).natDegree ≤ sliceTop D := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ ↦ ?_
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)
  · exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)

theorem latticeDeg_natCast (v : ι → ℕ) : latticeDeg (fun k ↦ (v k : ℤ)) = ((∑ k, v k : ℕ) : ℤ) := by
  simp [latticeDeg]

theorem sliceXi_coeff_top (D : LatticeTilingData ι) [Nonempty ι] (z : ι → ℂ) :
    (sliceXi D z).coeff (sliceTop D) ≠ 0 := by
  classical
  rw [sliceXi_coeff]
  have hq : ∀ j, ¬ sliceTop D = sliceTop D - ∑ k, D.q j k := by
    intro j h
    have h1 := q_deg_le_sliceTop D j
    have h2 := lt_of_le_of_lt (Nat.zero_le _) (p_deg_lt_q_deg D j)
    omega
  have hp : ∀ j, (sliceTop D = sliceTop D - ∑ k, D.p j k) ↔ D.p j = 0 := by
    intro j
    have h1 := (p_deg_lt_q_deg D j).le.trans (q_deg_le_sliceTop D j)
    constructor
    · intro h
      have hz : ∑ k, D.p j k = 0 := by omega
      funext k
      exact (sum_eq_zero_iff.mp hz) k (mem_univ k)
    · intro h
      simp [h]
  have hmono0 : ∀ j, D.p j = 0 → (latticeMono z fun k ↦ (D.p j k : ℤ)) = 1 := by
    intro j h
    simp [latticeMono, h]
  have hsum : ∑ j, ((if sliceTop D = sliceTop D - ∑ k, D.p j k then
      latticeMono z fun k ↦ (D.p j k : ℤ) else 0) -
      (if sliceTop D = sliceTop D - ∑ k, D.q j k then
        latticeMono z fun k ↦ (D.q j k : ℤ) else 0)) =
      ((univ.filter fun j ↦ D.p j = 0).card : ℂ) := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [ite_eq_right (hq j), sub_zero]
    by_cases h : D.p j = 0
    · rw [ite_eq_left ((hp j).mpr h), ite_eq_left h, hmono0 j h, Nat.cast_one]
    · rw [ite_eq_right (fun h' ↦ h ((hp j).mp h')), ite_eq_right h]
  rw [hsum, Nat.cast_ne_zero]
  exact card_ne_zero.mpr ⟨⟨0, D.n_pos⟩, mem_filter.mpr ⟨mem_univ _, D.p_zero⟩⟩

theorem sliceXi_natDegree (D : LatticeTilingData ι) [Nonempty ι] (z : ι → ℂ) :
    (sliceXi D z).natDegree = sliceTop D :=
  natDegree_eq_of_le_of_coeff_ne_zero (sliceXi_natDegree_le D z) (sliceXi_coeff_top D z)

/-- The monic characteristic polynomial of the slice recurrence at `z`. -/
noncomputable def sliceCharPoly (D : LatticeTilingData ι) (z : ι → ℂ) : ℂ[X] :=
  C ((sliceXi D z).coeff (sliceTop D))⁻¹ * sliceXi D z

theorem sliceCharPoly_monic (D : LatticeTilingData ι) [Nonempty ι] (z : ι → ℂ) :
    (sliceCharPoly D z).Monic := by
  have htop := sliceXi_coeff_top D z
  rw [Monic, sliceCharPoly, leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (inv_ne_zero htop)),
    leadingCoeff, sliceXi_natDegree, inv_mul_cancel₀ htop]

theorem sliceCharPoly_natDegree (D : LatticeTilingData ι) [Nonempty ι] (z : ι → ℂ) :
    (sliceCharPoly D z).natDegree = sliceTop D := by
  rw [sliceCharPoly, natDegree_C_mul (inv_ne_zero (sliceXi_coeff_top D z)), sliceXi_natDegree]

/-- The slice recurrence in the normalized form of `IsZRecurrence`. -/
theorem latticeSlice_isZRecurrence (D : LatticeTilingData ι) [Nonempty ι] {z : ι → ℂ}
    (hz : ∀ k, z k ≠ 0) : IsZRecurrence (sliceCharPoly D z) (latticeSlice D z) := by
  classical
  intro m
  rw [sliceCharPoly_natDegree]
  simp only [sliceCharPoly, coeff_C_mul, mul_assoc]
  rw [← mul_sum]
  refine mul_eq_zero_of_right _ ?_
  have hbal := latticeSlice_balance D hz (m + sliceTop D)
  simp only [sliceXi_coeff, sub_mul, sum_mul, sum_sub_distrib]
  rw [sum_comm, sum_comm (s := range (sliceTop D + 1))]
  have hp_le : ∀ j, ∑ k, D.p j k ≤ sliceTop D :=
    fun j ↦ (p_deg_lt_q_deg D j).le.trans (q_deg_le_sliceTop D j)
  have hpick : ∀ (t : ℕ), t ≤ sliceTop D → ∀ (w : ℂ),
      ∑ i ∈ range (sliceTop D + 1), (if i = sliceTop D - t then w else 0) *
        latticeSlice D z (m + i) = w * latticeSlice D z (m + sliceTop D - t) := by
    intro t ht w
    rw [sum_eq_single (sliceTop D - t)]
    · rw [ite_eq_left rfl]
      congr 2
      push_cast [Nat.cast_sub ht]
      ring
    · intro i _ hi
      rw [ite_eq_right hi, zero_mul]
    · intro h
      exact absurd (mem_range.mpr (by omega)) h
  rw [sum_congr rfl fun j _ ↦ hpick _ (hp_le j) _,
    sum_congr rfl fun j _ ↦ hpick _ (q_deg_le_sliceTop D j) _, sub_eq_zero]
  simpa only [latticeDeg_natCast, add_sub_assoc] using hbal

/-- **Unimodular spectrum.**  At a torus point where the characteristic polynomial has nonzero
constant coefficient, every slice is a sum of unimodular exponentials over the characteristic
roots on the unit circle, for all `m ∈ ℤ`. -/
theorem latticeSlice_unimodular (D : LatticeTilingData ι) [Nonempty ι] {z : ι → ℂ}
    (hz : ∀ k, ‖z k‖ = 1) (hgen : (sliceXi D z).coeff 0 ≠ 0) :
    ∃ c : ℂ → ℂ, ∀ m : ℤ, latticeSlice D z m =
      ∑ μ ∈ (sliceCharPoly D z).roots.toFinset.filter (fun μ ↦ ‖μ‖ = 1), c μ * μ ^ m := by
  have hz0 : ∀ k, z k ≠ 0 := fun k h ↦ by simpa [h] using hz k
  obtain ⟨B, hB⟩ := norm_latticeSlice_le D
  have h0 : (sliceCharPoly D z).coeff 0 ≠ 0 := by
    rw [sliceCharPoly, coeff_C_mul]
    exact mul_ne_zero (inv_ne_zero (sliceXi_coeff_top D z)) hgen
  exact twoSided_bounded_recurrence _ (sliceCharPoly_monic D z) h0
    (latticeSlice_isZRecurrence D hz0) (hB hz)

end WeakTiling

end

end LatticeSlices

/-! ## Multivariable phase rigidity by restriction to integer lines -/

section MultiVarRigidity

section

open Set Complex MeasureTheory Finset

namespace WeakTiling

variable {σ : Type*} [Fintype σ]

/-- The integer dot product `k · v`. -/
def dotZ (k v : σ → ℤ) : ℤ :=
  ∑ i, k i * v i

/-- The torus character `e(k·t) = exp(2πi (k·t) / T)`. -/
noncomputable def mvChar (T : ℝ) (k : σ → ℤ) (t : σ → ℝ) : ℂ :=
  exp (2 * Real.pi * I * ((∑ i, (k i : ℝ) * t i : ℝ) : ℂ) / T)

/-- A multivariable trigonometric polynomial `∑_{k ∈ s} cₖ e(k·t)`. -/
noncomputable def mvTrigPoly (T : ℝ) (s : Finset (σ → ℤ)) (c : (σ → ℤ) → ℂ) (t : σ → ℝ) : ℂ :=
  ∑ k ∈ s, c k * mvChar T k t

/-- Coefficients of the restriction to the line `t₀ + u v`. -/
noncomputable def restrictCoeff (T : ℝ) (s : Finset (σ → ℤ)) (c : (σ → ℤ) → ℂ) (t₀ : σ → ℝ)
    (v : σ → ℤ) (m : ℤ) : ℂ :=
  ∑ k ∈ s.filter (fun k ↦ dotZ k v = m), c k * mvChar T k t₀

theorem norm_mvChar (T : ℝ) (k : σ → ℤ) (t : σ → ℝ) : ‖mvChar T k t‖ = 1 := by
  rw [mvChar]
  have : 2 * (Real.pi : ℂ) * I * ((∑ i, (k i : ℝ) * t i : ℝ) : ℂ) / (T : ℂ) =
      ((2 * Real.pi * (∑ i, (k i : ℝ) * t i) / T : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [this, norm_exp_ofReal_mul_I]

theorem mvChar_line (T : ℝ) (k : σ → ℤ) (t₀ : σ → ℝ) (v : σ → ℤ) (u : ℝ) :
    mvChar T k (fun i ↦ t₀ i + u * v i) = mvChar T k t₀ * circleChar T (dotZ k v) u := by
  rw [mvChar, mvChar, circleChar, ← exp_add, dotZ]
  congr 1
  push_cast
  simp only [mul_add, Finset.sum_add_distrib]
  have : ∑ i, (k i : ℂ) * ((u : ℂ) * (v i : ℂ)) = (u : ℂ) * ∑ i, (k i : ℂ) * (v i : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [this]
  ring

/-- **Restriction to an integer line.** -/
theorem mvTrigPoly_line (T : ℝ) (s : Finset (σ → ℤ)) (c : (σ → ℤ) → ℂ) (t₀ : σ → ℝ)
    (v : σ → ℤ) (u : ℝ) :
    mvTrigPoly T s c (fun i ↦ t₀ i + u * v i) =
      trigPoly T (s.image fun k ↦ dotZ k v) (restrictCoeff T s c t₀ v) u := by
  classical
  rw [mvTrigPoly, trigPoly]
  simp_rw [mvChar_line]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun k ↦ dotZ k v)
    (t := s.image fun k ↦ dotZ k v) (fun k hk ↦ Finset.mem_image_of_mem _ hk)]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [restrictCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [(Finset.mem_filter.mp hk).2]
  ring

/-- The restricted coefficients have `ℓ¹` norm at most the original one. -/
theorem sum_norm_restrictCoeff_le (T : ℝ) (s : Finset (σ → ℤ)) (c : (σ → ℤ) → ℂ)
    (t₀ : σ → ℝ) (v : σ → ℤ) :
    ∑ m ∈ s.image (fun k ↦ dotZ k v), ‖restrictCoeff T s c t₀ v m‖ ≤ ∑ k ∈ s, ‖c k‖ := by
  classical
  calc ∑ m ∈ s.image (fun k ↦ dotZ k v), ‖restrictCoeff T s c t₀ v m‖
      ≤ ∑ m ∈ s.image (fun k ↦ dotZ k v),
          ∑ k ∈ s.filter (fun k ↦ dotZ k v = m), ‖c k‖ := by
        refine Finset.sum_le_sum fun m _ ↦ (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [norm_mul, norm_mvChar, mul_one]
    _ = ∑ k ∈ s, ‖c k‖ :=
        Finset.sum_fiberwise_of_maps_to (fun k hk ↦ Finset.mem_image_of_mem _ hk) _

variable {p q : ℝ}

open Classical in
/-- **Multivariable step H along an integer line.**

The row functions are multivariable trigonometric polynomials on the torus of period `T = q - p`
with uniformly bounded coefficient sums (step W).  On the line `t₀ + u v` (`v ∈ ℤ^d`,
`u ∈ [a, b]`) they are exponential sums `∑ᵢ Uᵢ zᵢⁿ`.  If the root `zⱼ = exp(iφ)` has
`|φ''| ≥ m > 0` along the line, then the localized amplitude `χ Uⱼ` vanishes on the line.  The
remaining hypotheses (root separation and regularity) are those of
`amplitude_eq_zero_of_curved_root`. -/
theorem amplitude_eq_zero_of_curved_root_line {a b m M : ℝ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hpq : p < q) (hpa : p ≤ a) (hab : a ≤ b) (hbq : b ≤ q) (hm : 0 < m)
    (χ : ℝ → ℂ) (U z : ι → ℝ → ℂ) (j : ι) {φ φ' φ'' : ℝ → ℝ} {ψ' : ℝ → ℂ}
    (s : ℕ → Finset (σ → ℤ)) (c : ℕ → (σ → ℤ) → ℂ) (n₀ : ℕ) (t₀ : σ → ℝ) (v : σ → ℤ)
    (hW : ∀ n, n₀ ≤ n → ∑ k ∈ s n, ‖c n k‖ ≤ M)
    (hz : ∀ t ∈ Icc a b, z j t = exp ((φ t : ℂ) * I))
    (hD : ∀ t ∈ Icc a b, IsUnit (∏ i ∈ univ.erase j, (z j t - z i t)))
    (hF : ∀ n, n₀ ≤ n → ∀ u ∈ Icc a b,
      mvTrigPoly (q - p) (s n) (c n) (fun i ↦ t₀ i + u * v i) =
        expSum (fun i ↦ U i u) (fun i ↦ z i u) n)
    (hχ : ∀ t, t ∉ Ioo a b → χ t = 0)
    (hψ : ∀ t ∈ Icc a b, HasDerivAt (fun t ↦ χ t * U j t) (ψ' t) t)
    (hψ'c : ContinuousOn ψ' (Icc a b))
    (hwc : ∀ r, Continuous fun t ↦ χ t * (if h : IsUnit (∏ i ∈ univ.erase j, (z j t - z i t))
      then extractionWeight (fun i ↦ z i t) j h r else 0))
    (hwsum : ∀ r, Summable fun i ↦ ‖fourierCoeffOn hpq (fun t ↦ χ t *
      (if h : IsUnit (∏ i ∈ univ.erase j, (z j t - z i t))
        then extractionWeight (fun i ↦ z i t) j h r else 0)) i‖)
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc a b, HasDerivAt φ' (φ'' t) t)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hcurv : ∀ t ∈ Icc a b, m ≤ |φ'' t|) :
    ∫ x in p..q, ‖χ x * U j x‖ ^ 2 = 0 :=
  amplitude_eq_zero_of_curved_root hpq hpa hab hbq hm χ U z j
    (fun n ↦ (s n).image fun k ↦ dotZ k v)
    (fun n ↦ restrictCoeff (q - p) (s n) (c n) t₀ v) n₀
    (fun n hn ↦ (sum_norm_restrictCoeff_le _ _ _ _ _).trans (hW n hn)) hz hD
    (fun n hn u hu ↦ by rw [← mvTrigPoly_line]; exact hF n hn u hu)
    hχ hψ hψ'c hwc hwsum hφ hφ' hφ''c hcurv

end WeakTiling

end

end MultiVarRigidity

/-! ## Slices as torus trigonometric polynomials, and smooth extraction weights -/

section SliceTrig

section

open Complex Finset Polynomial
open scoped Real

namespace WeakTiling

section Torus

variable {ι : Type} [Fintype ι]

/-- The torus point `(e^{iθₖ})ₖ`. -/
noncomputable def torusPt (θ : ι → ℝ) : ι → ℂ := fun k ↦ exp ((θ k : ℂ) * I)

omit [Fintype ι] in
theorem norm_torusPt (θ : ι → ℝ) (k : ι) : ‖torusPt θ k‖ = 1 :=
  norm_exp_ofReal_mul_I _

/-- The support box of degree `m`, cut down to degree exactly `m`. -/
noncomputable def sliceFiber (m : ℤ) : Finset (ι → ℤ) :=
  (sliceBox m).filter fun u ↦ latticeDeg u = m

theorem mvChar_two_pi (u : ι → ℤ) (θ : ι → ℝ) :
    mvChar (2 * π) u θ = latticeMono (torusPt θ) u := by
  rw [mvChar, latticeMono]
  simp only [torusPt]
  have hk : ∀ k, exp ((θ k : ℂ) * I) ^ u k = exp ((((u k : ℝ) * θ k : ℝ) : ℂ) * I) := by
    intro k
    rw [← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  simp only [hk, ← Complex.exp_sum]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← Finset.sum_mul]
  push_cast
  field_simp

theorem mvTrigPoly_sliceFiber (D : LatticeTilingData ι) (m : ℤ) (θ : ι → ℝ) :
    mvTrigPoly (2 * π) (sliceFiber m) (fun u ↦ (D.M u : ℂ)) θ = latticeSlice D (torusPt θ) m := by
  rw [latticeSlice_eq_sum, mvTrigPoly, sliceFiber, sum_filter]
  refine sum_congr rfl fun u _ ↦ ?_
  split_ifs <;> simp [mvChar_two_pi]

/-- **Uniformly bounded coefficient sums of the slices.** -/
theorem sum_norm_fiber_le (D : LatticeTilingData ι) [Nonempty ι] :
    ∃ B : ℝ, ∀ m : ℤ, ∑ u ∈ sliceFiber m, ‖(D.M u : ℂ)‖ ≤ B := by
  classical
  obtain ⟨B, -, hB⟩ := fiber_mass_le D
  refine ⟨B, fun m ↦ (le_of_eq ?_).trans (hB m)⟩
  rw [sliceFiber, sum_filter, sum_filter]
  refine sum_congr rfl fun u _ ↦ ?_
  by_cases hdeg : latticeDeg u = m
  · by_cases h : D.M u = 0
    · simp [hdeg, h]
    · rw [ite_eq_left hdeg, ite_eq_left ⟨hdeg, h⟩, Complex.norm_real, Real.norm_of_nonneg (D.nonneg u)]
  · simp [hdeg]

end Torus

section Weights

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞} {x : E}

/-- The coefficients of `∏_{i ∈ s} (X - zᵢ)` are smooth when the roots are. -/
theorem contDiffAt_coeff_prod_X_sub_C {κ : Type*} (s : Finset κ) (z : κ → E → ℂ)
    (hz : ∀ i ∈ s, ContDiffAt ℝ n (z i) x) (k : ℕ) :
    ContDiffAt ℝ n (fun y ↦ (∏ i ∈ s, (X - C (z i y))).coeff k) x := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [prod_empty]
    exact contDiffAt_const
  | insert a s ha ih =>
    have hz' : ∀ i ∈ s, ContDiffAt ℝ n (z i) x := fun i hi ↦ hz i (mem_insert_of_mem hi)
    have hza := hz a (mem_insert_self a s)
    simp only [prod_insert ha]
    rcases k with _ | k
    · simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
      exact hza.neg.mul (ih hz' 0)
    · have hform : ∀ y, ((X - C (z a y)) * ∏ i ∈ s, (X - C (z i y))).coeff (k + 1) =
          (∏ i ∈ s, (X - C (z i y))).coeff k -
            z a y * (∏ i ∈ s, (X - C (z i y))).coeff (k + 1) := by
        intro y
        rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
      simp only [hform]
      exact (ih hz' k).sub (hza.mul (ih hz' (k + 1)))

/-- The extraction weights in closed form. -/
theorem extractionWeight_eq {κ : Type*} [Fintype κ] [DecidableEq κ] (z : κ → ℂ) (j : κ)
    (hD : IsUnit (∏ i ∈ univ.erase j, (z j - z i))) (r : ℕ) :
    extractionWeight z j hD r =
      (∏ i ∈ univ.erase j, (z j - z i))⁻¹ * (∏ i ∈ univ.erase j, (X - C (z i))).coeff r := by
  rw [extractionWeight, lagrangeBasis, coeff_C_mul, lagrangeNumerator, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec]

/-- The closed-form extraction weight is smooth where the roots are distinct. -/
theorem contDiffAt_weightFormula {κ : Type*} [Fintype κ] [DecidableEq κ] (z : κ → E → ℂ)
    (j : κ) (hz : ∀ i, ContDiffAt ℝ n (z i) x)
    (hne : ∏ i ∈ univ.erase j, (z j x - z i x) ≠ 0) (r : ℕ) :
    ContDiffAt ℝ n (fun y ↦ (∏ i ∈ univ.erase j, (z j y - z i y))⁻¹ *
      (∏ i ∈ univ.erase j, (X - C (z i y))).coeff r) x := by
  have hprod : ContDiffAt ℝ n (fun y ↦ ∏ i ∈ univ.erase j, (z j y - z i y)) x :=
    contDiffAt_prod fun i _ ↦ (hz j).sub (hz i)
  exact (hprod.inv hne).mul (contDiffAt_coeff_prod_X_sub_C _ z (fun i _ ↦ hz i) r)

end Weights

end WeakTiling

end

end SliceTrig

/-! ## Hankel determinants and Prony polynomials of exponential sums -/

section Prony

section

open Matrix Polynomial Finset

namespace WeakTiling

/-- The Hankel matrix `(a_{i+j})_{i,j<k}`. -/
def hankel (a : ℕ → ℂ) (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun i j ↦ a (i + j)

/-- The Prony matrix: Hankel rows `a_{i+j}` (`i < k`, `j ≤ k`) and the last row `(yʲ)_{j ≤ k}`. -/
def pronyMat (a : ℕ → ℂ) (k : ℕ) (y : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.of fun i j ↦ if (i : ℕ) < k then a (i + j) else y ^ (j : ℕ)

/-- The minors of the Prony matrix along its last row. -/
noncomputable def pronyMinor (a : ℕ → ℂ) (k : ℕ) (j : Fin (k + 1)) : ℂ :=
  ((pronyMat a k 0).submatrix (Fin.last k).succAbove j.succAbove).det

/-- The Prony polynomial `det (pronyMat a k X)`, written out along its last row. -/
noncomputable def pronyPoly (a : ℕ → ℂ) (k : ℕ) : ℂ[X] :=
  ∑ j : Fin (k + 1), C ((-1) ^ (k + (j : ℕ)) * pronyMinor a k j) * X ^ (j : ℕ)

theorem pronyMat_minor (a : ℕ → ℂ) (k : ℕ) (y : ℂ) (j : Fin (k + 1)) :
    (pronyMat a k y).submatrix (Fin.last k).succAbove j.succAbove =
      (pronyMat a k 0).submatrix (Fin.last k).succAbove j.succAbove := by
  ext i l
  simp [pronyMat, Fin.succAbove_last]

theorem eval_pronyPoly (a : ℕ → ℂ) (k : ℕ) (y : ℂ) :
    (pronyPoly a k).eval y = (pronyMat a k y).det := by
  rw [det_succ_row _ (Fin.last k), pronyPoly, eval_finsetSum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, pronyMat_minor, ← pronyMinor]
  simp only [pronyMat, of_apply, Fin.val_last, lt_irrefl, ite_false]
  ring

theorem pronyPoly_coeff_top (a : ℕ → ℂ) (k : ℕ) :
    (pronyPoly a k).coeff k = (hankel a k).det := by
  rw [pronyPoly, finsetSum_coeff, sum_eq_single (Fin.last k)]
  · rw [coeff_C_mul_X_pow, Fin.val_last, ite_eq_left rfl, ← two_mul, pow_mul, neg_one_sq, one_pow,
      one_mul, pronyMinor]
    congr 1
    ext i j
    simp [pronyMat, hankel, Fin.succAbove_last]
  · intro j _ hj
    rw [coeff_C_mul_X_pow, ite_eq_right]
    intro h
    apply hj
    ext
    simp [← h]
  · simp

theorem pronyPoly_natDegree_le (a : ℕ → ℂ) (k : ℕ) : (pronyPoly a k).natDegree ≤ k :=
  natDegree_sum_le_of_forall_le _ _ fun j _ ↦
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp j.2)

/-- A product through a smaller inner dimension is singular. -/
theorem det_mul_eq_zero_of_card_lt {k : ℕ} {m : Type*} [Fintype m] (A : Matrix (Fin k) m ℂ)
    (B : Matrix m (Fin k) ℂ) (h : Fintype.card m < k) : (A * B).det = 0 := by
  by_contra hne
  have hunit : IsUnit (A * B) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne)
  have h1 := Matrix.rank_of_isUnit (A * B) hunit
  have h2 := (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_card_width A)
  rw [h1, Fintype.card_fin] at h2
  omega

/-- The exponential sum `m ↦ ∑_{μ ∈ A} c_μ μᵐ`. -/
def expSeq (A : Finset ℂ) (c : ℂ → ℂ) (m : ℕ) : ℂ := ∑ μ ∈ A, c μ * μ ^ m

theorem hankel_expSeq_eq_mul (A : Finset ℂ) (c : ℂ → ℂ) (k : ℕ) :
    hankel (expSeq A c) k =
      (Matrix.of fun (i : Fin k) (μ : A) ↦ c μ * (μ : ℂ) ^ (i : ℕ)) *
        Matrix.of fun (μ : A) (j : Fin k) ↦ (μ : ℂ) ^ (j : ℕ) := by
  ext i j
  simp only [hankel, expSeq, of_apply, mul_apply]
  rw [← sum_coe_sort A]
  refine sum_congr rfl fun μ _ ↦ ?_
  rw [pow_add]
  ring

/-- **Hankel determinants beyond the number of frequencies vanish.** -/
theorem hankel_det_eq_zero (A : Finset ℂ) (c : ℂ → ℂ) {k : ℕ} (hk : A.card < k) :
    (hankel (expSeq A c) k).det = 0 := by
  rw [hankel_expSeq_eq_mul]
  exact det_mul_eq_zero_of_card_lt _ _ (by simpa using hk)

/-- **The Hankel determinant of the right size does not vanish.** -/
theorem hankel_det_ne_zero (A : Finset ℂ) (c : ℂ → ℂ) (hc : ∀ μ ∈ A, c μ ≠ 0) :
    (hankel (expSeq A c) A.card).det ≠ 0 := by
  classical
  set e : Fin A.card ≃ A := (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm with he
  set v : Fin A.card → ℂ := fun l ↦ (e l : ℂ) with hv
  have hvinj : Function.Injective v := fun l l' h ↦ e.injective (Subtype.ext h)
  have hfac : hankel (expSeq A c) A.card =
      (vandermonde v)ᵀ * (diagonal (fun l ↦ c (v l)) * vandermonde v) := by
    ext i j
    simp only [hankel, expSeq, of_apply, mul_apply, transpose_apply, vandermonde, diagonal_apply,
      ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
    rw [← sum_coe_sort A, ← e.sum_comp]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [pow_add]
    simp only [hv]
    ring
  rw [hfac, det_mul, det_mul, det_transpose, det_diagonal]
  refine mul_ne_zero (det_vandermonde_ne_zero_iff.mpr hvinj)
    (mul_ne_zero ?_ (det_vandermonde_ne_zero_iff.mpr hvinj))
  exact prod_ne_zero_iff.mpr fun l _ ↦ hc _ (e l).2

/-- **The frequencies are roots of the Prony polynomial.** -/
theorem pronyPoly_eval_eq_zero (A : Finset ℂ) (c : ℂ → ℂ) {μ : ℂ} (hμ : μ ∈ A) :
    (pronyPoly (expSeq A c) A.card).eval μ = 0 := by
  classical
  rw [eval_pronyPoly]
  have hfac : pronyMat (expSeq A c) A.card μ =
      (Matrix.of fun (i : Fin (A.card + 1)) (ν : A) ↦
        if (i : ℕ) < A.card then c ν * (ν : ℂ) ^ (i : ℕ) else if (ν : ℂ) = μ then 1 else 0) *
      Matrix.of fun (ν : A) (j : Fin (A.card + 1)) ↦ (ν : ℂ) ^ (j : ℕ) := by
    ext i j
    simp only [pronyMat, of_apply, mul_apply]
    by_cases hi : (i : ℕ) < A.card
    · simp only [ite_eq_left hi, expSeq]
      rw [← sum_coe_sort A]
      refine sum_congr rfl fun ν _ ↦ ?_
      rw [pow_add]
      ring
    · simp only [ite_eq_right hi, ite_mul, one_mul, zero_mul]
      rw [sum_coe_sort A (fun ν ↦ if ν = μ then ν ^ (j : ℕ) else 0), sum_ite_eq' A μ, ite_eq_left hμ]
  rw [hfac]
  exact det_mul_eq_zero_of_card_lt _ _ (by simp)

/-- **Prony's theorem.**  The Prony polynomial of size `|A|` is nonzero of degree `|A|`. Its roots
are exactly the frequencies, all of them simple. -/
theorem pronyPoly_spec (A : Finset ℂ) (c : ℂ → ℂ) (hc : ∀ μ ∈ A, c μ ≠ 0) :
    pronyPoly (expSeq A c) A.card ≠ 0 ∧
      (pronyPoly (expSeq A c) A.card).natDegree = A.card ∧
      (pronyPoly (expSeq A c) A.card).roots.toFinset = A ∧
      ∀ μ ∈ A, (derivative (pronyPoly (expSeq A c) A.card)).eval μ ≠ 0 := by
  classical
  set Q := pronyPoly (expSeq A c) A.card with hQ
  have htop : Q.coeff A.card ≠ 0 := by
    rw [hQ, pronyPoly_coeff_top]
    exact hankel_det_ne_zero A c hc
  have hQ0 : Q ≠ 0 := fun h ↦ htop (by rw [h, coeff_zero])
  have hdeg : Q.natDegree = A.card :=
    natDegree_eq_of_le_of_coeff_ne_zero (pronyPoly_natDegree_le _ _) htop
  have hsub : A ⊆ Q.roots.toFinset := fun μ hμ ↦
    Multiset.mem_toFinset.mpr ((mem_roots hQ0).mpr (pronyPoly_eval_eq_zero A c hμ))
  have hcard : Q.roots.toFinset.card ≤ A.card :=
    (Multiset.toFinset_card_le _).trans ((card_roots' Q).trans hdeg.le)
  have hroots : Q.roots.toFinset = A := (eq_of_subset_of_card_le hsub hcard).symm
  have hnodup : Q.roots.Nodup := by
    have h1 : Q.roots.toFinset.card = Multiset.card Q.roots := by
      have h2 := Multiset.toFinset_card_le Q.roots
      have h3 := card_roots' Q
      rw [hroots] at h2 ⊢
      omega
    exact Multiset.toFinset_card_eq_card_iff_nodup.mp h1
  have hsep : Q.Separable := (nodup_roots_iff_of_splits hQ0 (IsAlgClosed.splits Q)).mp hnodup
  refine ⟨hQ0, hdeg, hroots, fun μ hμ ↦ ?_⟩
  have hroot : Q.eval μ = 0 := pronyPoly_eval_eq_zero A c hμ
  have := hsep.aeval_derivative_ne_zero (x := μ) (by simpa [aeval_def] using hroot)
  simpa [aeval_def] using this

end WeakTiling

end

end Prony

/-! ## Tools for constructing the active branches -/

section ActiveTools

section

open Complex Finset Polynomial Filter Topology
open scoped Real

namespace WeakTiling

variable {ι : Type} [Fintype ι]

/-- Real angles viewed as complex angles. -/
def ofRealVec (θ : ι → ℝ) : ι → ℂ := fun k ↦ (θ k : ℂ)

theorem contDiff_ofRealVec {n : WithTop ℕ∞} : ContDiff ℝ n (ofRealVec (ι := ι)) := by
  unfold ofRealVec
  exact contDiff_pi.mpr fun k ↦ ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ k)

/-- The degree slice with complexified angles. -/
noncomputable def sliceC (D : LatticeTilingData ι) (w : ι → ℂ) (m : ℤ) : ℂ :=
  ∑ u ∈ sliceFiber m, (D.M u : ℂ) * exp (I * ∑ k, (u k : ℂ) * w k)

theorem sliceC_ofRealVec (D : LatticeTilingData ι) (θ : ι → ℝ) (m : ℤ) :
    sliceC D (ofRealVec θ) m = latticeSlice D (torusPt θ) m := by
  rw [← mvTrigPoly_sliceFiber, sliceC, mvTrigPoly]
  refine sum_congr rfl fun u _ ↦ ?_
  congr 1
  rw [mvChar]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [ofRealVec]
  push_cast
  field_simp

theorem contDiff_sliceC (D : LatticeTilingData ι) (m : ℤ) {n : WithTop ℕ∞} :
    ContDiff ℂ n (fun w : ι → ℂ ↦ sliceC D w m) := by
  unfold sliceC
  refine ContDiff.sum fun u _ ↦ contDiff_const.mul ?_
  refine Complex.contDiff_exp.comp (contDiff_const.mul ?_)
  exact ContDiff.sum fun k _ ↦ contDiff_const.mul (contDiff_apply ℂ ℂ k)

/-- **Determinants of smooth entries are smooth.** -/
theorem contDiff_det_of_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n : WithTop ℕ∞} {A : E → Matrix κ κ ℂ}
    (hA : ∀ i j, ContDiff ℂ n (fun w ↦ A w i j)) : ContDiff ℂ n (fun w ↦ (A w).det) := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun σ _ ↦ ?_
  simp only [Units.smul_def]
  exact (contDiff_prod fun i _ ↦ hA (σ i) i).const_smul _

/-- The Prony polynomial of the complexified slices, evaluated at `p.2`. -/
noncomputable def pronyF (D : LatticeTilingData ι) (k : ℕ) (p : (ι → ℂ) × ℂ) : ℂ :=
  (pronyPoly (fun m ↦ sliceC D p.1 m) k).eval p.2

theorem pronyF_eq (D : LatticeTilingData ι) (k : ℕ) (p : (ι → ℂ) × ℂ) :
    pronyF D k p = ∑ j : Fin (k + 1),
      (-1) ^ (k + (j : ℕ)) * pronyMinor (fun m ↦ sliceC D p.1 m) k j * p.2 ^ (j : ℕ) := by
  simp [pronyF, pronyPoly, eval_finsetSum]

theorem contDiff_pronyMinor (D : LatticeTilingData ι) (k : ℕ) (j : Fin (k + 1))
    {n : WithTop ℕ∞} : ContDiff ℂ n (fun w : ι → ℂ ↦ pronyMinor (fun m ↦ sliceC D w m) k j) := by
  unfold pronyMinor
  refine contDiff_det_of_entries fun a b ↦ ?_
  simp only [Matrix.submatrix_apply, pronyMat, Matrix.of_apply]
  split_ifs
  · exact contDiff_sliceC D _
  · exact contDiff_const

theorem contDiff_pronyF (D : LatticeTilingData ι) (k : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℂ n (pronyF D k) := by
  have : pronyF D k = fun p ↦ ∑ j : Fin (k + 1),
      (-1) ^ (k + (j : ℕ)) * pronyMinor (fun m ↦ sliceC D p.1 m) k j * p.2 ^ (j : ℕ) :=
    funext (pronyF_eq D k)
  rw [this]
  refine ContDiff.sum fun j _ ↦ (contDiff_const.mul ?_).mul (contDiff_snd.pow _)
  exact (contDiff_pronyMinor D k j).comp contDiff_fst

/-- **A simple root moves smoothly** (implicit function theorem). -/
theorem exists_root_branch {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : E × ℂ → ℂ} {u : E × ℂ} (hf : ContDiffAt ℂ 2 f u) {d : ℂ}
    (hd : d ≠ 0) (hder : HasDerivAt (fun x ↦ f (u.1, x)) d u.2) :
    ∃ ψ : E → ℂ, ψ u.1 = u.2 ∧ ContDiffAt ℂ 2 ψ u.1 ∧ ∀ᶠ w in 𝓝 u.1, f (w, ψ w) = f u := by
  have hdiff : DifferentiableAt ℂ f u := hf.differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun x ↦ f (u.1, x)) ((fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ))
      u.2 := hdiff.hasFDerivAt.comp u.2 (hasFDerivAt_prodMk_right u.1 u.2)
  have h2 := hder.hasFDerivAt
  have hpart : (fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d := h1.unique h2
  have hinv : ((fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ)).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d hd), ?_⟩
    ext
    simp
  exact ⟨hf.implicitFunction (by norm_num) hinv, hf.implicitFunction_apply_self _ _,
    hf.contDiffAt_implicitFunction _ _, hf.eventually_apply_implicitFunction _ _⟩

end WeakTiling

end

end ActiveTools

/-! ## Smooth phase lifts of unimodular functions -/

section PhaseLift

section

open Complex

namespace WeakTiling

variable {E : Type*}

/-- The phase lift of `r` based at `x₀`. -/
noncomputable def phaseLift (r : E → ℂ) (x₀ : E) (x : E) : ℝ :=
  arg (r x₀) + (log (r x / r x₀)).im

theorem exp_arg_mul_I_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) : exp ((arg w : ℂ) * I) = w := by
  have := norm_mul_exp_arg_mul_I w
  rw [hw, ofReal_one, one_mul] at this
  exact this

theorem phaseLift_spec {r : E → ℂ} {x₀ : E} (h0 : ‖r x₀‖ = 1) {x : E} (hx : ‖r x‖ = 1) :
    r x = exp ((phaseLift r x₀ x : ℂ) * I) := by
  have hr0 : r x₀ ≠ 0 := fun h ↦ by simp [h] at h0
  set w := r x / r x₀ with hw
  have hwn : ‖w‖ = 1 := by rw [hw, norm_div, hx, h0, div_one]
  have hlog : (log w).im = arg w := log_im w
  rw [phaseLift, hlog]
  push_cast
  rw [add_mul, exp_add, exp_arg_mul_I_of_norm_one h0, exp_arg_mul_I_of_norm_one hwn, hw,
    mul_div_cancel₀ _ hr0]

theorem phaseLift_contDiffAt [NormedAddCommGroup E] [NormedSpace ℝ E] {r : E → ℂ} {x₀ x : E}
    {n : WithTop ℕ∞} (hr : ContDiffAt ℝ n r x)
    (hslit : r x / r x₀ ∈ slitPlane) : ContDiffAt ℝ n (phaseLift r x₀) x := by
  have hlog0 : ContDiffAt ℝ n log (r x / r x₀) := (contDiffAt_log (n := n) hslit).restrict_scalars ℝ
  have hlog : ContDiffAt ℝ n (fun x ↦ log (r x / r x₀)) x := by
    have := hlog0.comp x (hr.div_const (r x₀))
    simpa [Function.comp_def] using this
  have him : ContDiffAt ℝ n (fun x ↦ (log (r x / r x₀)).im) x :=
    (imCLM.contDiff.contDiffAt).comp x hlog
  exact contDiffAt_const.add him

end WeakTiling

end

end PhaseLift

/-! ## Summable Fourier coefficients of `C²` functions -/

section SmoothFourier

section

open Complex MeasureTheory intervalIntegral Set
open scoped Real

namespace WeakTiling

variable {p q : ℝ}

/-- One integration by parts for periodic data. -/
theorem fourierCoeffOn_eq_mul_deriv (hpq : p < q) {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x ∈ uIcc p q, HasDerivAt f (f' x) x) (hf' : IntervalIntegrable f' volume p q)
    (hfpq : f q = f p) :
    fourierCoeffOn hpq f n = ((q - p : ℝ) : ℂ) / (2 * π * I * n) * fourierCoeffOn hpq f' n := by
  rw [fourierCoeffOn_of_hasDerivAt hpq hn hf hf', hfpq, sub_self, mul_zero, zero_sub]
  have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  push_cast
  ring

/-- The trivial bound `|f̂(n)| ≤ (q - p)⁻¹ ∫ |f|`. -/
theorem norm_fourierCoeffOn_le (hpq : p < q) (f : ℝ → ℂ) (n : ℤ) :
    ‖fourierCoeffOn hpq f n‖ ≤ (q - p)⁻¹ * ∫ x in p..q, ‖f x‖ := by
  rw [fourierCoeffOn_eq_integral _ _ hpq, norm_smul, one_div, norm_inv, Real.norm_of_nonneg
    (sub_pos.mpr hpq).le]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (sub_pos.mpr hpq).le)
  refine (intervalIntegral.norm_integral_le_integral_norm hpq.le).trans (le_of_eq ?_)
  refine integral_congr fun x _ ↦ ?_
  simp only [norm_smul, fourier_coe_apply]
  have harg : 2 * (π : ℂ) * I * ((-n : ℤ) : ℂ) * (x : ℂ) / ((q - p : ℝ) : ℂ) =
      ((2 * π * (-n : ℤ) * x / (q - p) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **`C²` data have absolutely summable Fourier coefficients.** -/
theorem summable_fourierCoeffOn_of_deriv2 (hpq : p < q) {f f' f'' : ℝ → ℂ}
    (hf : ∀ x ∈ uIcc p q, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ uIcc p q, HasDerivAt f' (f'' x) x)
    (hf'' : ContinuousOn f'' (uIcc p q)) (hfpq : f q = f p) (hf'pq : f' q = f' p) :
    Summable fun n ↦ ‖fourierCoeffOn hpq f n‖ := by
  have hint' : IntervalIntegrable f' volume p q :=
    ContinuousOn.intervalIntegrable fun x hx ↦ (hf' x hx).continuousAt.continuousWithinAt
  have hint'' : IntervalIntegrable f'' volume p q := hf''.intervalIntegrable
  set B : ℝ := (q - p)⁻¹ * ∫ x in p..q, ‖f'' x‖ with hB
  set K : ℝ := ((q - p) / (2 * π)) ^ 2 * B with hK
  have hbound : ∀ n : ℤ, n ≠ 0 → ‖fourierCoeffOn hpq f n‖ ≤ K * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    rw [fourierCoeffOn_eq_mul_deriv hpq hn hf hint' hfpq,
      fourierCoeffOn_eq_mul_deriv hpq hn hf' hint'' hf'pq, ← mul_assoc]
    have hn' : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
    have hfac : ‖((q - p : ℝ) : ℂ) / (2 * π * I * n) * (((q - p : ℝ) : ℂ) / (2 * π * I * n))‖ =
        ((q - p) / (2 * π)) ^ 2 * (1 / (n : ℝ) ^ 2) := by
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      have hπ : ‖(π : ℂ)‖ = π := by rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      rw [norm_mul, norm_div, norm_mul, norm_mul, norm_mul, h2, hπ, norm_I, Complex.norm_real,
        Complex.norm_intCast, Real.norm_of_nonneg (sub_pos.mpr hpq).le, mul_one,
        div_mul_div_comm]
      have hn2 : 2 * π * |(n : ℝ)| * (2 * π * |(n : ℝ)|) = (2 * π) ^ 2 * (n : ℝ) ^ 2 := by
        have : |(n : ℝ)| * |(n : ℝ)| = (n : ℝ) ^ 2 := by rw [← sq, sq_abs]
        calc 2 * π * |(n : ℝ)| * (2 * π * |(n : ℝ)|) = (2 * π) ^ 2 * (|(n : ℝ)| * |(n : ℝ)|) := by
              ring
          _ = (2 * π) ^ 2 * (n : ℝ) ^ 2 := by rw [this]
      rw [hn2, div_pow]
      ring
    rw [norm_mul, hfac, hK]
    have := norm_fourierCoeffOn_le hpq f'' n
    rw [← hB] at this
    have h1 : 0 ≤ ((q - p) / (2 * π)) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
    calc ((q - p) / (2 * π)) ^ 2 * (1 / (n : ℝ) ^ 2) * ‖fourierCoeffOn hpq f'' n‖
        ≤ ((q - p) / (2 * π)) ^ 2 * (1 / (n : ℝ) ^ 2) * B :=
          mul_le_mul_of_nonneg_left this (mul_nonneg h1 h2)
      _ = ((q - p) / (2 * π)) ^ 2 * B * (1 / (n : ℝ) ^ 2) := by ring
  have hsum : Summable fun n : ℤ ↦ K * (1 / (n : ℝ) ^ 2) +
      (if n = 0 then ‖fourierCoeffOn hpq f 0‖ else 0) := by
    refine (Summable.mul_left K (Real.summable_one_div_int_pow.mpr (by norm_num))).add ?_
    exact summable_of_ne_finset_zero (s := {0}) fun n hn ↦ by
      rw [Finset.mem_singleton] at hn
      simp [hn]
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hsum
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [ite_eq_right hn, add_zero]
    exact hbound n hn

end WeakTiling

end

end SmoothFourier

/-! ## Localized weights -/

section LocalizedWeights

section

open Set Filter Topology MeasureTheory

namespace WeakTiling

/-- **Gluing a cutoff.** -/
theorem contDiff_mul_of_tsupport {χ W : ℝ → ℂ} {O : Set ℝ} {n : WithTop ℕ∞}
    (hχ : ContDiff ℝ n χ) (hsupp : tsupport χ ⊆ O) (hW : ∀ t ∈ O, ContDiffAt ℝ n W t) :
    ContDiff ℝ n (fun t ↦ χ t * W t) := by
  refine contDiff_iff_contDiffAt.2 fun t ↦ ?_
  by_cases ht : t ∈ O
  · exact hχ.contDiffAt.mul (hW t ht)
  · have h0 : χ =ᶠ[𝓝 t] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h ↦ ht (hsupp h)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with y hy
    simp [hy]

/-- **`C²` functions vanishing near the ends have summable Fourier coefficients.** -/
theorem summable_fourierCoeffOn_of_contDiff {p q : ℝ} (hpq : p < q) {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hp : F =ᶠ[𝓝 p] 0) (hq : F =ᶠ[𝓝 q] 0) :
    Summable fun n ↦ ‖fourierCoeffOn hpq F n‖ := by
  have h2 : ContDiff ℝ (1 + 1) F := by rw [one_add_one_eq_two]; exact hF
  obtain ⟨hdF, -, hF1⟩ := contDiff_succ_iff_deriv.mp h2
  obtain ⟨hdF', hcF''⟩ := contDiff_one_iff_deriv.mp hF1
  have hpd : deriv F p = 0 := by rw [hp.deriv_eq]; simp
  have hqd : deriv F q = 0 := by rw [hq.deriv_eq]; simp
  refine summable_fourierCoeffOn_of_deriv2 hpq (f' := deriv F) (f'' := deriv (deriv F))
    (fun x _ ↦ (hdF x).hasDerivAt) (fun x _ ↦ (hdF' x).hasDerivAt) hcF''.continuousOn ?_ ?_
  · rw [hp.eq_of_nhds, hq.eq_of_nhds]
    rfl
  · rw [hpd, hqd]

/-- **Positivity of an integral.** -/
theorem integral_pos_of_continuous_of_pos {G : ℝ → ℝ} {p q t₀ : ℝ} (hG : Continuous G)
    (hG0 : ∀ t, 0 ≤ G t) (ht₀ : t₀ ∈ Ioo p q) (hpos : 0 < G t₀) : 0 < ∫ t in p..q, G t := by
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ t, |t - t₀| < ε → 0 < G t := by
    have hev := hG.continuousAt (x := t₀) |>.eventually (lt_mem_nhds hpos)
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp hev
    exact ⟨ε, hε, fun t ht ↦ h (by simpa [Real.dist_eq] using ht)⟩
  obtain ⟨hp, hq⟩ := ht₀
  set ε' := min ε (min (t₀ - p) (q - t₀)) / 2 with hε'
  have hm1 := min_le_left ε (min (t₀ - p) (q - t₀))
  have hm2 := min_le_left (t₀ - p) (q - t₀)
  have hm3 := min_le_right (t₀ - p) (q - t₀)
  have hm4 := min_le_right ε (min (t₀ - p) (q - t₀))
  have hmpos : 0 < min ε (min (t₀ - p) (q - t₀)) := lt_min hε (lt_min (by linarith) (by linarith))
  have hε'pos : 0 < ε' := by positivity
  have hsmall : 0 < ∫ t in (t₀ - ε')..(t₀ + ε'), G t := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hG.intervalIntegrable _ _)
      (fun t ht ↦ hball t ?_) (by linarith)
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  refine hsmall.trans_le (intervalIntegral.integral_mono_interval (by linarith) (by linarith)
    (by linarith) (Eventually.of_forall hG0) (hG.intervalIntegrable _ _))

end WeakTiling

end

end LocalizedWeights

/-! ## A nonlinear phase is curved along an integer direction -/

section PhaseLinearity

section

open Set Filter Topology

namespace WeakTiling

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- An integer direction viewed as a real vector. -/
def intDir (v : σ → ℤ) : σ → ℝ :=
  fun k ↦ (v k : ℝ)

/-- The second directional derivative `D²_v φ(x)`. -/
noncomputable def secondDeriv (φ : (σ → ℝ) → ℝ) (x v : σ → ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ φ) x v v

/-- The test directions `eᵢ` and `eᵢ + eⱼ`. -/
def IsTestDirection (v : σ → ℤ) : Prop :=
  (∃ i, v = Pi.single i 1) ∨ ∃ i j, v = Pi.single i 1 + Pi.single j 1

theorem intDir_single (i : σ) : intDir (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℝ) := by
  funext k
  by_cases h : k = i
  · subst h; simp [intDir]
  · simp [intDir, Pi.single_apply]

theorem intDir_add (v w : σ → ℤ) : intDir (v + w) = intDir v + intDir w := by
  funext k
  simp [intDir]

theorem single_eq_smul (i : σ) (a : ℝ) : Pi.single i a = a • Pi.single i (1 : ℝ) := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_apply]

/-- A symmetric bilinear form vanishing on all test directions is zero. -/
theorem bilinear_eq_zero_of_test (B : (σ → ℝ) →L[ℝ] (σ → ℝ) →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v)
    (h : ∀ v : σ → ℤ, IsTestDirection v → B (intDir v) (intDir v) = 0) : B = 0 := by
  have hii : ∀ i, B (Pi.single i 1) (Pi.single i 1) = 0 := fun i ↦ by
    simpa [intDir_single] using h (Pi.single i 1) (Or.inl ⟨i, rfl⟩)
  have hij : ∀ i j, B (Pi.single i 1) (Pi.single j 1) = 0 := by
    intro i j
    have := h (Pi.single i 1 + Pi.single j 1) (Or.inr ⟨i, j, rfl⟩)
    simp only [intDir_add, intDir_single, map_add, ContinuousLinearMap.add_apply] at this
    rw [hii i, hii j, hsymm (Pi.single j 1) (Pi.single i 1)] at this
    linarith
  ext v w
  rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply,
    ← Finset.univ_sum_single v, ← Finset.univ_sum_single w]
  simp only [map_sum, ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
  rw [single_eq_smul i, single_eq_smul j, map_smul, map_smul, ContinuousLinearMap.smul_apply,
    hij, smul_zero, smul_zero]

/-- **Vanishing test curvatures force an affine phase.** -/
theorem affine_of_secondDeriv_test_zero {U : Set (σ → ℝ)} (hU : IsOpen U) (hconv : Convex ℝ U)
    {φ : (σ → ℝ) → ℝ} (hφ : ContDiffOn ℝ 2 φ U)
    (h0 : ∀ x ∈ U, ∀ v : σ → ℤ, IsTestDirection v → secondDeriv φ x (intDir v) = 0) :
    ∃ (c : ℝ) (L : (σ → ℝ) →L[ℝ] ℝ), ∀ x ∈ U, φ x = c + L x := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, 0, fun x hx ↦ absurd hx (Set.notMem_empty x)⟩
  have hH : ∀ x ∈ U, fderiv ℝ (fderiv ℝ φ) x = 0 := by
    intro x hx
    have hsymm := (hφ.contDiffAt (hU.mem_nhds hx)).isSymmSndFDerivAt (by simp)
    exact bilinear_eq_zero_of_test _ (fun v w ↦ hsymm v w) (h0 x hx)
  have hdiff1 : DifferentiableOn ℝ (fderiv ℝ φ) U :=
    (hφ.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num)
  have hconst : ∀ x ∈ U, fderiv ℝ φ x = fderiv ℝ φ x₀ := fun x hx ↦
    hconv.is_const_of_fderivWithin_eq_zero hdiff1
      (fun y hy ↦ by rw [fderivWithin_of_isOpen hU hy, hH y hy]) hx hx₀
  set L := fderiv ℝ φ x₀ with hL
  have hφd : DifferentiableOn ℝ φ U := hφ.differentiableOn (by norm_num)
  have hg : ∀ x ∈ U, φ x - L x = φ x₀ - L x₀ := by
    intro x hx
    refine hconv.is_const_of_fderivWithin_eq_zero (hφd.sub L.differentiable.differentiableOn)
      (fun y hy ↦ ?_) hx hx₀
    rw [fderivWithin_of_isOpen hU hy,
      fderiv_sub (hφd.differentiableAt (hU.mem_nhds hy)) L.differentiableAt,
      ContinuousLinearMap.fderiv, hconst y hy, sub_self]
  exact ⟨φ x₀ - L x₀, L, fun x hx ↦ by linarith [hg x hx]⟩

/-- **A nonlinear phase has a curved test direction.** -/
theorem exists_test_direction_curved {U : Set (σ → ℝ)} (hU : IsOpen U) (hconv : Convex ℝ U)
    {φ : (σ → ℝ) → ℝ} (hφ : ContDiffOn ℝ 2 φ U)
    (hna : ¬ ∃ (c : ℝ) (L : (σ → ℝ) →L[ℝ] ℝ), ∀ x ∈ U, φ x = c + L x) :
    ∃ x ∈ U, ∃ v : σ → ℤ, IsTestDirection v ∧ secondDeriv φ x (intDir v) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hna (affine_of_secondDeriv_test_zero hU hconv hφ hcon)

/-- **Curvature on a segment.**  If `D²_v φ(x) ≠ 0` at an interior point, then on some segment
`[-δ, δ]` the restriction `s ↦ φ(x + s v)` has derivative `s ↦ Dφ(x+sv) v` and second derivative
`s ↦ D²_v φ(x+sv)`.  The second derivative is continuous and bounded away from zero by `m > 0`. -/
theorem exists_curved_segment {U : Set (σ → ℝ)} (hU : IsOpen U) {φ : (σ → ℝ) → ℝ}
    (hφ : ContDiffOn ℝ 2 φ U) {x : σ → ℝ} (hx : x ∈ U) {v : σ → ℝ}
    (hv : secondDeriv φ x v ≠ 0) :
    ∃ δ > (0 : ℝ), ∃ m > (0 : ℝ),
      (∀ s ∈ Icc (-δ) δ, x + s • v ∈ U) ∧
      (∀ s ∈ Icc (-δ) δ,
        HasDerivAt (fun s ↦ φ (x + s • v)) (fderiv ℝ φ (x + s • v) v) s) ∧
      (∀ s ∈ Icc (-δ) δ,
        HasDerivAt (fun s ↦ fderiv ℝ φ (x + s • v) v) (secondDeriv φ (x + s • v) v) s) ∧
      ContinuousOn (fun s ↦ secondDeriv φ (x + s • v) v) (Icc (-δ) δ) ∧
      ∀ s ∈ Icc (-δ) δ, m ≤ |secondDeriv φ (x + s • v) v| := by
  set ℓ : ℝ → (σ → ℝ) := fun s ↦ x + s • v with hℓ
  have hℓc : Continuous ℓ := by rw [hℓ]; fun_prop
  have hℓd : ∀ s, HasDerivAt ℓ v s := fun s ↦ by
    have := ((hasDerivAt_id s).smul_const v).const_add x
    simp only [id, one_smul] at this
    exact this
  have hH1 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have hHc : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) U :=
    hH1.continuousOn_fderiv_of_isOpen hU (by norm_num)
  set F : ℝ → ℝ := fun s ↦ secondDeriv φ (ℓ s) v with hF
  -- a neighbourhood of `0` mapped into `U`
  have hpre : IsOpen (ℓ ⁻¹' U) := hU.preimage hℓc
  have h0 : (0 : ℝ) ∈ ℓ ⁻¹' U := by simp [hℓ, hx]
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.mp hpre 0 h0
  have hFc : ContinuousOn F (ℓ ⁻¹' U) := by
    have hcomp : ContinuousOn (fun s ↦ fderiv ℝ (fderiv ℝ φ) (ℓ s)) (ℓ ⁻¹' U) :=
      hHc.comp hℓc.continuousOn (fun s hs ↦ hs)
    exact (hcomp.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hF0 : F 0 ≠ 0 := by simpa [hF, hℓ] using hv
  have hFcont0 : ContinuousAt F 0 := hFc.continuousAt (hpre.mem_nhds h0)
  obtain ⟨δ₂, hδ₂, hclose⟩ := Metric.continuousAt_iff.mp hFcont0 (|F 0| / 2)
    (by positivity)
  set δ := min δ₁ δ₂ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hmem : ∀ s ∈ Icc (-δ) δ, s ∈ Metric.ball (0 : ℝ) δ₁ ∧ dist s 0 < δ₂ := by
    intro s hs
    have habs : |s| ≤ δ := abs_le.mpr ⟨hs.1, hs.2⟩
    have h1 : δ < δ₁ := by
      have := min_le_left δ₁ δ₂
      rw [hδ]; linarith
    have h2 : δ < δ₂ := by
      have := min_le_right δ₁ δ₂
      rw [hδ]; linarith
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith
    · rw [Real.dist_eq, sub_zero]; linarith
  have hU' : ∀ s ∈ Icc (-δ) δ, ℓ s ∈ U := fun s hs ↦ hball (hmem s hs).1
  refine ⟨δ, hδpos, |F 0| / 2, by positivity, hU', ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hdφ : HasFDerivAt φ (fderiv ℝ φ (ℓ s)) (ℓ s) :=
      ((hφ.differentiableOn (by norm_num)).differentiableAt
        (hU.mem_nhds (hU' s hs))).hasFDerivAt
    exact hdφ.comp_hasDerivAt s (hℓd s)
  · intro s hs
    have hdφ' : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (ℓ s)) (ℓ s) :=
      ((hH1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hU' s hs))).hasFDerivAt
    have happ := hdφ'.clm_apply (hasFDerivAt_const v (ℓ s))
    have hval : ((fderiv ℝ φ (ℓ s)).comp (0 : (σ → ℝ) →L[ℝ] (σ → ℝ)) +
        (fderiv ℝ (fderiv ℝ φ) (ℓ s)).flip v) v =
        secondDeriv φ (ℓ s) v := by
      simp [secondDeriv]
    have key : HasDerivAt ((fun y ↦ fderiv ℝ φ y v) ∘ ℓ) (secondDeriv φ (ℓ s) v) s := by
      have := happ.comp_hasDerivAt s (hℓd s)
      rwa [hval] at this
    exact key
  · exact hFc.mono fun s hs ↦ hU' s hs
  · intro s hs
    have hd := hclose (hmem s hs).2
    rw [Real.dist_eq] at hd
    have := abs_sub_abs_le_abs_sub (F 0) (F s)
    rw [abs_sub_comm] at hd
    change |F 0| / 2 ≤ |F s|
    linarith [abs_sub_comm (F s) (F 0)]

end WeakTiling

end

end PhaseLinearity

/-! ## Step H: surviving characteristic phases are affine -/

section PhaseH

section

open Complex Finset Filter Topology Metric Set
open scoped Real

namespace WeakTiling

variable {ι : Type} [Fintype ι]

/-- **Active branches** of lattice tiling data on an open set `N` of angles. -/
structure ActiveBranches (D : LatticeTilingData ι) (N : Set (ι → ℝ)) where
  /-- The number of active roots. -/
  r : ℕ
  /-- The active roots. -/
  root : Fin r → (ι → ℝ) → ℂ
  /-- Their amplitudes. -/
  amp : Fin r → (ι → ℝ) → ℂ
  root_smooth : ∀ l, ∀ θ ∈ N, ContDiffAt ℝ 2 (root l) θ
  amp_smooth : ∀ l, ∀ θ ∈ N, ContDiffAt ℝ 2 (amp l) θ
  root_ne : ∀ θ ∈ N, ∀ l l', l ≠ l' → root l θ ≠ root l' θ
  root_unit : ∀ l, ∀ θ ∈ N, ‖root l θ‖ = 1
  amp_ne : ∀ l, ∀ θ ∈ N, amp l θ ≠ 0
  rep : ∀ θ ∈ N, ∀ n : ℕ, latticeSlice D (torusPt θ) n = ∑ l, amp l θ * root l θ ^ n

omit [Fintype ι] in
theorem line_eq (x : ι → ℝ) (v : ι → ℤ) (s : ℝ) :
    (fun i ↦ x i + s * (v i : ℝ)) = x + s • intDir v := by
  funext i
  simp [intDir, smul_eq_mul]

namespace ActiveBranches

variable {D : LatticeTilingData ι} {N : Set (ι → ℝ)}

/-- **Step H.**  Every active root has an affine phase near every point of `N`. -/
theorem phase_affine [Nonempty ι] [DecidableEq ι] (hN : IsOpen N) (B : ActiveBranches D N)
    (l : Fin B.r) {θ₀ : ι → ℝ} (hθ₀ : θ₀ ∈ N) :
    ∃ ε > 0, ball θ₀ ε ⊆ N ∧ ∃ (c : ℝ) (L : (ι → ℝ) →L[ℝ] ℝ),
      ∀ θ ∈ ball θ₀ ε, B.root l θ = exp (((c + L θ : ℝ) : ℂ) * I) := by
  classical
  -- a ball on which the phase lift is defined and smooth
  have hr0 : B.root l θ₀ ≠ 0 := fun h ↦ by simpa [h] using B.root_unit l θ₀ hθ₀
  have hslit : {θ | B.root l θ / B.root l θ₀ ∈ slitPlane} ∈ 𝓝 θ₀ := by
    have h1 : B.root l θ₀ / B.root l θ₀ ∈ slitPlane := by
      rw [div_self hr0]
      exact one_mem_slitPlane
    exact ((B.root_smooth l θ₀ hθ₀).continuousAt.div_const _).preimage_mem_nhds
      (isOpen_slitPlane.mem_nhds h1)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hN.mem_nhds hθ₀) hslit)
  refine ⟨ε, hε, fun θ hθ ↦ (hball hθ).1, ?_⟩
  set U := ball θ₀ ε with hU
  have hUN : ∀ θ ∈ U, θ ∈ N := fun θ hθ ↦ (hball hθ).1
  have hUs : ∀ θ ∈ U, B.root l θ / B.root l θ₀ ∈ slitPlane := fun θ hθ ↦ (hball hθ).2
  set φ := phaseLift (B.root l) θ₀ with hφdef
  have hφ : ContDiffOn ℝ 2 φ U := fun θ hθ ↦
    (phaseLift_contDiffAt (B.root_smooth l θ (hUN θ hθ)) (hUs θ hθ)).contDiffWithinAt
  have hrepφ : ∀ θ ∈ U, B.root l θ = exp ((φ θ : ℂ) * I) := fun θ hθ ↦
    phaseLift_spec (B.root_unit l θ₀ hθ₀) (B.root_unit l θ (hUN θ hθ))
  suffices haff : ∃ (c : ℝ) (L : (ι → ℝ) →L[ℝ] ℝ), ∀ θ ∈ U, φ θ = c + L θ by
    obtain ⟨c, L, h⟩ := haff
    exact ⟨c, L, fun θ hθ ↦ by rw [hrepφ θ hθ, h θ hθ]⟩
  by_contra hna
  -- a curved segment
  obtain ⟨x, hxU, v, -, hv⟩ := exists_test_direction_curved isOpen_ball (convex_ball θ₀ ε) hφ hna
  obtain ⟨δ, hδ, m, hm, hseg, hd1, hd2, hcont2, hcurv⟩ :=
    exists_curved_segment isOpen_ball hφ hxU hv
  set δ' := min (δ / 2) 1 with hδ'
  have hδ'pos : 0 < δ' := lt_min (by linarith) one_pos
  have hδ'δ : δ' < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hπ3 : (3 : ℝ) < π := Real.pi_gt_three
  set line : ℝ → (ι → ℝ) := fun s ↦ x + s • intDir v with hline
  have hlineU : ∀ s ∈ Ioo (-δ) δ, line s ∈ U := fun s hs ↦ hseg s ⟨hs.1.le, hs.2.le⟩
  have hlineN : ∀ s ∈ Ioo (-δ) δ, line s ∈ N := fun s hs ↦ hUN _ (hlineU s hs)
  have hline_smooth : ContDiff ℝ 2 line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hsub : Icc (-δ') δ' ⊆ Ioo (-δ) δ := fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsubI : Icc (-δ') δ' ⊆ Icc (-δ) δ := fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- the cutoff
  let bump : ContDiffBump (0 : ℝ) := ⟨δ' / 4, δ' / 2, by positivity, by linarith⟩
  set χc : ℝ → ℂ := fun t ↦ ((bump t : ℝ) : ℂ) with hχc
  have hχc_smooth : ContDiff ℝ 2 χc := ofRealCLM.contDiff.comp bump.contDiff
  have hχc_zero : ∀ t, δ' / 2 ≤ |t| → χc t = 0 := by
    intro t ht
    have : t ∉ Function.support bump := by
      rw [bump.support_eq, mem_ball_zero_iff, Real.norm_eq_abs, not_lt]
      exact ht
    simp [hχc, Function.notMem_support.mp this]
  have hχc_tsupport : tsupport χc ⊆ closedBall 0 (δ' / 2) := by
    refine closure_minimal (fun t ht ↦ ?_) isClosed_closedBall
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    by_contra h
    exact ht (hχc_zero t (not_le.mp h).le)
  have hχc_tsupport' : tsupport χc ⊆ Ioo (-δ) δ := fun t ht ↦ by
    have := hχc_tsupport ht
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hχc0 : χc 0 = 1 := by
    have : bump 0 = 1 := bump.one_of_mem_closedBall (mem_closedBall_self (by positivity))
    simp [hχc, this]
  have hχc_out : ∀ t, t ∉ Ioo (-δ') δ' → χc t = 0 := by
    intro t ht
    refine hχc_zero t ?_
    by_contra h
    apply ht
    rw [not_le, abs_lt] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hvanish : ∀ t, t = -π ∨ t = π → χc =ᶠ[𝓝 t] 0 := by
    intro t ht
    refine notMem_tsupport_iff_eventuallyEq.mp fun h ↦ ?_
    have := hχc_tsupport h
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
    rcases ht with rfl | rfl
    · rw [abs_neg, abs_of_pos Real.pi_pos] at this
      linarith
    · rw [abs_of_pos Real.pi_pos] at this
      linarith
  -- the localized amplitude
  set g : ℝ → ℂ := fun t ↦ χc t * B.amp l (line t) with hg
  have hg_smooth : ContDiff ℝ 2 g := contDiff_mul_of_tsupport hχc_smooth hχc_tsupport'
    fun t ht ↦ (B.amp_smooth l (line t) (hlineN t ht)).comp t hline_smooth.contDiffAt
  -- the localized extraction weights
  have hroot_line : ∀ i, ∀ t ∈ Ioo (-δ) δ, ContDiffAt ℝ 2 (fun t ↦ B.root i (line t)) t :=
    fun i t ht ↦ (B.root_smooth i (line t) (hlineN t ht)).comp t hline_smooth.contDiffAt
  have hprod_ne : ∀ t ∈ Ioo (-δ) δ,
      ∏ i ∈ univ.erase l, (B.root l (line t) - B.root i (line t)) ≠ 0 := by
    intro t ht
    refine prod_ne_zero_iff.mpr fun i hi ↦ sub_ne_zero.mpr ?_
    exact B.root_ne _ (hlineN t ht) l i (ne_of_mem_erase hi).symm
  set W : ℕ → ℝ → ℂ := fun r t ↦
    if h : IsUnit (∏ i ∈ univ.erase l, (B.root l (line t) - B.root i (line t))) then
      extractionWeight (fun i ↦ B.root i (line t)) l h r else 0 with hW
  have hW_smooth : ∀ r, ∀ t ∈ Ioo (-δ) δ, ContDiffAt ℝ 2 (W r) t := by
    intro r t ht
    have hformula := contDiffAt_weightFormula (fun i t ↦ B.root i (line t)) l
      (fun i ↦ hroot_line i t ht) (hprod_ne t ht) r
    refine hformula.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht] with t' ht'
    simp only [hW]
    rw [dite_eq_left (isUnit_iff_ne_zero.mpr (hprod_ne t' ht')), extractionWeight_eq]
  have hχW_smooth : ∀ r, ContDiff ℝ 2 (fun t ↦ χc t * W r t) := fun r ↦
    contDiff_mul_of_tsupport hχc_smooth hχc_tsupport' (hW_smooth r)
  -- the row bound
  obtain ⟨Mb, hMb⟩ := sum_norm_fiber_le D
  have hpq : -π < π := neg_lt_self Real.pi_pos
  -- apply the one-variable rigidity theorem on the segment
  have hzero := amplitude_eq_zero_of_curved_root_line (a := -δ') (b := δ') (m := m) (M := Mb)
    hpq (by linarith) (by linarith) (by linarith) hm χc
    (fun i u ↦ B.amp i (line u)) (fun i u ↦ B.root i (line u)) l
    (φ := fun s ↦ φ (x + s • intDir v)) (φ' := fun s ↦ fderiv ℝ φ (x + s • intDir v) (intDir v))
    (φ'' := fun s ↦ secondDeriv φ (x + s • intDir v) (intDir v)) (ψ' := deriv g)
    (fun n ↦ sliceFiber (n : ℤ)) (fun _ u ↦ (D.M u : ℂ)) 0 x v
    (fun n _ ↦ hMb n)
    (fun t ht ↦ hrepφ _ (hlineU t (hsub ht)))
    (fun t ht ↦ isUnit_iff_ne_zero.mpr (hprod_ne t (hsub ht)))
    (fun n _ u hu ↦ by
      rw [show π - -π = 2 * π by ring, line_eq, mvTrigPoly_sliceFiber,
        B.rep _ (hlineN u (hsub hu)) n]
      rfl)
    hχc_out
    (fun t _ ↦ ((hg_smooth.differentiable (by norm_num)) t).hasDerivAt)
    (hg_smooth.continuous_deriv (by norm_num)).continuousOn
    (fun r ↦ (hχW_smooth r).continuous)
    (fun r ↦ summable_fourierCoeffOn_of_contDiff hpq (hχW_smooth r)
      (by filter_upwards [hvanish (-π) (Or.inl rfl)] with y hy; simp [hy])
      (by filter_upwards [hvanish π (Or.inr rfl)] with y hy; simp [hy]))
    (fun t ht ↦ hd1 t (hsubI ht)) (fun t ht ↦ hd2 t (hsubI ht)) (hcont2.mono hsubI)
    (fun t ht ↦ hcurv t (hsubI ht))
  -- but the localized amplitude is nonzero at the centre
  have hline0 : line 0 = x := by simp [hline]
  have hpos : 0 < ∫ t in -π..π, ‖g t‖ ^ 2 := by
    refine integral_pos_of_continuous_of_pos (t₀ := 0) (hg_smooth.continuous.norm.pow 2)
      (fun t ↦ sq_nonneg _) ⟨by linarith, by linarith⟩ ?_
    have hx : B.amp l x ≠ 0 := B.amp_ne l x (hUN x hxU)
    show 0 < ‖g 0‖ ^ 2
    have hg0 : g 0 = B.amp l x := by simp only [hg, hχc0, hline0, one_mul]
    rw [hg0]
    exact pow_pos (norm_pos_iff.mpr hx) 2
  have : ∫ t in -π..π, ‖g t‖ ^ 2 = 0 := hzero
  linarith

end ActiveBranches

end WeakTiling

end

end PhaseH

/-! ## Construction of the active branches -/

section ActiveConstruction

section

open Complex Finset Polynomial Filter Topology Metric Set
open scoped Real

namespace WeakTiling

variable {ι : Type} [Fintype ι]

section Spectrum

variable (D : LatticeTilingData ι)

/-- The slice values at real angles. -/
noncomputable def sliceVal (θ : ι → ℝ) (m : ℕ) : ℂ := latticeSlice D (torusPt θ) m

theorem sliceVal_eq_sliceC (θ : ι → ℝ) (m : ℕ) :
    sliceVal D θ m = sliceC D (ofRealVec θ) m := (sliceC_ofRealVec D θ m).symm

theorem contDiff_sliceVal (m : ℕ) {n : WithTop ℕ∞} : ContDiff ℝ n (fun θ ↦ sliceVal D θ m) := by
  have : (fun θ ↦ sliceVal D θ m) = (fun w ↦ sliceC D w m) ∘ ofRealVec := by
    funext θ
    exact sliceVal_eq_sliceC D θ m
  rw [this]
  exact ((contDiff_sliceC D m).restrict_scalars ℝ).comp contDiff_ofRealVec

/-- Generic angles: the characteristic polynomial has nonzero constant coefficient. -/
def genericSet : Set (ι → ℝ) := {θ | (sliceXi D (torusPt θ)).coeff 0 ≠ 0}

/-- The unimodular characteristic roots. -/
noncomputable def unitSpec (θ : ι → ℝ) : Finset ℂ :=
  (sliceCharPoly D (torusPt θ)).roots.toFinset.filter fun μ ↦ ‖μ‖ = 1

theorem continuous_latticeMono_torusPt (u : ι → ℤ) :
    Continuous fun θ : ι → ℝ ↦ latticeMono (torusPt θ) u := by
  simp_rw [← mvChar_two_pi]
  unfold mvChar
  fun_prop

theorem isOpen_genericSet : IsOpen (genericSet D) := by
  have hc : Continuous fun θ : ι → ℝ ↦ (sliceXi D (torusPt θ)).coeff 0 := by
    simp only [sliceXi_coeff]
    refine continuous_finsetSum _ fun j _ ↦ Continuous.sub ?_ ?_
    · split_ifs
      · exact continuous_latticeMono_torusPt _
      · exact continuous_const
    · split_ifs
      · exact continuous_latticeMono_torusPt _
      · exact continuous_const
  exact isOpen_ne_fun hc continuous_const

theorem zero_mem_genericSet [Nonempty ι] : (0 : ι → ℝ) ∈ genericSet D := by
  classical
  show (sliceXi D (torusPt 0)).coeff 0 ≠ 0
  have hone : ∀ u : ι → ℤ, latticeMono (torusPt 0) u = 1 := by
    intro u
    simp [latticeMono, torusPt]
  rw [sliceXi_coeff]
  simp only [hone]
  have hp : ∀ j, ¬ (0 = sliceTop D - ∑ k, D.p j k) := by
    intro j h
    have h1 := (p_deg_lt_q_deg D j).trans_le (q_deg_le_sliceTop D j)
    omega
  simp only [hp, ite_false, zero_sub, sum_neg_distrib, neg_ne_zero]
  rw [sum_boole]
  obtain ⟨j0, -, hj0⟩ := exists_mem_eq_sup (univ : Finset (Fin D.n))
    ⟨⟨0, D.n_pos⟩, mem_univ _⟩ fun j ↦ ∑ k, D.q j k
  refine Nat.cast_ne_zero.mpr (card_ne_zero.mpr ⟨j0, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩)
  rw [sliceTop, hj0, Nat.sub_self]

variable [Nonempty ι]

/-- The amplitudes of the unimodular expansion at a generic angle. -/
noncomputable def actAmp (θ : ι → ℝ) : ℂ → ℂ := by
  classical
  exact if h : θ ∈ genericSet D then
    Classical.choose (latticeSlice_unimodular D (norm_torusPt θ) h) else fun _ ↦ 0

theorem actAmp_spec {θ : ι → ℝ} (h : θ ∈ genericSet D) (m : ℤ) :
    latticeSlice D (torusPt θ) m = ∑ μ ∈ unitSpec D θ, actAmp D θ μ * μ ^ m := by
  classical
  have := Classical.choose_spec (latticeSlice_unimodular D (norm_torusPt θ) h) m
  rw [actAmp, dite_eq_left h]
  convert this using 2
  ext μ
  simp [unitSpec]

/-- The active roots: unimodular roots with nonzero amplitude. -/
noncomputable def actSet (θ : ι → ℝ) : Finset ℂ := by
  classical
  exact (unitSpec D θ).filter fun μ ↦ actAmp D θ μ ≠ 0

theorem mem_actSet {θ : ι → ℝ} {μ : ℂ} (hμ : μ ∈ actSet D θ) :
    μ ∈ (sliceCharPoly D (torusPt θ)).roots.toFinset ∧ ‖μ‖ = 1 ∧ actAmp D θ μ ≠ 0 := by
  classical
  simp only [actSet, unitSpec, mem_filter] at hμ
  exact ⟨hμ.1.1, hμ.1.2, hμ.2⟩

theorem sliceVal_eq_expSeq {θ : ι → ℝ} (h : θ ∈ genericSet D) (m : ℕ) :
    sliceVal D θ m = expSeq (actSet D θ) (actAmp D θ) m := by
  classical
  rw [sliceVal, actAmp_spec D h, expSeq, actSet, sum_filter_of_ne fun μ _ hμ ↦
    left_ne_zero_of_mul hμ]
  exact sum_congr rfl fun μ _ ↦ by rw [zpow_natCast]

theorem card_actSet_le (θ : ι → ℝ) : (actSet D θ).card ≤ sliceTop D := by
  classical
  have hsub : actSet D θ ⊆ (sliceCharPoly D (torusPt θ)).roots.toFinset := fun μ hμ ↦
    (mem_actSet D hμ).1
  refine (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans ?_)
  exact (card_roots' _).trans (sliceCharPoly_natDegree D _).le

theorem eval_sliceXi_of_mem_actSet {θ : ι → ℝ} {μ : ℂ} (hμ : μ ∈ actSet D θ) :
    (sliceXi D (torusPt θ)).eval μ = 0 := by
  have hroot := (mem_actSet D hμ).1
  rw [Multiset.mem_toFinset, mem_roots (sliceCharPoly_monic D _).ne_zero, IsRoot,
    sliceCharPoly, eval_mul, eval_C] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left (inv_ne_zero (sliceXi_coeff_top D _))

/-- The largest number of active roots at a generic angle. -/
noncomputable def activeRank : ℕ := sSup {k | ∃ θ ∈ genericSet D, (actSet D θ).card = k}

theorem activeRank_bdd : BddAbove {k | ∃ θ ∈ genericSet D, (actSet D θ).card = k} :=
  ⟨sliceTop D, by rintro k ⟨θ, -, rfl⟩; exact card_actSet_le D θ⟩

theorem card_actSet_le_activeRank {θ : ι → ℝ} (h : θ ∈ genericSet D) :
    (actSet D θ).card ≤ activeRank D :=
  le_csSup (activeRank_bdd D) ⟨θ, h, rfl⟩

theorem exists_activeRank : ∃ θ ∈ genericSet D, (actSet D θ).card = activeRank D :=
  Nat.sSup_mem (s := {k | ∃ θ ∈ genericSet D, (actSet D θ).card = k})
    ⟨(actSet D 0).card, 0, zero_mem_genericSet D, rfl⟩ (activeRank_bdd D)

end Spectrum

section Good

variable (D : LatticeTilingData ι) [Nonempty ι]

/-- Generic angles with nonzero Hankel determinant of size `activeRank D`. -/
def goodSet : Set (ι → ℝ) :=
  {θ | θ ∈ genericSet D ∧ (hankel (sliceVal D θ) (activeRank D)).det ≠ 0}

theorem isOpen_goodSet : IsOpen (goodSet D) := by
  have hc : Continuous fun θ ↦ (hankel (sliceVal D θ) (activeRank D)).det := by
    refine Continuous.matrix_det ?_
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    exact (contDiff_sliceVal D _ (n := 0)).continuous
  exact (isOpen_genericSet D).inter (isOpen_ne_fun hc continuous_const)

theorem card_actSet_of_good {θ : ι → ℝ} (hθ : θ ∈ goodSet D) :
    (actSet D θ).card = activeRank D := by
  refine le_antisymm (card_actSet_le_activeRank D hθ.1) ?_
  by_contra hlt
  apply hθ.2
  have : sliceVal D θ = expSeq (actSet D θ) (actAmp D θ) := funext (sliceVal_eq_expSeq D hθ.1)
  rw [this]
  exact hankel_det_eq_zero _ _ (not_le.mp hlt)

theorem pronyPoly_good {θ : ι → ℝ} (hθ : θ ∈ goodSet D) :
    pronyPoly (sliceVal D θ) (activeRank D) =
      pronyPoly (expSeq (actSet D θ) (actAmp D θ)) (actSet D θ).card := by
  rw [card_actSet_of_good D hθ, funext (sliceVal_eq_expSeq D hθ.1)]

theorem pronyPoly_good_spec {θ : ι → ℝ} (hθ : θ ∈ goodSet D) :
    pronyPoly (sliceVal D θ) (activeRank D) ≠ 0 ∧
      (pronyPoly (sliceVal D θ) (activeRank D)).roots.toFinset = actSet D θ ∧
      ∀ μ ∈ actSet D θ, (derivative (pronyPoly (sliceVal D θ) (activeRank D))).eval μ ≠ 0 := by
  have hc : ∀ μ ∈ actSet D θ, actAmp D θ μ ≠ 0 := fun μ hμ ↦ (mem_actSet D hμ).2.2
  obtain ⟨h1, -, h3, h4⟩ := pronyPoly_spec (actSet D θ) (actAmp D θ) hc
  rw [pronyPoly_good D hθ]
  exact ⟨h1, h3, h4⟩

theorem pronyF_ofRealVec (θ : ι → ℝ) (x : ℂ) :
    pronyF D (activeRank D) (ofRealVec θ, x) = (pronyPoly (sliceVal D θ) (activeRank D)).eval x := by
  rw [pronyF]
  congr 2
  funext m
  exact (sliceVal_eq_sliceC D θ m).symm

end Good

/-- **Active branches exist.**  On some ball of angles, the active roots move smoothly and
distinctly, with smooth nonvanishing amplitudes. They are roots of the characteristic
polynomial. -/
theorem exists_activeBranches (D : LatticeTilingData ι) [Nonempty ι] :
    ∃ (θ₀ : ι → ℝ) (ε : ℝ), 0 < ε ∧ (∀ θ ∈ ball θ₀ ε, θ ∈ genericSet D) ∧
      ∃ B : ActiveBranches D (ball θ₀ ε),
        ∀ θ ∈ ball θ₀ ε, ∀ l, (sliceXi D (torusPt θ)).eval (B.root l θ) = 0 := by
  classical
  set r := activeRank D with hr
  obtain ⟨θs, hθsG, hθscard⟩ := exists_activeRank D
  have hθsgood : θs ∈ goodSet D := by
    refine ⟨hθsG, ?_⟩
    have : sliceVal D θs = expSeq (actSet D θs) (actAmp D θs) :=
      funext (sliceVal_eq_expSeq D hθsG)
    rw [this, ← hθscard]
    exact hankel_det_ne_zero _ _ fun μ hμ ↦ (mem_actSet D hμ).2.2
  obtain ⟨hQ0, hQroots, hQder⟩ := pronyPoly_good_spec D hθsgood
  -- index the active roots at `θs`
  set e : Fin r ≃ actSet D θs :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hθscard])).symm with he
  -- implicit branches through each active root
  have hbranch : ∀ l : Fin r, ∃ ψ : (ι → ℂ) → ℂ, ψ (ofRealVec θs) = (e l : ℂ) ∧
      ContDiffAt ℂ 2 ψ (ofRealVec θs) ∧
      ∀ᶠ w in 𝓝 (ofRealVec θs), pronyF D r (w, ψ w) = pronyF D r (ofRealVec θs, (e l : ℂ)) := by
    intro l
    have hμ : ((e l : ℂ)) ∈ actSet D θs := (e l).2
    refine exists_root_branch (u := (ofRealVec θs, (e l : ℂ)))
      (contDiff_pronyF D r).contDiffAt (hQder _ hμ) ?_
    have hfun : (fun x ↦ pronyF D r ((ofRealVec θs, (e l : ℂ)).1, x)) =
        fun x ↦ (pronyPoly (sliceVal D θs) r).eval x := funext fun x ↦ pronyF_ofRealVec D θs x
    rw [hfun]
    exact Polynomial.hasDerivAt _ _
  choose ψ hψ0 hψs hψev using hbranch
  have hroot0 : ∀ l, pronyF D r (ofRealVec θs, (e l : ℂ)) = 0 := by
    intro l
    rw [pronyF_ofRealVec]
    have hμ : ((e l : ℂ)) ∈ (pronyPoly (sliceVal D θs) r).roots.toFinset := by
      rw [hQroots]
      exact (e l).2
    exact (mem_roots hQ0).mp (Multiset.mem_toFinset.mp hμ)
  set root : Fin r → (ι → ℝ) → ℂ := fun l θ ↦ ψ l (ofRealVec θ) with hroot
  have hroot_smooth0 : ∀ l, ContDiffAt ℝ 2 (root l) θs := fun l ↦
    ((hψs l).restrict_scalars ℝ).comp θs contDiff_ofRealVec.contDiffAt
  have hroot_val : ∀ l, root l θs = (e l : ℂ) := fun l ↦ hψ0 l
  -- eventual properties near `θs`
  have hev_smooth : ∀ᶠ θ in 𝓝 θs, ∀ l, ContDiffAt ℝ 2 (root l) θ :=
    eventually_all.mpr fun l ↦ (hroot_smooth0 l).eventually (by simp)
  have hev_root : ∀ᶠ θ in 𝓝 θs, ∀ l, pronyF D r (ofRealVec θ, root l θ) = 0 := by
    refine eventually_all.mpr fun l ↦ ?_
    have := (contDiff_ofRealVec (n := 0)).continuous.tendsto θs |>.eventually (hψev l)
    filter_upwards [this] with θ hθ
    rw [hθ, hroot0 l]
  have hev_ne : ∀ᶠ θ in 𝓝 θs, ∀ l l', l ≠ l' → root l θ ≠ root l' θ := by
    refine eventually_all.mpr fun l ↦ eventually_all.mpr fun l' ↦ ?_
    by_cases hll : l = l'
    · exact Eventually.of_forall fun _ h ↦ absurd hll h
    · have hne : root l θs - root l' θs ≠ 0 := by
        rw [hroot_val, hroot_val, sub_ne_zero]
        intro h
        exact hll (e.injective (Subtype.ext h))
      have hcont := ((hroot_smooth0 l).continuousAt.sub (hroot_smooth0 l').continuousAt)
      filter_upwards [hcont.eventually_ne hne] with θ hθ _
      exact sub_ne_zero.mp hθ
  have hev_good : ∀ᶠ θ in 𝓝 θs, θ ∈ goodSet D := (isOpen_goodSet D).mem_nhds hθsgood
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hev_smooth.and (hev_root.and (hev_ne.and hev_good)))
  -- on the ball the branches are exactly the active roots
  have hgood : ∀ θ ∈ ball θs ε, θ ∈ goodSet D := fun θ hθ ↦ (hball θ hθ).2.2.2
  have hsmooth : ∀ θ ∈ ball θs ε, ∀ l, ContDiffAt ℝ 2 (root l) θ := fun θ hθ ↦ (hball θ hθ).1
  have hne : ∀ θ ∈ ball θs ε, ∀ l l', l ≠ l' → root l θ ≠ root l' θ :=
    fun θ hθ ↦ (hball θ hθ).2.2.1
  have hinj : ∀ θ ∈ ball θs ε, Function.Injective fun l ↦ root l θ := by
    intro θ hθ l l' h
    by_contra hll
    exact hne θ hθ l l' hll h
  have himage : ∀ θ ∈ ball θs ε, Finset.univ.image (fun l ↦ root l θ) = actSet D θ := by
    intro θ hθ
    obtain ⟨hQ0θ, hQrootsθ, -⟩ := pronyPoly_good_spec D (hgood θ hθ)
    have hsub : Finset.univ.image (fun l ↦ root l θ) ⊆ actSet D θ := by
      intro μ hμ
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hμ
      rw [← hQrootsθ, Multiset.mem_toFinset, mem_roots hQ0θ, IsRoot, ← pronyF_ofRealVec]
      exact (hball θ hθ).2.1 l
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [card_actSet_of_good D (hgood θ hθ), Finset.card_image_of_injective _ (hinj θ hθ),
      Finset.card_univ, Fintype.card_fin]
  have hmem : ∀ θ ∈ ball θs ε, ∀ l, root l θ ∈ actSet D θ := fun θ hθ l ↦ by
    rw [← himage θ hθ]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ l)
  -- amplitudes by Vandermonde extraction
  set amp : Fin r → (ι → ℝ) → ℂ := fun l θ ↦ ∑ k ∈ range r,
    ((∏ i ∈ univ.erase l, (root l θ - root i θ))⁻¹ *
      (∏ i ∈ univ.erase l, (X - C (root i θ))).coeff k) * sliceVal D θ k with hamp
  have hrep : ∀ θ ∈ ball θs ε, ∀ n : ℕ,
      sliceVal D θ n = ∑ l, actAmp D θ (root l θ) * root l θ ^ n := by
    intro θ hθ n
    rw [sliceVal_eq_expSeq D (hgood θ hθ).1, expSeq, ← himage θ hθ,
      Finset.sum_image fun l _ l' _ h ↦ hinj θ hθ h]
  have hamp_eq : ∀ θ ∈ ball θs ε, ∀ l, amp l θ = actAmp D θ (root l θ) := by
    intro θ hθ l
    have hD : IsUnit (∏ i ∈ univ.erase l, (root l θ - root i θ)) := by
      refine isUnit_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i hi ↦ sub_ne_zero.mpr ?_)
      exact hne θ hθ l i (ne_of_mem_erase hi).symm
    have hext := sum_extractionWeight_mul_expSum (fun i ↦ actAmp D θ (root i θ))
      (fun i ↦ root i θ) l hD 0
    rw [pow_zero, mul_one, Fintype.card_fin] at hext
    rw [← hext, hamp]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [extractionWeight_eq, zero_add, hrep θ hθ k]
    rfl
  refine ⟨θs, ε, hε, fun θ hθ ↦ (hgood θ hθ).1,
    ⟨r, root, amp, fun l θ hθ ↦ hsmooth θ hθ l, ?_, fun θ hθ ↦ hne θ hθ,
    fun l θ hθ ↦ (mem_actSet D (hmem θ hθ l)).2.1, ?_, ?_⟩, ?_⟩
  · -- smooth amplitudes
    intro l θ hθ
    refine ContDiffAt.sum fun k _ ↦ ?_
    refine ContDiffAt.mul ?_ (contDiff_sliceVal D k).contDiffAt
    refine contDiffAt_weightFormula root l (hsmooth θ hθ) ?_ k
    exact prod_ne_zero_iff.mpr fun i hi ↦ sub_ne_zero.mpr
      (hne θ hθ l i (ne_of_mem_erase hi).symm)
  · intro l θ hθ
    rw [hamp_eq θ hθ l]
    exact (mem_actSet D (hmem θ hθ l)).2.2
  · intro θ hθ n
    rw [← sliceVal, hrep θ hθ n]
    exact sum_congr rfl fun l _ ↦ by rw [hamp_eq θ hθ l]
  · intro θ hθ l
    exact eval_sliceXi_of_mem_actSet D (hmem θ hθ l)

end WeakTiling

end

end ActiveConstruction

/-! ## Rational slopes of algebraic linear phases -/

section RationalSlope

section

open Complex Finset Polynomial

namespace WeakTiling

/-- **Linear independence of exponentials on an interval.** -/
theorem coeff_eq_zero_of_expSum_vanish_interval {α : Type*} (S : Finset α) (ω : α → ℝ)
    (hinj : Set.InjOn ω S) (a : α → ℂ) {t₀ β : ℝ} (hβ : t₀ < β)
    (h : ∀ t ∈ Set.Ico t₀ β, ∑ i ∈ S, a i * exp ((ω i * t : ℝ) * I) = 0) :
    ∀ i ∈ S, a i = 0 := by
  classical
  -- a small sampling step
  set D : ℝ := 2 * ∑ i ∈ S, |ω i| with hD
  have hD0 : 0 ≤ D := by positivity
  set h0 : ℝ := min ((β - t₀) / (S.card + 1)) (1 / (D + 1)) with hh0
  have hpos : 0 < h0 := lt_min (div_pos (by linarith) (by positivity)) (by positivity)
  have hdiff : ∀ i ∈ S, ∀ j ∈ S, |ω i - ω j| ≤ D := by
    intro i hi j hj
    calc |ω i - ω j| ≤ |ω i| + |ω j| := abs_sub _ _
      _ ≤ ∑ k ∈ S, |ω k| + ∑ k ∈ S, |ω k| := add_le_add
          (single_le_sum (fun k _ ↦ abs_nonneg (ω k)) hi)
          (single_le_sum (fun k _ ↦ abs_nonneg (ω k)) hj)
      _ = D := by rw [hD]; ring
  -- sampled exponential sum over the subtype
  set U : S → ℂ := fun i ↦ a i * exp ((ω i * t₀ : ℝ) * I) with hU
  set z : S → ℂ := fun i ↦ exp ((ω i * h0 : ℝ) * I) with hz
  have hsample : ∀ n : ℕ, n < S.card + 1 → expSum U z n = 0 := by
    intro n hn
    have hmem : t₀ + n * h0 ∈ Set.Ico t₀ β := by
      have hn' : (n : ℝ) ≤ S.card := by exact_mod_cast Nat.lt_succ_iff.mp hn
      have h1 : h0 ≤ (β - t₀) / (S.card + 1) := min_le_left _ _
      have h2 : (n : ℝ) * h0 < β - t₀ := by
        calc (n : ℝ) * h0 ≤ S.card * h0 := mul_le_mul_of_nonneg_right hn' hpos.le
          _ < (S.card + 1) * h0 := by nlinarith
          _ ≤ (S.card + 1) * ((β - t₀) / (S.card + 1)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = β - t₀ := by field_simp
      exact ⟨by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)], by linarith⟩
    have := h _ hmem
    rw [expSum, ← this, ← sum_coe_sort S]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [hU, hz]
    rw [mul_assoc, ← exp_nat_mul, ← exp_add]
    congr 2
    push_cast
    ring
  -- distinct sampled roots
  have hzinj : ∀ i j : S, i ≠ j → z j - z i ≠ 0 := by
    intro i j hij heq
    apply hij
    rw [sub_eq_zero] at heq
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
    have hre : ω j * h0 = ω i * h0 + n * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      simpa using this
    have hsmall : |ω j - ω i| * h0 < 1 := by
      have h2 : h0 ≤ 1 / (D + 1) := min_le_right _ _
      calc |ω j - ω i| * h0 ≤ D * (1 / (D + 1)) :=
            mul_le_mul (hdiff j j.2 i i.2) h2 hpos.le hD0
        _ < 1 := by rw [mul_one_div, div_lt_one (by linarith)]; linarith
    have hn0 : n = 0 := by
      by_contra hn0
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hn0
      have h3 : |ω j - ω i| * h0 = |(n : ℝ)| * (2 * Real.pi) := by
        rw [← abs_of_pos hpos, ← abs_mul, sub_mul, hre]
        rw [show ω i * h0 + n * (2 * Real.pi) - ω i * h0 = n * (2 * Real.pi) by ring,
          abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_gt_three]
    rw [hn0, Int.cast_zero, zero_mul, add_zero] at hre
    exact Subtype.ext (hinj j.2 i.2 (mul_right_cancel₀ hpos.ne' hre)).symm
  -- extraction
  have hDunit : ∀ j : S, IsUnit (∏ i ∈ univ.erase j, (z j - z i)) := fun j ↦
    isUnit_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i hi ↦ hzinj i j (ne_of_mem_erase hi))
  intro i hi
  have hext := sum_extractionWeight_mul_expSum U z ⟨i, hi⟩ (hDunit ⟨i, hi⟩) 0
  rw [Fintype.card_coe] at hext
  have h0sum : ∑ r ∈ range S.card, extractionWeight z ⟨i, hi⟩ (hDunit ⟨i, hi⟩) r *
      expSum U z (0 + r) = 0 :=
    sum_eq_zero fun r hr ↦ by
      rw [zero_add, hsample r (Nat.lt_succ_of_lt (mem_range.mp hr)), mul_zero]
  rw [h0sum, pow_zero, mul_one] at hext
  have : a i * exp ((ω i * t₀ : ℝ) * I) = 0 := hext.symm
  exact (mul_eq_zero.mp this).resolve_right (exp_ne_zero _)

end WeakTiling

end

end RationalSlope

/-! ## Collision cancellation in any number of variables -/

section MultiVarCancellation

section

open Polynomial Filter Topology

namespace WeakTiling

/-- Evaluate `P ∈ (MvPolynomial σ ℂ)[X]` at `(x, y)`. -/
noncomputable def evalMv {σ : Type*} (P : Polynomial (MvPolynomial σ ℂ)) (x : ℂ) (y : σ → ℂ) :
    ℂ :=
  (P.map (MvPolynomial.eval y)).eval x

end WeakTiling

end

end MultiVarCancellation

/-! ## Rational slopes in several variables -/

section MultiRationalSlope

section

open Complex Finset Polynomial

namespace WeakTiling

variable {σ : Type*} [Fintype σ]

/-- **A separating direction** for finitely many distinct vectors. -/
theorem exists_separating_direction {α : Type*} (S : Finset α) (ξ : α → σ → ℝ)
    (hinj : Set.InjOn ξ S) :
    ∃ e : σ → ℝ, Set.InjOn (fun a ↦ ∑ i, ξ a i * e i) S := by
  classical
  set k : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  set poly : (σ → ℝ) → ℝ[X] := fun v ↦ ∑ i, C (v i) * X ^ (k i : ℕ) with hpoly
  have hpoly_ne : ∀ v : σ → ℝ, v ≠ 0 → poly v ≠ 0 := by
    intro v hv hzero
    apply hv
    funext i
    have := congrArg (fun p ↦ p.coeff (k i : ℕ)) hzero
    simp only [hpoly, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro j _ hj
      rw [ite_eq_right]
      intro h
      exact hj (k.injective (Fin.ext h.symm))
    · simp
  have heval : ∀ (v : σ → ℝ) (r : ℝ), (poly v).eval r = ∑ i, v i * r ^ (k i : ℕ) := by
    intro v r
    simp [hpoly, eval_finsetSum]
  set bad : Finset ℝ := (S ×ˢ S).biUnion fun ab ↦
    if ab.1 = ab.2 then ∅ else (poly (ξ ab.1 - ξ ab.2)).roots.toFinset with hbad
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset bad
  refine ⟨fun i ↦ r ^ (k i : ℕ), ?_⟩
  intro a ha b hb hab
  by_contra hne
  have hv : ξ a - ξ b ≠ 0 := sub_ne_zero.mpr fun h ↦ hne (hinj ha hb h)
  apply hr
  rw [hbad, mem_biUnion]
  refine ⟨(a, b), mem_product.mpr ⟨ha, hb⟩, ?_⟩
  rw [ite_eq_right hne, Multiset.mem_toFinset, mem_roots (hpoly_ne _ hv), IsRoot, heval]
  simp only at hab
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  linarith

/-- **Independence of multivariable exponentials on a box.** -/
theorem coeff_eq_zero_of_mvExpSum_vanish_box {α : Type*} (S : Finset α) (ξ : α → σ → ℝ)
    (hinj : Set.InjOn ξ S) (a : α → ℂ) (t₀ : σ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t : σ → ℝ, (∀ i, |t i - t₀ i| < δ) →
      ∑ x ∈ S, a x * exp (((∑ i, ξ x i * t i : ℝ) : ℂ) * I) = 0) :
    ∀ x ∈ S, a x = 0 := by
  obtain ⟨e, he⟩ := exists_separating_direction S ξ hinj
  set E : ℝ := ∑ i, |e i| + 1 with hE
  have hEpos : 0 < E := by positivity
  set ω : α → ℝ := fun x ↦ ∑ i, ξ x i * e i with hω
  set b : α → ℂ := fun x ↦ a x * exp (((∑ i, ξ x i * t₀ i : ℝ) : ℂ) * I) with hb
  have hline : ∀ u ∈ Set.Ico (0 : ℝ) (δ / E),
      ∑ x ∈ S, b x * exp ((ω x * u : ℝ) * I) = 0 := by
    intro u hu
    have hbox : ∀ i, |(t₀ i + u * e i) - t₀ i| < δ := by
      intro i
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hu.1]
      have hei : |e i| < E := by
        have := single_le_sum (fun j _ ↦ abs_nonneg (e j)) (mem_univ i)
        rw [hE]; linarith
      have hu' : u < δ / E := hu.2
      calc u * |e i| ≤ u * E := mul_le_mul_of_nonneg_left hei.le hu.1
        _ < δ / E * E := mul_lt_mul_of_pos_right hu' hEpos
        _ = δ := by field_simp
    have := h (fun i ↦ t₀ i + u * e i) hbox
    rw [← this]
    refine sum_congr rfl fun x _ ↦ ?_
    simp only [hb, hω]
    rw [mul_assoc, ← exp_add]
    congr 2
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hb0 := coeff_eq_zero_of_expSum_vanish_interval S ω he b (by positivity) hline
  intro x hx
  have := hb0 x hx
  simp only [hb] at this
  exact (mul_eq_zero.mp this).resolve_right (exp_ne_zero _)

/-- **Rational slopes of algebraic linear phases on the torus.**

Let `P ∈ (MvPolynomial σ ℂ)[w]` be nonzero and `c ≠ 0`.  If `P(e^{it}, c e^{i s·t}) = 0` for
all `t` in a box around `t₀`, then every slope `sᵢ` is rational. -/
theorem slopes_rational_of_algebraic (P : Polynomial (MvPolynomial σ ℂ)) (hP : P ≠ 0) {c : ℂ}
    (hc : c ≠ 0) (s : σ → ℝ) (t₀ : σ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hvan : ∀ t : σ → ℝ, (∀ i, |t i - t₀ i| < δ) →
      evalMv P (c * exp (((∑ i, s i * t i : ℝ) : ℂ) * I)) (fun i ↦ exp ((t i : ℂ) * I)) = 0) :
    ∀ i, ∃ q : ℚ, s i = q := by
  classical
  by_contra hirr
  push Not at hirr
  obtain ⟨i₀, hi₀⟩ := hirr
  set N := P.natDegree + 1 with hN
  set S : Finset (Σ _ : ℕ, σ →₀ ℕ) := (range N).sigma fun k ↦ (P.coeff k).support with hS
  set ξ : (Σ _ : ℕ, σ →₀ ℕ) → σ → ℝ := fun km i ↦ (km.2 i : ℝ) + km.1 * s i with hξ
  have hinj : Set.InjOn ξ S := by
    rintro ⟨k, m⟩ _ ⟨k', m'⟩ _ hkm
    have hcoord : ∀ i, (m i : ℝ) + k * s i = m' i + k' * s i := fun i ↦ congrFun hkm i
    by_cases hk : k = k'
    · subst hk
      have hm : m = m' := by
        ext i
        have := hcoord i
        exact_mod_cast (by linarith : (m i : ℝ) = m' i)
      subst hm
      rfl
    · exfalso
      have hk' : ((k : ℝ) - k') ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hk)
      apply hi₀ ((m' i₀ - m i₀ : ℚ) / (k - k'))
      have := hcoord i₀
      push_cast
      field_simp
      linarith
  set a : (Σ _ : ℕ, σ →₀ ℕ) → ℂ := fun km ↦ (P.coeff km.1).coeff km.2 * c ^ km.1 with ha
  have hexpand : ∀ t : σ → ℝ,
      evalMv P (c * exp (((∑ i, s i * t i : ℝ) : ℂ) * I)) (fun i ↦ exp ((t i : ℂ) * I)) =
        ∑ km ∈ S, a km * exp (((∑ i, ξ km i * t i : ℝ) : ℂ) * I) := by
    intro t
    rw [evalMv, eval_eq_sum_range' (n := N) (lt_of_le_of_lt natDegree_map_le (Nat.lt_succ_self _)),
      hS, sum_sigma]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [coeff_map, MvPolynomial.eval_eq, sum_mul]
    refine sum_congr rfl fun m _ ↦ ?_
    simp only [ha, hξ]
    have hprod : ∏ i ∈ m.support, exp ((t i : ℂ) * I) ^ m i =
        exp (((∑ i, (m i : ℝ) * t i : ℝ) : ℂ) * I) := by
      rw [← Finset.sum_subset (subset_univ m.support) (fun i _ hi ↦ by
        rw [Finsupp.notMem_support_iff.mp hi]; simp)]
      push_cast
      rw [sum_mul, exp_sum]
      refine prod_congr rfl fun i _ ↦ ?_
      rw [← exp_nat_mul]
      congr 1
      ring
    rw [hprod, mul_pow, ← exp_nat_mul]
    calc (P.coeff k).coeff m * exp (((∑ i, (m i : ℝ) * t i : ℝ) : ℂ) * I) *
          (c ^ k * exp ((k : ℂ) * (((∑ i, s i * t i : ℝ) : ℂ) * I)))
        = (P.coeff k).coeff m * c ^ k * (exp (((∑ i, (m i : ℝ) * t i : ℝ) : ℂ) * I) *
            exp ((k : ℂ) * (((∑ i, s i * t i : ℝ) : ℂ) * I))) := by ring
      _ = (P.coeff k).coeff m * c ^ k *
            exp (((∑ i, ((m i : ℝ) + k * s i) * t i : ℝ) : ℂ) * I) := by
          rw [← exp_add]
          congr 2
          push_cast
          simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hzero := coeff_eq_zero_of_mvExpSum_vanish_box S ξ hinj a t₀ hδ
    (fun t ht ↦ by rw [← hexpand t]; exact hvan t ht)
  apply hP
  ext k m
  rw [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
  by_contra hne
  have hk : k < N := by
    have : P.coeff k ≠ 0 := fun h0 ↦ hne (by simp [h0])
    have := le_natDegree_of_ne_zero this
    omega
  have := hzero ⟨k, m⟩ (mem_sigma.mpr ⟨mem_range.mpr hk, MvPolynomial.mem_support_iff.mpr hne⟩)
  simp only [ha] at this
  exact hne ((mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hc))

end WeakTiling

end

end MultiRationalSlope

/-! ## Step H for lattice tiling data: the active roots are monomials -/

section LatticeH

section

open Complex Finset Polynomial Metric Set Filter Topology

namespace WeakTiling

variable {ι : Type} [Fintype ι]

/-- The characteristic polynomial `∑ⱼ (z^{pⱼ} X^{E-|pⱼ|} - z^{qⱼ} X^{E-|qⱼ|})` with polynomial
coefficients. -/
noncomputable def sliceXiMv (D : LatticeTilingData ι) : Polynomial (MvPolynomial ι ℂ) :=
  ∑ j, (C (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (D.p j)) 1) *
      X ^ (sliceTop D - ∑ k, D.p j k) -
    C (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (D.q j)) 1) *
      X ^ (sliceTop D - ∑ k, D.q j k))

theorem eval_monomial_eq_latticeMono (z : ι → ℂ) (v : ι → ℕ) :
    MvPolynomial.eval z (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm v) 1) =
      latticeMono z (fun k ↦ (v k : ℤ)) := by
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _)]
  simp [latticeMono]

theorem sliceXiMv_map (D : LatticeTilingData ι) (z : ι → ℂ) :
    (sliceXiMv D).map (MvPolynomial.eval z) = sliceXi D z := by
  simp only [sliceXiMv, sliceXi, Polynomial.map_sum, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_monomial_eq_latticeMono]

theorem evalMv_sliceXiMv (D : LatticeTilingData ι) (x : ℂ) (z : ι → ℂ) :
    evalMv (sliceXiMv D) x z = (sliceXi D z).eval x := by
  rw [evalMv, sliceXiMv_map]

theorem sliceXiMv_ne_zero (D : LatticeTilingData ι) [Nonempty ι] : sliceXiMv D ≠ 0 := by
  intro h
  have := sliceXi_coeff_top D (fun _ ↦ 1)
  rw [← sliceXiMv_map, h, Polynomial.map_zero, coeff_zero] at this
  exact this rfl

/-- Restriction of active branches to a smaller set. -/
def ActiveBranches.restrict {D : LatticeTilingData ι} {N N' : Set (ι → ℝ)}
    (B : ActiveBranches D N) (h : N' ⊆ N) : ActiveBranches D N' where
  r := B.r
  root := B.root
  amp := B.amp
  root_smooth := fun l θ hθ ↦ B.root_smooth l θ (h hθ)
  amp_smooth := fun l θ hθ ↦ B.amp_smooth l θ (h hθ)
  root_ne := fun θ hθ ↦ B.root_ne θ (h hθ)
  root_unit := fun l θ hθ ↦ B.root_unit l θ (h hθ)
  amp_ne := fun l θ hθ ↦ B.amp_ne l θ (h hθ)
  rep := fun θ hθ ↦ B.rep θ (h hθ)

/-- **Step H for lattice tiling data.**  On some ball of angles all active roots are monomials
with rational exponents. -/
theorem exists_monomial_branches (D : LatticeTilingData ι) [Nonempty ι] [DecidableEq ι] :
    ∃ (θ₀ : ι → ℝ) (ε : ℝ), 0 < ε ∧ (∀ θ ∈ ball θ₀ ε, θ ∈ genericSet D) ∧
      ∃ B : ActiveBranches D (ball θ₀ ε),
      (∀ θ ∈ ball θ₀ ε, ∀ l, (sliceXi D (torusPt θ)).eval (B.root l θ) = 0) ∧
      ∃ (c : Fin B.r → ℂ) (s : Fin B.r → ι → ℚ), (∀ l, c l ≠ 0) ∧
        ∀ θ ∈ ball θ₀ ε, ∀ l,
          B.root l θ = c l * exp (((∑ i, (s l i : ℝ) * θ i : ℝ) : ℂ) * I) := by
  obtain ⟨θ₀, ε, hε, hgen, B, halg⟩ := exists_activeBranches D
  -- affine phases near the centre
  have haff : ∀ l, ∃ (c : ℝ) (L : (ι → ℝ) →L[ℝ] ℝ),
      ∀ᶠ θ in 𝓝 θ₀, B.root l θ = exp (((c + L θ : ℝ) : ℂ) * I) := by
    intro l
    obtain ⟨ε₁, hε₁, -, c, L, hL⟩ := B.phase_affine isOpen_ball l (mem_ball_self hε)
    exact ⟨c, L, Filter.eventually_of_mem (ball_mem_nhds θ₀ hε₁) fun θ hθ ↦ hL θ hθ⟩
  choose c L hL using haff
  obtain ⟨ε', hε', hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((eventually_all.mpr hL).and (ball_mem_nhds θ₀ hε))
  have hsub : ball θ₀ ε' ⊆ ball θ₀ ε := fun θ hθ ↦ (hball θ hθ).2
  -- the slopes
  set s : Fin B.r → ι → ℝ := fun l i ↦ L l (fun j ↦ if i = j then 1 else 0) with hs
  have hLsum : ∀ l θ, L l θ = ∑ i, s l i * θ i := by
    intro l θ
    have := (L l : (ι → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ θ
    rw [ContinuousLinearMap.coe_coe] at this
    rw [this]
    exact sum_congr rfl fun i _ ↦ by rw [smul_eq_mul, mul_comm]
  have hform : ∀ θ ∈ ball θ₀ ε', ∀ l,
      B.root l θ = exp ((c l : ℂ) * I) * exp (((∑ i, s l i * θ i : ℝ) : ℂ) * I) := by
    intro θ hθ l
    rw [(hball θ hθ).1 l, ← exp_add, hLsum]
    congr 1
    push_cast
    ring
  have hrat : ∀ l i, ∃ q : ℚ, s l i = q := by
    intro l
    refine slopes_rational_of_algebraic (sliceXiMv D) (sliceXiMv_ne_zero D)
      (exp_ne_zero ((c l : ℂ) * I)) (s l) θ₀ hε' fun t ht ↦ ?_
    have htb : t ∈ ball θ₀ ε' := by
      rw [mem_ball, dist_pi_lt_iff hε']
      intro i
      rw [Real.dist_eq]
      exact ht i
    rw [evalMv_sliceXiMv, ← hform t htb l]
    exact halg t (hsub htb) l
  choose q hq using hrat
  refine ⟨θ₀, ε', hε', fun θ hθ ↦ hgen θ (hsub hθ), B.restrict hsub,
    fun θ hθ l ↦ halg θ (hsub hθ) l,
    fun l ↦ exp ((c l : ℂ) * I), q, fun l ↦ exp_ne_zero _, fun θ hθ l ↦ ?_⟩
  change B.root l θ = _
  rw [hform θ hθ l]
  congr 3
  push_cast
  refine sum_congr rfl fun i _ ↦ ?_
  rw [hq l i]
  norm_cast

end WeakTiling

end

end LatticeH

/-! ## The `ℓ²` binomial lemma -/

section BinomialL2

section

open Finset Filter Topology

namespace WeakTiling

variable {ι : Type*}

theorem norm_eq_of_binomial {a b : ℂ} (hab : ‖a‖ = ‖b‖) (hb : b ≠ 0) {x y : ℂ}
    (h : a * x = b * y) : ‖y‖ = ‖x‖ := by
  have := congrArg norm h
  rw [norm_mul, norm_mul, hab] at this
  exact (mul_left_cancel₀ (norm_ne_zero_iff.mpr hb) this).symm

/-- Along a ray that avoids `S`, the modulus of `f` is constant. -/
theorem norm_eq_along_forward {f : (ι → ℤ) → ℂ} {v : ι → ℤ} {a b : ℂ} (hab : ‖a‖ = ‖b‖)
    (hb : b ≠ 0) {S : Finset (ι → ℤ)} (hrel : ∀ n ∉ S, a * f (n - v) = b * f n) (n : ι → ℤ)
    (havoid : ∀ j : ℕ, 1 ≤ j → n + (j : ℤ) • v ∉ S) :
    ∀ j : ℕ, ‖f (n + (j : ℤ) • v)‖ = ‖f n‖ := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hnot := havoid (j + 1) (by omega)
    have := norm_eq_of_binomial hab hb (hrel _ hnot)
    have harg : n + ((j + 1 : ℕ) : ℤ) • v - v = n + (j : ℤ) • v := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [this, harg, ih]

theorem norm_eq_along_backward {f : (ι → ℤ) → ℂ} {v : ι → ℤ} {a b : ℂ} (hab : ‖a‖ = ‖b‖)
    (hb : b ≠ 0) {S : Finset (ι → ℤ)} (hrel : ∀ n ∉ S, a * f (n - v) = b * f n) (n : ι → ℤ)
    (havoid : ∀ j : ℕ, n - (j : ℤ) • v ∉ S) :
    ∀ j : ℕ, ‖f (n - (j : ℤ) • v)‖ = ‖f n‖ := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have := norm_eq_of_binomial hab hb (hrel _ (havoid j))
    have harg : n - (j : ℤ) • v - v = n - ((j + 1 : ℕ) : ℤ) • v := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [← harg, ← this, ih]

/-- A square-summable function cannot keep a nonzero modulus along a ray. -/
theorem eq_zero_of_norm_const_along {f : (ι → ℤ) → ℂ} (hf : Summable fun n ↦ ‖f n‖ ^ 2)
    {v : ι → ℤ} (hv : v ≠ 0) (n : ι → ℤ) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hconst : ∀ j : ℕ, ‖f (n + (s * j) • v)‖ = ‖f n‖) : f n = 0 := by
  have hinj : Function.Injective fun j : ℕ ↦ n + (s * j) • v := by
    intro i j h
    have h' : (s * i) • v = (s * j) • v := add_left_cancel h
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
    have := congrFun h' k
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    have := mul_right_cancel₀ hk this
    exact_mod_cast mul_left_cancel₀ hs0 this
  have hsum := hf.comp_injective hinj
  have hlim := hsum.tendsto_atTop_zero
  have hconst' : (fun j : ℕ ↦ ‖f (n + (s * j) • v)‖ ^ 2) = fun _ ↦ ‖f n‖ ^ 2 :=
    funext fun j ↦ by rw [hconst j]
  rw [Function.comp_def, hconst'] at hlim
  have h0 : ‖f n‖ ^ 2 = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  simpa using h0

/-- **The `ℓ²` binomial lemma.** -/
theorem finite_support_of_binomial {f : (ι → ℤ) → ℂ} (hf : Summable fun n ↦ ‖f n‖ ^ 2)
    {v : ι → ℤ} (hv : v ≠ 0) {a b : ℂ} (hab : ‖a‖ = ‖b‖) (hb : b ≠ 0) (S : Finset (ι → ℤ))
    (hrel : ∀ n ∉ S, a * f (n - v) = b * f n) : (Function.support f).Finite := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  -- a bound for the index distance between two points of `S` on a common line
  set R : ℕ := (S ×ˢ S).sup fun p ↦ (p.2 k - p.1 k).natAbs with hR
  set T : Finset (ι → ℤ) := (S ×ˢ range (R + 1)).image fun p ↦ p.1 - (p.2 : ℤ) • v with hT
  refine T.finite_toSet.subset fun n hn ↦ ?_
  have hfn : f n ≠ 0 := hn
  -- forward: some `n + j v` with `j ≥ 1` lies in `S`
  have hfwd : ∃ j : ℕ, 1 ≤ j ∧ n + (j : ℤ) • v ∈ S := by
    by_contra hno
    push Not at hno
    apply hfn
    refine eq_zero_of_norm_const_along hf hv n 1 (Or.inl rfl) fun j ↦ ?_
    simpa using norm_eq_along_forward hab hb hrel n hno j
  -- backward: some `n - j v` with `j ≥ 0` lies in `S`
  have hbwd : ∃ j : ℕ, n - (j : ℤ) • v ∈ S := by
    by_contra hno
    push Not at hno
    apply hfn
    refine eq_zero_of_norm_const_along hf hv n (-1) (Or.inr rfl) fun j ↦ ?_
    have := norm_eq_along_backward hab hb hrel n hno j
    rw [← this]
    congr 1
    rw [neg_one_mul, neg_smul, sub_eq_add_neg]
  obtain ⟨j, hj1, hjS⟩ := hfwd
  obtain ⟨j', hj'S⟩ := hbwd
  -- the index distance is bounded by `R`
  have hdist : (j : ℤ) + j' ≤ R := by
    have hdiff : (n + (j : ℤ) • v) k - (n - (j' : ℤ) • v) k = ((j : ℤ) + j') * v k := by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hle : ((n + (j : ℤ) • v) k - (n - (j' : ℤ) • v) k).natAbs ≤ R :=
      Finset.le_sup (f := fun p : (ι → ℤ) × (ι → ℤ) ↦ (p.2 k - p.1 k).natAbs)
        (b := (n - (j' : ℤ) • v, n + (j : ℤ) • v)) (mem_product.mpr ⟨hj'S, hjS⟩)
    rw [hdiff, Int.natAbs_mul] at hle
    have hvk : 1 ≤ (v k).natAbs := Int.natAbs_pos.mpr hk
    have : (((j : ℤ) + j').natAbs : ℤ) ≤ R := by
      have h1 : ((j : ℤ) + j').natAbs ≤ ((j : ℤ) + j').natAbs * (v k).natAbs :=
        Nat.le_mul_of_pos_right _ hvk
      exact_mod_cast h1.trans hle
    have hnn : (0 : ℤ) ≤ (j : ℤ) + j' := by positivity
    rw [Int.natAbs_of_nonneg hnn] at this
    exact this
  rw [Finset.coe_image]
  refine ⟨(n + (j : ℤ) • v, j), mem_product.mpr ⟨hjS, mem_range.mpr (by omega)⟩, ?_⟩
  simp

end WeakTiling

end

end BinomialL2

/-! ## Laurent polynomials as trigonometric polynomials on the torus -/

section TorusTrig

section

noncomputable section

open MeasureTheory UnitAddTorus Complex Finset Filter Metric
open scoped Real

/-- Same measure as in `Mathlib.Analysis.Fourier.AddCircleMulti`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace WeakTiling

variable {ι : Type} [Fintype ι]

/-- Laurent polynomials in the variables `ι`: the group algebra `ℂ[ℤ^ι]`. -/
abbrev LaurentPoly (ι : Type) := AddMonoidAlgebra ℂ (ι → ℤ)

/-- The characters at a torus point, as a monoid homomorphism. -/
noncomputable def charHom (t : UnitAddTorus ι) : Multiplicative (ι → ℤ) →* ℂ where
  toFun k := mFourier (Multiplicative.toAdd k) t
  map_one' := by simp [mFourier_zero]
  map_mul' k k' := by simp [mFourier_add]

/-- Evaluation of Laurent polynomials at a torus point. -/
noncomputable def trigEval (t : UnitAddTorus ι) : LaurentPoly ι →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (ι → ℤ) (charHom t)

theorem trigEval_apply (t : UnitAddTorus ι) (T : LaurentPoly ι) :
    trigEval t T = ∑ k ∈ T.coeff.support, T.coeff k * mFourier k t := by
  rw [trigEval, AddMonoidAlgebra.lift_apply]
  simp [Finsupp.sum, charHom, smul_eq_mul]

theorem trigEval_single (t : UnitAddTorus ι) (k : ι → ℤ) (c : ℂ) :
    trigEval t (AddMonoidAlgebra.single k c) = c * mFourier k t := by
  rw [trigEval, AddMonoidAlgebra.lift_single]
  simp [charHom, smul_eq_mul]

theorem continuous_trigEval (T : LaurentPoly ι) : Continuous fun t : UnitAddTorus ι ↦ trigEval t T := by
  simp only [trigEval_apply]
  exact continuous_finsetSum _ fun k _ ↦ continuous_const.mul (mFourier k).continuous

theorem mFourierCoeff_mFourier (k n : ι → ℤ) :
    mFourierCoeff (fun t ↦ mFourier k t) n = if n = k then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := ι))) n k
  rw [ContinuousMap.inner_toLp] at h
  rw [mFourierCoeff, ← h]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp [mFourier_neg, smul_eq_mul, mul_comm]

/-- **Multiplication by a Laurent polynomial convolves Fourier coefficients.** -/
theorem mFourierCoeff_trigEval_mul {F : UnitAddTorus ι → ℂ} (hF : Integrable F)
    (T : LaurentPoly ι) (n : ι → ℤ) :
    mFourierCoeff (fun t ↦ trigEval t T * F t) n =
      ∑ k ∈ T.coeff.support, T.coeff k * mFourierCoeff F (n - k) := by
  have hexp : ∀ t, mFourier (-n) t • (trigEval t T * F t) =
      ∑ k ∈ T.coeff.support, T.coeff k * (mFourier (-(n - k)) t • F t) := by
    intro t
    rw [trigEval_apply, Finset.sum_mul, Finset.smul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    have hmf : mFourier (-(n - k)) t = mFourier (-n) t * mFourier k t := by
      rw [← mFourier_add]
      congr 1
      abel
    rw [hmf]
    simp only [smul_eq_mul]
    ring
  simp only [mFourierCoeff]
  simp_rw [hexp]
  rw [integral_finsetSum]
  · exact sum_congr rfl fun k _ ↦ integral_const_mul _ _
  · intro k _
    refine Integrable.const_mul ?_ _
    have hb : ∀ t, ‖mFourier (-(n - k)) t‖ ≤ 1 := fun t ↦
      ((mFourier (-(n - k))).norm_coe_le_norm t).trans (le_of_eq mFourier_norm)
    exact (hF.bdd_mul (c := 1) (mFourier (-(n - k))).continuous.aestronglyMeasurable
      (Eventually.of_forall hb)).congr (Eventually.of_forall fun t ↦ by simp [smul_eq_mul])

theorem mFourierCoeff_one (m : ι → ℤ) :
    mFourierCoeff (fun _ : UnitAddTorus ι ↦ (1 : ℂ)) m = if m = 0 then 1 else 0 := by
  have := mFourierCoeff_mFourier (ι := ι) 0 m
  simp only [mFourier_zero, ContinuousMap.one_apply] at this
  exact this

/-- The Fourier coefficients of a Laurent polynomial are its coefficients. -/
theorem mFourierCoeff_trigEval (T : LaurentPoly ι) (n : ι → ℤ) :
    mFourierCoeff (fun t ↦ trigEval t T) n = T.coeff n := by
  classical
  have h := mFourierCoeff_trigEval_mul (F := fun _ ↦ (1 : ℂ)) (integrable_const _) T n
  simp only [mul_one] at h
  rw [h]
  simp only [mFourierCoeff_one, sub_eq_zero, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  split_ifs with hn
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hn).symm

/-- The Fourier coefficients of an `L²` function agree with those of its `Lp` class. -/
theorem mFourierCoeff_toLp {F : UnitAddTorus ι → ℂ} (hF : MemLp F 2) (n : ι → ℤ) :
    mFourierCoeff (hF.toLp F) n = mFourierCoeff F n := by
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with t ht
  rw [ht]

/-- **Parseval: square-summable coefficients.** -/
theorem summable_sq_mFourierCoeff {F : UnitAddTorus ι → ℂ} (hF : MemLp F 2) :
    Summable fun n ↦ ‖mFourierCoeff F n‖ ^ 2 := by
  have h := hasSum_sq_mFourierCoeff (hF.toLp F)
  simp only [mFourierCoeff_toLp hF] at h
  exact h.summable

/-- **Parseval: vanishing coefficients force vanishing almost everywhere.** -/
theorem ae_eq_zero_of_mFourierCoeff_eq_zero {F : UnitAddTorus ι → ℂ} (hF : MemLp F 2)
    (h : ∀ n, mFourierCoeff F n = 0) : F =ᵐ[volume] 0 := by
  have hs := hasSum_sq_mFourierCoeff (hF.toLp F)
  simp only [mFourierCoeff_toLp hF, h, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at hs
  have hzero : ∫ t, ‖(hF.toLp F) t‖ ^ 2 = 0 := (hasSum_zero.unique hs).symm
  have hint : Integrable fun t ↦ ‖(hF.toLp F) t‖ ^ 2 :=
    (Lp.memLp (hF.toLp F)).norm.integrable_sq
  have hae := (integral_eq_zero_iff_of_nonneg (fun t ↦ sq_nonneg _) hint).mp hzero
  filter_upwards [hae, hF.coeFn_toLp] with t h1 h2
  simp only [Pi.zero_apply, pow_eq_zero_iff (two_ne_zero), norm_eq_zero] at h1
  rw [Pi.zero_apply, ← h2, h1]

/-- The scaled torus point `θ / (2πQ)`. -/
noncomputable def toTorus (Q : ℕ) (θ : ι → ℝ) : UnitAddTorus ι :=
  fun i ↦ ((θ i / (2 * π * Q) : ℝ) : UnitAddCircle)

omit [Fintype ι] in
theorem toTorus_surjective {Q : ℕ} (hQ : 0 < Q) : Function.Surjective (toTorus (ι := ι) Q) := by
  intro t
  have hQ' : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  choose x hx using fun i ↦ QuotientAddGroup.mk_surjective (t i)
  refine ⟨fun i ↦ 2 * π * Q * x i, funext fun i ↦ ?_⟩
  simp only [toTorus]
  rw [← hx i]
  congr 1
  field_simp

theorem mFourier_toTorus {Q : ℕ} (hQ : 0 < Q) (k : ι → ℤ) (θ : ι → ℝ) :
    mFourier k (toTorus Q θ) = exp (((∑ i, ((k i : ℝ) / Q) * θ i : ℝ) : ℂ) * I) := by
  have hQ' : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [mFourier, ContinuousMap.coe_mk, toTorus, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  field_simp

/-- **A Laurent polynomial vanishing on a ball of angles is zero.** -/
theorem laurentPoly_eq_zero_of_vanish_ball {Q : ℕ} (hQ : 0 < Q) (T : LaurentPoly ι)
    {θ₀ : ι → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ θ ∈ ball θ₀ ε, trigEval (toTorus Q θ) T = 0) : T = 0 := by
  classical
  have hQ' : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hinj : Set.InjOn (fun (k : ι → ℤ) (i : ι) ↦ (k i : ℝ) / Q) T.coeff.support := by
    intro k _ k' _ hkk
    funext i
    have := congrFun hkk i
    simp only at this
    exact_mod_cast (div_left_inj' hQ').mp this
  have hzero := coeff_eq_zero_of_mvExpSum_vanish_box T.coeff.support (fun k i ↦ (k i : ℝ) / Q)
    hinj (fun k ↦ T.coeff k) θ₀ hε fun θ hθ ↦ by
      have hball : θ ∈ ball θ₀ ε := by
        rw [mem_ball, dist_pi_lt_iff hε]
        intro i
        rw [Real.dist_eq]
        exact hθ i
      have := h θ hball
      rw [trigEval_apply] at this
      rw [← this]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [mFourier_toTorus hQ]
  rw [← AddMonoidAlgebra.coeff_eq_zero]
  ext k
  by_contra hk
  exact hk (hzero k (Finsupp.mem_support_iff.mpr hk))

end WeakTiling

end

end

end TorusTrig

/-! ## Step A, first part: the global structure of the slices on the torus -/

section GlobalA

section

noncomputable section

open Complex Finset Polynomial Metric Set UnitAddTorus
open scoped Real

namespace WeakTiling

variable {ι : Type} [Fintype ι]

theorem exists_common_denom {α : Type*} [Fintype α] (q : α → ℚ) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ a, ∃ z : ℤ, (z : ℚ) = q a * Q := by
  classical
  refine ⟨∏ a, (q a).den, Finset.prod_pos fun a _ ↦ (q a).pos, fun a ↦ ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun a ↦ (q a).den) (Finset.mem_univ a)
  refine ⟨(q a).num * m, ?_⟩
  rw [hm]
  push_cast
  rw [← mul_assoc, Rat.mul_den_eq_num]

theorem norm_mFourier_apply (k : ι → ℤ) (t : UnitAddTorus ι) : ‖mFourier k t‖ = 1 := by
  have h := mFourier_add (m := k) (n := -k) (x := t)
  rw [add_neg_cancel, mFourier_zero, mFourier_neg, mul_conj] at h
  have h1 : normSq (mFourier k t) = 1 := by
    have := congrArg re h
    simpa using this.symm
  rw [Complex.norm_def, h1, Real.sqrt_one]

/-- The global monomial data of a lattice tiling datum. -/
structure MonoData (D : LatticeTilingData ι) where
  θ₀ : ι → ℝ
  ε : ℝ
  hε : 0 < ε
  hgen : ∀ θ ∈ ball θ₀ ε, θ ∈ genericSet D
  B : ActiveBranches D (ball θ₀ ε)
  halg : ∀ θ ∈ ball θ₀ ε, ∀ l, (sliceXi D (torusPt θ)).eval (B.root l θ) = 0
  c : Fin B.r → ℂ
  Q : ℕ
  hQ : 0 < Q
  k : Fin B.r → ι → ℤ
  hroot : ∀ θ ∈ ball θ₀ ε, ∀ l, B.root l θ = c l * mFourier (k l) (toTorus Q θ)

theorem exists_monoData (D : LatticeTilingData ι) [Nonempty ι] [DecidableEq ι] :
    Nonempty (MonoData D) := by
  obtain ⟨θ₀, ε, hε, hgen, B, halg, c, s, -, hform⟩ := exists_monomial_branches D
  obtain ⟨Q, hQ, hz⟩ := exists_common_denom (fun p : Fin B.r × ι ↦ s p.1 p.2)
  choose z hz using hz
  refine ⟨⟨θ₀, ε, hε, hgen, B, halg, c, Q, hQ, fun l i ↦ z (l, i), fun θ hθ l ↦ ?_⟩⟩
  rw [hform θ hθ l, mFourier_toTorus hQ]
  have hQ' : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hsum : ∑ i, (s l i : ℝ) * θ i = ∑ i, ((z (l, i) : ℝ) / Q) * θ i := by
    refine sum_congr rfl fun i _ ↦ ?_
    have : ((z (l, i) : ℤ) : ℝ) = (s l i : ℝ) * Q := by exact_mod_cast hz (l, i)
    rw [this, mul_div_cancel_right₀ _ hQ']
  rw [hsum]

namespace MonoData

variable {D : LatticeTilingData ι} (M : MonoData D)

theorem norm_c (l : Fin M.B.r) : ‖M.c l‖ = 1 := by
  have h := M.B.root_unit l M.θ₀ (mem_ball_self M.hε)
  rwa [M.hroot _ (mem_ball_self M.hε), norm_mul, norm_mFourier_apply, mul_one] at h

theorem c_ne_zero (l : Fin M.B.r) : M.c l ≠ 0 := fun h ↦ by simpa [h] using M.norm_c l

theorem distinct {l l' : Fin M.B.r} (h : l ≠ l') : M.k l ≠ M.k l' ∨ M.c l ≠ M.c l' := by
  by_contra hcon
  push Not at hcon
  apply M.B.root_ne M.θ₀ (mem_ball_self M.hε) l l' h
  rw [M.hroot _ (mem_ball_self M.hε) l, M.hroot _ (mem_ball_self M.hε) l', hcon.1, hcon.2]

/-- The roots as Laurent polynomials. -/
def rootT (l : Fin M.B.r) : LaurentPoly ι := AddMonoidAlgebra.single (M.k l) (M.c l)

/-- The slices as Laurent polynomials. -/
def sliceT (m : ℤ) : LaurentPoly ι :=
  ∑ u ∈ sliceFiber m, AddMonoidAlgebra.single (M.Q • u) (D.M u : ℂ)

/-- The roots on the torus. -/
def μT (l : Fin M.B.r) (t : UnitAddTorus ι) : ℂ := M.c l * mFourier (M.k l) t

theorem norm_μT (l : Fin M.B.r) (t : UnitAddTorus ι) : ‖M.μT l t‖ = 1 := by
  rw [μT, norm_mul, M.norm_c, norm_mFourier_apply, one_mul]

theorem μT_ne_zero (l : Fin M.B.r) (t : UnitAddTorus ι) : M.μT l t ≠ 0 := fun h ↦ by
  simpa [h] using M.norm_μT l t

theorem trigEval_rootT (t : UnitAddTorus ι) (l : Fin M.B.r) :
    trigEval t (M.rootT l) = M.μT l t := trigEval_single t _ _

theorem μT_toTorus {θ : ι → ℝ} (hθ : θ ∈ ball M.θ₀ M.ε) (l : Fin M.B.r) :
    M.μT l (toTorus M.Q θ) = M.B.root l θ := (M.hroot θ hθ l).symm

theorem trigEval_sliceT (m : ℤ) (θ : ι → ℝ) :
    trigEval (toTorus M.Q θ) (M.sliceT m) = latticeSlice D (torusPt θ) m := by
  rw [← mvTrigPoly_sliceFiber, sliceT, map_sum, mvTrigPoly]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [trigEval_single, mFourier_toTorus M.hQ, mvChar]
  congr 1
  have hQ' : (M.Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.hQ.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsum : ∑ i, (((M.Q • u) i : ℤ) : ℝ) / M.Q * θ i = ∑ i, (u i : ℝ) * θ i := by
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
    field_simp
  rw [hsum]
  push_cast
  field_simp

/-- The characteristic product `∏ₗ (X - μₗ)` over Laurent polynomials. -/
def charProd : Polynomial (LaurentPoly ι) := ∏ l, (X - C (M.rootT l))

theorem charProd_map (t : UnitAddTorus ι) :
    (M.charProd).map (trigEval t) = ∏ l, (X - C (M.μT l t)) := by
  simp [charProd, Polynomial.map_prod, trigEval_rootT]

theorem prod_X_sub_monic (f : Fin M.B.r → ℂ) : (∏ l, (X - C (f l))).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

theorem prod_X_sub_natDegree (f : Fin M.B.r → ℂ) : (∏ l, (X - C (f l))).natDegree = M.B.r := by
  rw [natDegree_prod_of_monic _ _ fun l _ ↦ monic_X_sub_C _]
  simp

/-- A root of a monic-type product solves the associated recurrence. -/
theorem sum_coeff_mul_zpow_eq_zero (f : Fin M.B.r → ℂ) {μ : ℂ} (hμ0 : μ ≠ 0)
    (hroot : (∏ l, (X - C (f l))).eval μ = 0) (a : ℂ) (m : ℤ) :
    ∑ i ∈ range ((∏ l, (X - C (f l))).natDegree + 1),
      (∏ l, (X - C (f l))).coeff i * (a * μ ^ (m + i : ℤ)) = 0 := by
  calc ∑ i ∈ range ((∏ l, (X - C (f l))).natDegree + 1),
        (∏ l, (X - C (f l))).coeff i * (a * μ ^ (m + i : ℤ))
      = a * μ ^ m * (∏ l, (X - C (f l))).eval μ := by
        rw [eval_eq_sum_range, mul_sum]
        refine sum_congr rfl fun i _ ↦ ?_
        rw [zpow_add₀ hμ0, zpow_natCast]
        ring
    _ = 0 := by rw [hroot, mul_zero]

theorem eval_prod_X_sub_self (f : Fin M.B.r → ℂ) (l : Fin M.B.r) :
    (∏ l', (X - C (f l'))).eval (f l) = 0 := by
  rw [eval_prod]
  exact prod_eq_zero (mem_univ l) (by simp)

/-- The two-sided expansion on the ball. -/
theorem slice_twoSided [Nonempty ι] {θ : ι → ℝ} (hθ : θ ∈ ball M.θ₀ M.ε) (m : ℤ) :
    latticeSlice D (torusPt θ) m = ∑ l, M.B.amp l θ * M.B.root l θ ^ m := by
  have hz0 : ∀ k, torusPt θ k ≠ 0 := fun k h ↦ by simpa [h] using norm_torusPt θ k
  set χ := sliceCharPoly D (torusPt θ) with hχ
  have hχ0 : χ.coeff 0 ≠ 0 := by
    rw [hχ, sliceCharPoly, coeff_C_mul]
    exact mul_ne_zero (inv_ne_zero (sliceXi_coeff_top D _)) (M.hgen θ hθ)
  have hroot : ∀ l, χ.eval (M.B.root l θ) = 0 := by
    intro l
    rw [hχ, sliceCharPoly, eval_mul, eval_C, M.halg θ hθ l, mul_zero]
  have hR : IsZRecurrence χ (fun m ↦ ∑ l, M.B.amp l θ * M.B.root l θ ^ m) := by
    intro m
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_eq_zero fun l _ ↦ ?_
    have hμ0 : M.B.root l θ ≠ 0 := fun h ↦ by simpa [h] using M.B.root_unit l θ hθ
    calc ∑ i ∈ range (χ.natDegree + 1), χ.coeff i * (M.B.amp l θ * M.B.root l θ ^ (m + i : ℤ))
        = M.B.amp l θ * M.B.root l θ ^ m * χ.eval (M.B.root l θ) := by
          rw [eval_eq_sum_range, mul_sum]
          refine sum_congr rfl fun i _ ↦ ?_
          rw [zpow_add₀ hμ0, zpow_natCast]
          ring
      _ = 0 := by rw [hroot, mul_zero]
  have heq := eq_of_isZRecurrence χ hχ0 (latticeSlice_isZRecurrence D hz0) hR fun n ↦ by
    simp only [zpow_natCast]
    exact M.B.rep θ hθ n
  exact congrFun heq m

/-- The recurrence element `∑ⱼ πⱼ a_{m+j}` as a Laurent polynomial. -/
def recElem (m : ℤ) : LaurentPoly ι :=
  ∑ j ∈ range (M.B.r + 1), (M.charProd).coeff j * M.sliceT (m + j)

theorem trigEval_charProd_coeff (t : UnitAddTorus ι) (j : ℕ) :
    trigEval t ((M.charProd).coeff j) = (∏ l, (X - C (M.μT l t))).coeff j := by
  rw [← charProd_map, coeff_map]
  rfl

/-- **The recurrence element vanishes identically.** -/
theorem recElem_eq_zero [Nonempty ι] (m : ℤ) : M.recElem m = 0 := by
  refine laurentPoly_eq_zero_of_vanish_ball (θ₀ := M.θ₀) M.hQ _ M.hε fun θ hθ ↦ ?_
  simp only [recElem, map_sum, map_mul, trigEval_charProd_coeff, trigEval_sliceT]
  have hμ : ∀ l, M.μT l (toTorus M.Q θ) = M.B.root l θ := M.μT_toTorus hθ
  simp only [hμ, M.slice_twoSided hθ, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun l _ ↦ ?_
  have hμ0 : M.B.root l θ ≠ 0 := fun h ↦ by simpa [h] using M.B.root_unit l θ hθ
  have := M.sum_coeff_mul_zpow_eq_zero (fun l ↦ M.B.root l θ) hμ0
    (M.eval_prod_X_sub_self (fun l ↦ M.B.root l θ) l) (M.B.amp l θ) m
  rw [M.prod_X_sub_natDegree] at this
  rw [← this]

/-- **The recurrence at every torus point.** -/
theorem rec_everywhere [Nonempty ι] (t : UnitAddTorus ι) :
    IsZRecurrence (∏ l, (X - C (M.μT l t))) (fun m ↦ trigEval t (M.sliceT m)) := by
  intro m
  have h := congrArg (trigEval t) (M.recElem_eq_zero m)
  simp only [recElem, map_sum, map_mul, trigEval_charProd_coeff, map_zero] at h
  rw [M.prod_X_sub_natDegree]
  rw [← h]

/-- Pairwise distinct roots at a torus point. -/
def NonColl (t : UnitAddTorus ι) : Prop := ∀ l l', l ≠ l' → M.μT l t ≠ M.μT l' t

/-- The Vandermonde-extracted amplitude on the torus. -/
def ampT (l : Fin M.B.r) (t : UnitAddTorus ι) : ℂ :=
  (∏ i ∈ univ.erase l, (M.μT l t - M.μT i t))⁻¹ *
    ∑ j ∈ range M.B.r, (∏ i ∈ univ.erase l, (X - C (M.μT i t))).coeff j *
      trigEval t (M.sliceT j)

/-- **Expansion at non-collision points**, for all `m ∈ ℤ`. -/
theorem nonColl_rep [Nonempty ι] {t : UnitAddTorus ι} (ht : M.NonColl t) (m : ℤ) :
    trigEval t (M.sliceT m) = ∑ l, M.ampT l t * M.μT l t ^ m := by
  classical
  set μ : Fin M.B.r → ℂ := fun l ↦ M.μT l t with hμ
  have hinj : Function.Injective μ := fun l l' h ↦ by
    by_contra hne
    exact ht l l' hne h
  set S := Finset.univ.image μ with hS
  have hPS : ∏ l, (X - C (μ l)) = ∏ a ∈ S, (X - C a) := by
    rw [hS, Finset.prod_image fun l _ l' _ h ↦ hinj h]
  have hmon := M.prod_X_sub_monic μ
  have h0 : (∏ l, (X - C (μ l))).coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, eval_prod]
    refine prod_ne_zero_iff.mpr fun l _ ↦ ?_
    simpa using M.μT_ne_zero l t
  have hrec : IsZRecurrence (∏ l, (X - C (μ l))) (fun m ↦ trigEval t (M.sliceT m)) :=
    M.rec_everywhere t
  obtain ⟨p, hpdeg, hp⟩ := isPolyExpMult_of_linearRecurrence _ hmon h0
    (fun n : ℕ ↦ trigEval t (M.sliceT n)) fun n ↦ by
      have := hrec n
      push_cast at this ⊢
      exact this
  have hroots : (∏ l, (X - C (μ l))).roots = S.val := by rw [hPS, roots_prod_X_sub_C]
  have hconst : ∀ a ∈ S, p a = C ((p a).coeff 0) := by
    intro a ha
    ext k
    rcases k with _ | k
    · simp
    · rw [coeff_C, ite_eq_right (Nat.succ_ne_zero k)]
      refine hpdeg a (k + 1) ?_
      rw [hroots, Multiset.count_eq_one_of_mem S.nodup ha]
      omega
  set V : Fin M.B.r → ℂ := fun l ↦ (p (μ l)).coeff 0 with hV
  have hfwd : ∀ n : ℕ, trigEval t (M.sliceT n) = ∑ l, V l * μ l ^ n := by
    intro n
    have h := hp n
    simp only at h
    rw [h, hroots, Finset.val_toFinset, hS, Finset.sum_image fun l _ l' _ h ↦ hinj h]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [hconst (μ l) (Finset.mem_image_of_mem _ (Finset.mem_univ l)), eval_C]
  have hamp : ∀ l, M.ampT l t = V l := by
    intro l
    have hD : IsUnit (∏ i ∈ univ.erase l, (μ l - μ i)) := by
      refine isUnit_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i hi ↦ sub_ne_zero.mpr ?_)
      exact fun h ↦ ht l i (ne_of_mem_erase hi).symm h
    have hext := sum_extractionWeight_mul_expSum V μ l hD 0
    rw [pow_zero, mul_one, Fintype.card_fin] at hext
    rw [← hext, ampT, mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [extractionWeight_eq, zero_add]
    simp only [expSum]
    rw [← hfwd j]
    simp only [hμ]
    ring
  have hR : IsZRecurrence (∏ l, (X - C (μ l))) (fun m ↦ ∑ l, M.ampT l t * μ l ^ m) := by
    intro m
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_eq_zero fun l _ ↦ M.sum_coeff_mul_zpow_eq_zero μ (M.μT_ne_zero l t)
      (M.eval_prod_X_sub_self μ l) (M.ampT l t) m
  have heq := eq_of_isZRecurrence _ h0 hrec hR fun n ↦ by
    simp only [zpow_natCast]
    rw [hfwd n]
    exact sum_congr rfl fun l _ ↦ by rw [hamp l]
  exact congrFun heq m

/-- **Cesàro bound on the amplitudes.** -/
theorem sum_norm_sq_ampT_le [Nonempty ι] {B₀ : ℝ}
    (hB₀ : ∀ θ : ι → ℝ, ∀ m : ℤ, ‖latticeSlice D (torusPt θ) m‖ ≤ B₀) {t : UnitAddTorus ι}
    (ht : M.NonColl t) : ∑ l, ‖M.ampT l t‖ ^ 2 ≤ B₀ ^ 2 := by
  obtain ⟨θ, rfl⟩ := toTorus_surjective M.hQ t
  have hB0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ θ 0)
  refine sum_norm_sq_le_of_exponential_sum_bounded (fun l ↦ M.ampT l _) (fun l ↦ M.μT l _)
    (fun l ↦ M.norm_μT l _) (fun l l' h ↦ by by_contra hne; exact ht l l' hne h) B₀ hB0
    fun n ↦ ?_
  have := M.nonColl_rep ht n
  simp only [zpow_natCast] at this
  rw [← this, M.trigEval_sliceT]
  exact hB₀ θ n

end MonoData

end WeakTiling

end

end

end GlobalA

/-! ## Step A, second part: the amplitudes are trigonometric polynomials -/

section AmplitudeFourier

section

noncomputable section

open MeasureTheory UnitAddTorus Complex Finset Filter Polynomial
open scoped Real

/-- Same measure as in `Mathlib.Analysis.Fourier.AddCircleMulti`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace WeakTiling

variable {ι : Type} [Fintype ι]

theorem mFourierCoeff_const_mFourier_mul {F : UnitAddTorus ι → ℂ} (hF : Integrable F)
    (k : ι → ℤ) (c : ℂ) (n : ι → ℤ) :
    mFourierCoeff (fun t ↦ c * mFourier k t * F t) n = c * mFourierCoeff F (n - k) := by
  classical
  have h := mFourierCoeff_trigEval_mul hF (AddMonoidAlgebra.single k c) n
  simp only [trigEval_single] at h
  rw [h]
  by_cases hc : c = 0
  · subst hc
    simp
  · have hcoeff : (AddMonoidAlgebra.single k c).coeff = Finsupp.single k c := rfl
    rw [hcoeff, Finsupp.support_single k hc, sum_singleton, Finsupp.single_eq_same]

theorem mFourierCoeff_sub {F G : UnitAddTorus ι → ℂ} (hF : Integrable F) (hG : Integrable G)
    (n : ι → ℤ) :
    mFourierCoeff (fun t ↦ F t - G t) n = mFourierCoeff F n - mFourierCoeff G n := by
  simp only [mFourierCoeff, smul_sub]
  refine integral_sub ?_ ?_
  · exact hF.bdd_mul (c := 1) (mFourier (-n)).continuous.aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ((mFourier (-n)).norm_coe_le_norm t).trans
        (le_of_eq mFourier_norm)) |>.congr (Eventually.of_forall fun t ↦ by simp [smul_eq_mul])
  · exact hG.bdd_mul (c := 1) (mFourier (-n)).continuous.aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ((mFourier (-n)).norm_coe_le_norm t).trans
        (le_of_eq mFourier_norm)) |>.congr (Eventually.of_forall fun t ↦ by simp [smul_eq_mul])

theorem mFourierCoeff_congr_ae {F G : UnitAddTorus ι → ℂ} (h : F =ᵐ[volume] G) (n : ι → ℤ) :
    mFourierCoeff F n = mFourierCoeff G n := by
  refine integral_congr_ae ?_
  filter_upwards [h] with t ht
  rw [ht]

theorem volume_mFourier_eq_null {v : ι → ℤ} (hv : v ≠ 0) (γ : ℂ) :
    volume {t : UnitAddTorus ι | mFourier v t = γ} = 0 := by
  classical
  set Z := {t : UnitAddTorus ι | mFourier v t = γ} with hZ
  have hZm : MeasurableSet Z := (isClosed_eq (mFourier v).continuous continuous_const).measurableSet
  by_cases hγ : ‖γ‖ = 1
  swap
  · have : Z = ∅ := by
      ext t
      simp only [hZ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      apply hγ
      rw [← h, norm_mFourier_apply]
    rw [this, measure_empty]
  set F : UnitAddTorus ι → ℂ := Z.indicator fun _ ↦ 1 with hF
  have hFm : AEStronglyMeasurable F volume :=
    (measurable_const.indicator hZm).aestronglyMeasurable
  have hFb : ∀ t, ‖F t‖ ≤ 1 := fun t ↦ by
    simp only [hF, Set.indicator]
    split_ifs <;> simp
  have hFL : MemLp F 2 volume := MemLp.of_bound hFm 1 (Eventually.of_forall hFb)
  have hFi : Integrable F volume := hFL.integrable (by norm_num)
  -- the multiplicative relation `e_v F = γ F`
  have hrel : ∀ t, 1 * mFourier v t * F t = γ * mFourier 0 t * F t := by
    intro t
    by_cases ht : t ∈ Z
    · simp only [hF, Set.indicator_of_mem ht, mFourier_zero]
      simp only [hZ, Set.mem_ofPred_eq] at ht
      simp [ht]
    · simp [hF, Set.indicator_of_notMem ht]
  have hcoef : ∀ n, mFourierCoeff F (n - v) = γ * mFourierCoeff F n := by
    intro n
    have h1 := mFourierCoeff_const_mFourier_mul hFi v 1 n
    have h2 := mFourierCoeff_const_mFourier_mul hFi 0 γ n
    rw [one_mul] at h1
    rw [sub_zero] at h2
    rw [← h1, ← h2]
    exact congrArg (fun G ↦ mFourierCoeff G n) (funext hrel)
  have hsum := summable_sq_mFourierCoeff hFL
  have hzero : ∀ n, mFourierCoeff F n = 0 := by
    intro n
    refine eq_zero_of_norm_const_along hsum hv n 1 (Or.inl rfl) fun j ↦ ?_
    have := norm_eq_along_forward (f := mFourierCoeff F) (v := v) (a := 1) (b := γ)
      (by rw [norm_one, hγ]) (fun h ↦ by simp [h] at hγ) (S := ∅)
      (fun m _ ↦ by rw [one_mul, hcoef m]) n (fun _ _ ↦ Finset.notMem_empty _) j
    simpa using this
  have hae := ae_eq_zero_of_mFourierCoeff_eq_zero hFL hzero
  refine measure_mono_null (fun t ht ↦ ?_) (ae_iff.mp hae)
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, hF, Set.indicator_of_mem ht]
  exact one_ne_zero

namespace MonoData

variable {D : LatticeTilingData ι} (M : MonoData D)

/-- **Almost every torus point is a non-collision point.** -/
theorem ae_nonColl : ∀ᵐ t ∂(volume : Measure (UnitAddTorus ι)), M.NonColl t := by
  classical
  have hpair : ∀ l l', l ≠ l' →
      volume {t : UnitAddTorus ι | M.μT l t = M.μT l' t} = 0 := by
    intro l l' hll
    by_cases hk : M.k l = M.k l'
    · have hc : M.c l ≠ M.c l' := (M.distinct hll).resolve_left (not_not.mpr hk)
      have : {t : UnitAddTorus ι | M.μT l t = M.μT l' t} = ∅ := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, μT, hk]
        intro h
        have hne : mFourier (M.k l') t ≠ 0 := fun h' ↦ by
          simpa [h'] using norm_mFourier_apply (M.k l') t
        exact hc (mul_right_cancel₀ hne h)
      rw [this, measure_empty]
    · refine measure_mono_null (fun t ht ↦ ?_)
        (volume_mFourier_eq_null (sub_ne_zero.mpr hk) (M.c l' / M.c l))
      simp only [Set.mem_ofPred_eq, μT] at ht ⊢
      have h0 : M.c l ≠ 0 := M.c_ne_zero l
      have hne : mFourier (M.k l') t ≠ 0 := fun h ↦ by
        simpa [h] using norm_mFourier_apply (M.k l') t
      have hm : mFourier (M.k l) t = mFourier (M.k l - M.k l') t * mFourier (M.k l') t := by
        rw [← mFourier_add, sub_add_cancel]
      rw [hm, ← mul_assoc] at ht
      have := mul_right_cancel₀ hne ht
      rw [eq_div_iff h0, mul_comm]
      exact this
  have hunion : volume (⋃ p : Fin M.B.r × Fin M.B.r,
      {t : UnitAddTorus ι | p.1 ≠ p.2 ∧ M.μT p.1 t = M.μT p.2 t}) = 0 := by
    refine measure_iUnion_null fun p ↦ ?_
    by_cases hp : p.1 = p.2
    · simp [hp]
    · exact measure_mono_null (fun t ht ↦ ht.2) (hpair p.1 p.2 hp)
  rw [ae_iff]
  refine measure_mono_null (fun t ht ↦ ?_) hunion
  simp only [Set.mem_ofPred_eq, NonColl, not_forall] at ht
  obtain ⟨l, l', hll, h⟩ := ht
  exact Set.mem_iUnion.mpr ⟨(l, l'), hll, not_not.mp h⟩

/-- The numerator Laurent polynomial `Pₗ`. -/
def numT (l : Fin M.B.r) : LaurentPoly ι :=
  ∑ j ∈ range M.B.r, (∏ i ∈ univ.erase l, (X - C (M.rootT i))).coeff j * M.sliceT j

theorem trigEval_prod_erase_coeff (l : Fin M.B.r) (t : UnitAddTorus ι) (j : ℕ) :
    trigEval t ((∏ i ∈ univ.erase l, (X - C (M.rootT i))).coeff j) =
      (∏ i ∈ univ.erase l, (X - C (M.μT i t))).coeff j := by
  have hmap : (∏ i ∈ univ.erase l, (X - C (M.rootT i))).map (trigEval t) =
      ∏ i ∈ univ.erase l, (X - C (M.μT i t)) := by
    simp [Polynomial.map_prod, trigEval_rootT]
  rw [← hmap, coeff_map]
  rfl

theorem trigEval_numT (l : Fin M.B.r) (t : UnitAddTorus ι) :
    trigEval t (M.numT l) = ∑ j ∈ range M.B.r,
      (∏ i ∈ univ.erase l, (X - C (M.μT i t))).coeff j * trigEval t (M.sliceT j) := by
  simp only [numT, map_sum, map_mul, trigEval_prod_erase_coeff]

/-- The collision denominator `Δₗ`. -/
def denom (l : Fin M.B.r) (t : UnitAddTorus ι) : ℂ := ∏ i ∈ univ.erase l, (M.μT l t - M.μT i t)

theorem ampT_eq (l : Fin M.B.r) (t : UnitAddTorus ι) :
    M.ampT l t = (M.denom l t)⁻¹ * trigEval t (M.numT l) := by
  rw [ampT, trigEval_numT, denom]

theorem continuous_μT (l : Fin M.B.r) : Continuous (M.μT l) :=
  continuous_const.mul (mFourier (M.k l)).continuous

theorem continuous_denom (l : Fin M.B.r) : Continuous (M.denom l) :=
  continuous_finsetProd _ fun i _ ↦ (M.continuous_μT l).sub (M.continuous_μT i)

theorem measurable_ampT (l : Fin M.B.r) : Measurable (M.ampT l) := by
  have : M.ampT l = fun t ↦ (M.denom l t)⁻¹ * trigEval t (M.numT l) := funext (M.ampT_eq l)
  rw [this]
  exact ((M.continuous_denom l).measurable.inv).mul (continuous_trigEval _).measurable

theorem denom_ne_zero {l : Fin M.B.r} {t : UnitAddTorus ι} (ht : M.NonColl t) :
    M.denom l t ≠ 0 :=
  prod_ne_zero_iff.mpr fun i hi ↦ sub_ne_zero.mpr fun h ↦ ht l i (ne_of_mem_erase hi).symm h

/-- The amplitudes are bounded almost everywhere. -/
theorem ae_norm_ampT_le [Nonempty ι] {B : ℝ}
    (hB : ∀ θ : ι → ℝ, ∀ m : ℤ, ‖latticeSlice D (torusPt θ) m‖ ≤ B) (l : Fin M.B.r) :
    ∀ᵐ t ∂(volume : Measure (UnitAddTorus ι)), ‖M.ampT l t‖ ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  filter_upwards [M.ae_nonColl] with t ht
  have h := M.sum_norm_sq_ampT_le hB ht
  have h1 : ‖M.ampT l t‖ ^ 2 ≤ B ^ 2 :=
    (single_le_sum (f := fun i ↦ ‖M.ampT i t‖ ^ 2) (fun i _ ↦ sq_nonneg _) (mem_univ l)).trans h
  exact (sq_le_sq₀ (norm_nonneg _) hB0).mp h1

theorem memLp_ampT [Nonempty ι] (l : Fin M.B.r) : MemLp (M.ampT l) 2 volume := by
  obtain ⟨B, hB⟩ := norm_latticeSlice_le D
  exact MemLp.of_bound (M.measurable_ampT l).aestronglyMeasurable B
    (M.ae_norm_ampT_le (fun θ m ↦ hB (norm_torusPt θ) m) l)

/-- **The collision poles cancel: each amplitude has finitely many Fourier coefficients.** -/
theorem finite_support_mFourierCoeff_ampT [Nonempty ι] (l : Fin M.B.r) :
    (Function.support (mFourierCoeff (M.ampT l))).Finite := by
  classical
  obtain ⟨B, hB⟩ := norm_latticeSlice_le D
  have hB' : ∀ θ : ι → ℝ, ∀ m : ℤ, ‖latticeSlice D (torusPt θ) m‖ ≤ B :=
    fun θ m ↦ hB (norm_torusPt θ) m
  set E := univ.erase l with hE
  set G : Finset (Fin M.B.r) → UnitAddTorus ι → ℂ :=
    fun J t ↦ (∏ i ∈ E \ J, (M.μT l t - M.μT i t)) * M.ampT l t with hG
  -- every partial product is in `L²`
  have hGL : ∀ J, MemLp (G J) 2 volume := by
    intro J
    have hmeas : AEStronglyMeasurable (G J) volume :=
      ((continuous_finsetProd _ fun i _ ↦ (M.continuous_μT l).sub
        (M.continuous_μT i)).measurable.mul (M.measurable_ampT l)).aestronglyMeasurable
    refine MemLp.of_bound hmeas (2 ^ (E \ J).card * B) ?_
    filter_upwards [M.ae_norm_ampT_le hB' l] with t ht
    rw [hG, norm_mul, norm_prod]
    refine mul_le_mul ?_ ht (norm_nonneg _) (by positivity)
    calc ∏ i ∈ E \ J, ‖M.μT l t - M.μT i t‖ ≤ ∏ _i ∈ E \ J, (2 : ℝ) := by
          gcongr with i hi
          exact (norm_sub_le _ _).trans (by rw [M.norm_μT, M.norm_μT]; norm_num)
      _ = 2 ^ (E \ J).card := by rw [prod_const]
  have hGi : ∀ J, Integrable (G J) volume := fun J ↦ (hGL J).integrable (by norm_num)
  -- the statement for all `J ⊆ E`, by induction on `J`
  have hind : ∀ J : Finset (Fin M.B.r), J ⊆ E →
      (Function.support (mFourierCoeff (G J))).Finite := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _
      have hae : G ∅ =ᵐ[volume] fun t ↦ trigEval t (M.numT l) := by
        filter_upwards [M.ae_nonColl] with t ht
        simp only [hG, sdiff_empty]
        rw [M.ampT_eq, ← mul_assoc,
          show (∏ x ∈ E, (M.μT l t - M.μT x t)) = M.denom l t from rfl,
          mul_inv_cancel₀ (M.denom_ne_zero ht), one_mul]
      refine (M.numT l).coeff.finite_support.subset fun n hn ↦ ?_
      rw [Function.mem_support, mFourierCoeff_congr_ae hae, mFourierCoeff_trigEval] at hn
      exact hn
    | insert i J hiJ ih =>
      intro hsub
      have hiE : i ∈ E := hsub (mem_insert_self i J)
      have hfin := ih ((subset_insert i J).trans hsub)
      set H := G (insert i J) with hH
      -- `G J = (μₗ - μᵢ) · H`
      have hGJ : ∀ t, G J t = M.c l * mFourier (M.k l) t * H t -
          M.c i * mFourier (M.k i) t * H t := by
        intro t
        have hsd : E \ J = insert i (E \ insert i J) := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hxE, hxJ⟩
            by_cases hx : x = i
            · exact Or.inl hx
            · exact Or.inr ⟨hxE, fun h ↦ h.elim hx hxJ⟩
          · rintro (rfl | ⟨hxE, hx⟩)
            · exact ⟨hiE, hiJ⟩
            · exact ⟨hxE, fun h ↦ hx (Or.inr h)⟩
        have hnot : i ∉ E \ insert i J := fun h ↦
          (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self i J)
        simp only [hH, hG]
        rw [hsd, prod_insert hnot]
        simp only [μT]
        ring
      have hcoef : ∀ n, mFourierCoeff (G J) n =
          M.c l * mFourierCoeff H (n - M.k l) - M.c i * mFourierCoeff H (n - M.k i) := by
        intro n
        rw [show G J = fun t ↦ M.c l * mFourier (M.k l) t * H t -
            M.c i * mFourier (M.k i) t * H t from funext hGJ]
        rw [mFourierCoeff_sub, mFourierCoeff_const_mFourier_mul (hGi _),
          mFourierCoeff_const_mFourier_mul (hGi _)]
        · exact (hGi _).bdd_mul (c := ‖M.c l‖) ((continuous_const.mul
            (mFourier (M.k l)).continuous).aestronglyMeasurable)
            (Eventually.of_forall fun t ↦ by rw [norm_mul, norm_mFourier_apply, mul_one])
        · exact (hGi _).bdd_mul (c := ‖M.c i‖) ((continuous_const.mul
            (mFourier (M.k i)).continuous).aestronglyMeasurable)
            (Eventually.of_forall fun t ↦ by rw [norm_mul, norm_mFourier_apply, mul_one])
      have hil : l ≠ i := (ne_of_mem_erase hiE).symm
      by_cases hk : M.k l = M.k i
      · -- equal exponents: a nonzero multiple of a shift
        have hc : M.c l - M.c i ≠ 0 :=
          sub_ne_zero.mpr ((M.distinct hil).resolve_left (not_not.mpr hk))
        refine (hfin.image fun n ↦ n - M.k l).subset fun m hm ↦ ?_
        refine ⟨m + M.k l, ?_, by simp⟩
        rw [Function.mem_support, hcoef, hk, add_sub_cancel_right, ← sub_mul]
        exact mul_ne_zero hc hm
      · -- different exponents: the `ℓ²` binomial lemma
        refine finite_support_of_binomial (summable_sq_mFourierCoeff (hGL _))
          (sub_ne_zero.mpr hk) (a := M.c l) (b := M.c i) (by rw [M.norm_c, M.norm_c])
          (M.c_ne_zero i) (hfin.toFinset.image fun n ↦ n - M.k i) fun m hm ↦ ?_
        have hnot : m + M.k i ∉ Function.support (mFourierCoeff (G J)) := by
          intro h
          apply hm
          exact Finset.mem_image.mpr ⟨m + M.k i, hfin.mem_toFinset.mpr h, by simp⟩
        rw [Function.notMem_support, hcoef] at hnot
        have h1 : m + M.k i - M.k l = m - (M.k l - M.k i) := by abel
        rw [h1, add_sub_cancel_right] at hnot
        exact sub_eq_zero.mp hnot
  have hfinal := hind E subset_rfl
  have hGE : G E = M.ampT l := by
    funext t
    simp [hG]
  rwa [hGE] at hfinal

end MonoData

end WeakTiling

end

end

end AmplitudeFourier

/-! ## The lattice core theorem and FC Problem 4.1 -/

section CoreTheorem

section

noncomputable section

open MeasureTheory UnitAddTorus Complex Finset Filter Polynomial ComplexConjugate
open scoped Real

/-- Same measure as in `Mathlib.Analysis.Fourier.AddCircleMulti`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace WeakTiling

theorem mFourier_nsmul {ι : Type} [Fintype ι] (n : ℕ) (k : ι → ℤ) (t : UnitAddTorus ι) :
    mFourier (n • k) t = mFourier k t ^ n := by
  induction n with
  | zero => simp [mFourier_zero]
  | succ n ih => rw [succ_nsmul, mFourier_add, ih, pow_succ]

theorem mFourier_zsmul {ι : Type} [Fintype ι] (m : ℤ) (k : ι → ℤ) (t : UnitAddTorus ι) :
    mFourier (m • k) t = mFourier k t ^ m := by
  rcases m with n | n
  · simp only [Int.ofNat_eq_natCast, natCast_zsmul, zpow_natCast]
    exact mFourier_nsmul n k t
  · have hnorm : ‖mFourier ((n + 1 : ℕ) • k) t‖ = 1 := norm_mFourier_apply _ t
    have hinv : conj (mFourier ((n + 1 : ℕ) • k) t) = (mFourier ((n + 1 : ℕ) • k) t)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
      simp
    rw [negSucc_zsmul, mFourier_neg, hinv, mFourier_nsmul, zpow_negSucc]

theorem mFourierCoeff_finset_sum {ι : Type} [Fintype ι] {α : Type*} (s : Finset α)
    {F : α → UnitAddTorus ι → ℂ} (hF : ∀ a ∈ s, Integrable (F a)) (n : ι → ℤ) :
    mFourierCoeff (fun t ↦ ∑ a ∈ s, F a t) n = ∑ a ∈ s, mFourierCoeff (F a) n := by
  simp only [mFourierCoeff, Finset.smul_sum]
  refine integral_finsetSum _ fun a ha ↦ ?_
  exact (hF a ha).bdd_mul (c := 1) (mFourier (-n)).continuous.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ((mFourier (-n)).norm_coe_le_norm t).trans
      (le_of_eq mFourier_norm)) |>.congr (Eventually.of_forall fun t ↦ by simp [smul_eq_mul])

namespace MonoData

variable {ι : Type} [Fintype ι] {D : LatticeTilingData ι} (M : MonoData D)

theorem μT_zpow (l : Fin M.B.r) (t : UnitAddTorus ι) (m : ℤ) :
    M.μT l t ^ m = M.c l ^ m * mFourier (m • M.k l) t := by
  rw [μT, mul_zpow, mFourier_zsmul]

/-- **Fourier matching of the slices.** -/
theorem sliceT_coeff_eq [Nonempty ι] (m : ℤ) (n : ι → ℤ) :
    (M.sliceT m).coeff n = ∑ l, M.c l ^ m * mFourierCoeff (M.ampT l) (n - m • M.k l) := by
  have hae : (fun t ↦ trigEval t (M.sliceT m)) =ᵐ[volume]
      fun t ↦ ∑ l, M.c l ^ m * mFourier (m • M.k l) t * M.ampT l t := by
    filter_upwards [M.ae_nonColl] with t ht
    rw [M.nonColl_rep ht m]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [M.μT_zpow]
    ring
  have hint : ∀ l ∈ (univ : Finset (Fin M.B.r)),
      Integrable (fun t ↦ M.c l ^ m * mFourier (m • M.k l) t * M.ampT l t) volume := by
    intro l _
    have hi := (M.memLp_ampT l).integrable (by norm_num)
    refine (hi.bdd_mul (c := ‖M.c l ^ m‖) ((continuous_const.mul
      (mFourier (m • M.k l)).continuous).aestronglyMeasurable) ?_)
    exact Eventually.of_forall fun t ↦ by rw [norm_mul, norm_mFourier_apply, mul_one]
  rw [← mFourierCoeff_trigEval, mFourierCoeff_congr_ae hae, mFourierCoeff_finset_sum _ hint]
  refine sum_congr rfl fun l _ ↦ ?_
  exact mFourierCoeff_const_mFourier_mul ((M.memLp_ampT l).integrable (by norm_num)) _ _ _

theorem nsmul_Q_injective : Function.Injective fun u : ι → ℤ ↦ M.Q • u := by
  intro u u' h
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr M.hQ.ne') this

theorem sliceT_coeff_Q (m : ℤ) {u : ι → ℤ} (hdeg : latticeDeg u = m) (hM : D.M u ≠ 0) :
    (M.sliceT m).coeff (M.Q • u) = D.M u := by
  classical
  have hmem : u ∈ sliceFiber m := by
    rw [sliceFiber, Finset.mem_filter]
    exact ⟨hdeg ▸ mem_sliceBox_of_ne_zero D hM, hdeg⟩
  rw [sliceT, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [sum_eq_single u]
  · simp
  · intro u' _ hu'
    rw [ite_eq_right]
    exact fun h ↦ hu' (M.nsmul_Q_injective h)
  · intro h
    exact absurd hmem h

/-- **Every atom lies on a rational ray.** -/
theorem exists_ray_rep [Nonempty ι] {u : ι → ℤ} (hM : D.M u ≠ 0) :
    ∃ l, M.Q • u - latticeDeg u • M.k l ∈ Function.support (mFourierCoeff (M.ampT l)) := by
  by_contra hno
  push Not at hno
  apply hM
  have h := M.sliceT_coeff_eq (latticeDeg u) (M.Q • u)
  rw [M.sliceT_coeff_Q _ rfl hM] at h
  have h0 : (D.M u : ℂ) = 0 := by
    rw [h]
    refine sum_eq_zero fun l _ ↦ ?_
    rw [Function.notMem_support.mp (hno l), mul_zero]
  exact_mod_cast h0

end MonoData

theorem hasFiniteLatticeRayCover_of_finset {ι α : Type*} (F : Finset α) (w : α → ι → ℤ)
    (v : α → ι → ℕ) (hv : ∀ a ∈ F, v a ≠ 0) {E S : Set (ι → ℤ)} (hE : E.Finite)
    (hS : S ⊆ E ∪ ⋃ a ∈ F, latticeRay (w a) (v a)) : HasFiniteLatticeRayCover S := by
  classical
  let e := F.equivFin
  refine ⟨E, F.card, fun j ↦ w (e.symm j), fun j ↦ v (e.symm j), hE,
    fun j ↦ hv _ (e.symm j).2, fun u hu ↦ ?_⟩
  rcases hS hu with h | h
  · exact Or.inl h
  · obtain ⟨a, ha, hua⟩ := Set.mem_iUnion₂.mp h
    refine Or.inr (Set.mem_iUnion.mpr ⟨e ⟨a, ha⟩, ?_⟩)
    simpa using hua

theorem hasFiniteLatticeRayCover_of_finite {ι : Type*} {S : Set (ι → ℤ)} (hS : S.Finite) :
    HasFiniteLatticeRayCover S :=
  ⟨S, 0, fun j ↦ j.elim0, fun j ↦ j.elim0, hS, fun j ↦ j.elim0, fun _ hu ↦ Or.inl hu⟩

/-- **Rational rays in the positive orthant are covered by finitely many lattice rays.** -/
theorem hasFiniteLatticeRayCover_of_rational {ι : Type*} [Fintype ι] {r Q : ℕ} (hQ : 0 < Q)
    (k : Fin r → ι → ℤ) (K : Fin r → Finset (ι → ℤ)) {S : Set (ι → ℤ)}
    (hS : ∀ u ∈ S, (∀ i, 0 ≤ u i) ∧
      ∃ l, ∃ κ ∈ K l, ∃ d : ℕ, Q • u = κ + (d : ℤ) • k l) :
    HasFiniteLatticeRayCover S := by
  classical
  have hQinj : Function.Injective fun u : ι → ℤ ↦ Q • u := by
    intro u u' h
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, nsmul_eq_mul] at this
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hQ.ne') this
  -- the triples `(l, κ, ρ)`
  set T : Finset (Σ _ : Fin r, (ι → ℤ) × ℕ) :=
    (univ : Finset (Fin r)).sigma fun l ↦ K l ×ˢ range Q with hT
  -- the base point of a triple
  set base : (Σ _ : Fin r, (ι → ℤ) × ℕ) → ι → ℤ := fun τ ↦
    if h : ∃ w : ι → ℤ, Q • w = τ.2.1 + (τ.2.2 : ℤ) • k τ.1 then h.choose else 0 with hbase
  -- a bound for the finitely many points on a ray with a negative direction
  set bound : (Σ _ : Fin r, (ι → ℤ) × ℕ) → ℕ := fun τ ↦ ∑ i, (base τ i).natAbs with hbound
  set E : Set (ι → ℤ) := ⋃ τ ∈ T,
    ((Finset.range (bound τ + 1)).image fun j : ℕ ↦ base τ + (j : ℤ) • k τ.1 : Set (ι → ℤ))
    with hE
  have hEfin : E.Finite := Set.Finite.biUnion T.finite_toSet fun τ _ ↦ Finset.finite_toSet _
  set good : Finset (Σ _ : Fin r, (ι → ℤ) × ℕ) :=
    T.filter fun τ ↦ (∀ i, 0 ≤ k τ.1 i) ∧ k τ.1 ≠ 0 with hgood
  refine hasFiniteLatticeRayCover_of_finset good base (fun τ i ↦ (k τ.1 i).toNat)
    (fun τ hτ ↦ ?_) hEfin fun u hu ↦ ?_
  · -- nonzero directions
    obtain ⟨-, hnn, hne⟩ := Finset.mem_filter.mp hτ
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    intro h
    have := congrFun h i
    simp only [Pi.zero_apply, Int.toNat_eq_zero] at this
    exact hi (le_antisymm this (hnn i))
  -- decompose the ray index
  obtain ⟨hnn, l, κ, hκ, d, hd⟩ := hS u hu
  set ρ := d % Q with hρ
  set j := d / Q with hj
  have hdρ : (d : ℤ) = ρ + Q * j := by
    have := Nat.mod_add_div d Q
    rw [hρ, hj]
    exact_mod_cast this.symm
  have hτT : (⟨l, κ, ρ⟩ : Σ _ : Fin r, (ι → ℤ) × ℕ) ∈ T := by
    rw [hT, Finset.mem_sigma]
    exact ⟨mem_univ l, Finset.mem_product.mpr ⟨hκ, Finset.mem_range.mpr (Nat.mod_lt d hQ)⟩⟩
  have hex : ∃ w : ι → ℤ, Q • w = κ + (ρ : ℤ) • k l := by
    refine ⟨u - (j : ℤ) • k l, ?_⟩
    funext i
    have := congrFun hd i
    simp only [Pi.smul_apply, nsmul_eq_mul, Pi.add_apply, smul_eq_mul, Pi.sub_apply] at this ⊢
    rw [hdρ] at this
    linarith
  have hbaseτ : Q • base ⟨l, κ, ρ⟩ = κ + (ρ : ℤ) • k l := by
    simp only [hbase]
    rw [dite_eq_left hex]
    exact hex.choose_spec
  -- `u = base + j • kₗ`
  have hu_eq : u = base ⟨l, κ, ρ⟩ + (j : ℤ) • k l := by
    apply hQinj
    simp only
    rw [smul_add, hbaseτ, hd, hdρ]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply]
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  by_cases hgoodτ : (∀ i, 0 ≤ k l i) ∧ k l ≠ 0
  · -- on a genuine lattice ray
    refine Or.inr (Set.mem_iUnion₂.mpr ⟨⟨l, κ, ρ⟩, Finset.mem_filter.mpr ⟨hτT, hgoodτ⟩, j, ?_⟩)
    rw [hu_eq]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Int.toNat_of_nonneg (hgoodτ.1 i)]
  · -- finitely many points
    refine Or.inl (Set.mem_iUnion₂.mpr ⟨⟨l, κ, ρ⟩, hτT, ?_⟩)
    rw [Finset.coe_image]
    rw [not_and_or, not_forall, not_not] at hgoodτ
    rcases hgoodτ with ⟨i, hi⟩ | hzero
    · -- a negative direction bounds `j`
      refine ⟨j, Finset.mem_coe.mpr (Finset.mem_range.mpr ?_), hu_eq.symm⟩
      have hi' : k l i ≤ -1 := by omega
      have hui := hnn i
      rw [hu_eq] at hui
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hui
      have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
      have h1 : (j : ℤ) ≤ base ⟨l, κ, ρ⟩ i := by nlinarith
      have hjle : (j : ℤ) ≤ (base ⟨l, κ, ρ⟩ i).natAbs := h1.trans Int.le_natAbs
      have hsum : (base ⟨l, κ, ρ⟩ i).natAbs ≤ bound ⟨l, κ, ρ⟩ :=
        Finset.single_le_sum (f := fun i ↦ (base ⟨l, κ, ρ⟩ i).natAbs)
          (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
      omega
    · -- zero direction: `u` is the base point
      refine ⟨0, Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.succ_pos _)), ?_⟩
      rw [hu_eq, hzero]
      simp

namespace MonoData

variable {ι : Type} [Fintype ι] {D : LatticeTilingData ι} (M : MonoData D)

theorem latticeDeg_neg (u : ι → ℤ) : latticeDeg (-u) = -latticeDeg u := by
  simp [latticeDeg, sum_neg_distrib]

/-- **The positive side is covered by finitely many lattice rays.** -/
theorem pos_cover [Nonempty ι] (M : MonoData D) :
    HasFiniteLatticeRayCover {u | (∀ k, 0 ≤ u k) ∧ D.M u ≠ 0} := by
  classical
  refine hasFiniteLatticeRayCover_of_rational M.hQ M.k
    (fun l ↦ (M.finite_support_mFourierCoeff_ampT l).toFinset) fun u hu ↦ ⟨hu.1, ?_⟩
  obtain ⟨l, hl⟩ := M.exists_ray_rep hu.2
  have hdeg : 0 ≤ latticeDeg u := Finset.sum_nonneg fun i _ ↦ hu.1 i
  refine ⟨l, M.Q • u - latticeDeg u • M.k l,
    (Set.Finite.mem_toFinset _).mpr hl, (latticeDeg u).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hdeg, sub_add_cancel]

/-- **The reflected negative side is covered by finitely many lattice rays.** -/
theorem neg_cover [Nonempty ι] (M : MonoData D) :
    HasFiniteLatticeRayCover {u | (∀ k, 0 ≤ u k) ∧ D.M (-u) ≠ 0} := by
  classical
  refine hasFiniteLatticeRayCover_of_rational M.hQ M.k
    (fun l ↦ ((M.finite_support_mFourierCoeff_ampT l).toFinset).image Neg.neg)
    fun u hu ↦ ⟨hu.1, ?_⟩
  obtain ⟨l, hl⟩ := M.exists_ray_rep hu.2
  have hdeg : 0 ≤ latticeDeg u := Finset.sum_nonneg fun i _ ↦ hu.1 i
  refine ⟨l, -(M.Q • -u - latticeDeg (-u) • M.k l),
    Finset.mem_image.mpr ⟨_, (Set.Finite.mem_toFinset _).mpr hl, rfl⟩,
    (latticeDeg u).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hdeg, latticeDeg_neg, smul_neg, neg_smul]
  abel

end MonoData

/-- **The lattice core hypothesis holds**: steps H and A. -/
theorem latticeCoreHypothesis_holds : LatticeCoreHypothesis := by
  intro ι _ D
  classical
  by_cases hne : Nonempty ι
  · obtain ⟨M⟩ := exists_monoData D
    exact ⟨M.pos_cover, M.neg_cover⟩
  · have hsub : Subsingleton (ι → ℤ) := ⟨fun a b ↦ funext fun i ↦ (hne ⟨i⟩).elim⟩
    exact ⟨hasFiniteLatticeRayCover_of_finite (Set.toFinite _),
      hasFiniteLatticeRayCover_of_finite (Set.toFinite _)⟩

/-- **FC Problem 4.1 in the exact answer form**: the answer is `True`. -/
theorem problem_4_1_answer_true :
    True ↔ ∀ (Ω : Set ℝ) (_ : IsFiniteUnionOfIntervals Ω)
      (ν : Measure ℝ) (_ : IsWeakTilingMeasure Ω ν), HasBoundedDensity ν.support :=
  problem_4_1_answer_true_of_latticeCore latticeCoreHypothesis_holds

end WeakTiling

end

end

end CoreTheorem

/-! ## The Formal Conjectures statement -/

section FormalConjecturesStatement

open MeasureTheory Set ENNReal NNReal

namespace WeakTiling

/-- **Weak Tiling Problem 4.1, solved.**  The support of every weak tiling measure of a finite
union of intervals has bounded density.  This is `WeakTiling.problem_4_1` from Formal
Conjectures, with its answer hole filled by `True`. -/
theorem problem_4_1_solved :
    True ↔ ∀ (Ω : Set ℝ) (_ : IsFiniteUnionOfIntervals Ω)
      (ν : Measure ℝ) (_ : IsWeakTilingMeasure Ω ν), HasBoundedDensity ν.support :=
  problem_4_1_answer_true

end WeakTiling

end FormalConjecturesStatement

#print axioms WeakTiling.problem_4_1_solved
