/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.RationalFunction
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.Topology.Algebra.Polynomial

/-!
# Algebra of nonnegativity away from poles
-/

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

theorem isFracRep_num_den
    (r : FracPoly) :
    IsFracRep r (IsFractionRing.num Poly r) ↑(IsFractionRing.den Poly r) := by
  refine ⟨nonZeroDivisors.ne_zero (IsFractionRing.den Poly r).2, ?_⟩
  exact (IsFractionRing.mk'_num_den' Poly r).symm

theorem isFracRep_mul_den_sq
    {r : FracPoly}
    {p q : Poly}
    (hrep : IsFracRep r p q) :
    IsFracRep r (p * q) (q ^ 2) := by
  rcases hrep with ⟨hq0, hr⟩
  refine ⟨pow_ne_zero 2 hq0, ?_⟩
  calc
    r = algebraMap Poly FracPoly p / algebraMap Poly FracPoly q := hr
    _ = algebraMap Poly FracPoly (p * q) / algebraMap Poly FracPoly (q ^ 2) := by
          have hqf : algebraMap Poly FracPoly q ≠ 0 := by
            exact (map_ne_zero_iff _ (IsFractionRing.injective Poly FracPoly)).mpr hq0
          field_simp [hqf]
          simp [map_mul, pow_two, mul_left_comm]

theorem eval_mul_den_nonneg_of_nonneg_where_defined
    {r : FracPoly}
    {p q : Poly}
    (hr : RatNonnegWhereDefined r)
    (hrep : IsFracRep r p q) :
    ∀ x : ℝ, 0 ≤ (p * q).eval x := by
  intro x
  by_cases hqx : q.eval x = 0
  · simp [Polynomial.eval_mul, hqx]
  · have hrep' : IsFracRep r (p * q) (q ^ 2) := isFracRep_mul_den_sq hrep
    have hfrac :
        0 ≤ ((p * q).eval x) / ((q ^ 2).eval x) := by
      exact hr x hrep' (by simpa [Polynomial.eval_pow] using pow_ne_zero 2 hqx)
    have hq2pos : 0 < (q ^ 2).eval x := by
      simpa [Polynomial.eval_pow] using sq_pos_iff.mpr hqx
    have hcancel :
        (((p * q).eval x) / ((q ^ 2).eval x)) * ((q ^ 2).eval x) = (p * q).eval x := by
      field_simp [show ((q ^ 2).eval x) ≠ 0 by linarith]
    exact hcancel ▸ mul_nonneg hfrac hq2pos.le

theorem eventually_eval_ne_zero_punctured_nhds
    {p : Poly}
    (hp : p ≠ 0)
    (x : ℝ) :
    ∀ᶠ y in nhdsWithin x ({x}ᶜ), p.eval y ≠ 0 := by
  by_cases hx : p.eval x = 0
  · have hroot : x ∈ ((p.roots.toFinset : Finset ℝ) : Set ℝ) := by
      exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).2 hx))
    obtain ⟨ε, hε, hclosed⟩ :
        ∃ ε > 0, Metric.closedBall x ε ∩ (((p.roots.toFinset : Finset ℝ) : Set ℝ)) = {x} := by
      exact Metric.exists_closedBall_inter_eq_singleton_of_discrete
        ((Set.toFinite (((p.roots.toFinset : Finset ℝ) : Set ℝ))).isDiscrete) hroot
    change {y : ℝ | p.eval y ≠ 0} ∈ nhdsWithin x ({x}ᶜ)
    rw [Metric.mem_nhdsWithin_iff]
    refine ⟨ε, hε, ?_⟩
    intro y hy
    rcases hy with ⟨hyball, hyne⟩
    have hyball' : y ∈ Metric.closedBall x ε := Metric.mem_closedBall.mpr (le_of_lt hyball)
    have hyroot : y ∉ (((p.roots.toFinset : Finset ℝ) : Set ℝ)) := by
      intro hy_mem
      have : y = x := by
        have hy_inter : y ∈ Metric.closedBall x ε ∩ (((p.roots.toFinset : Finset ℝ) : Set ℝ)) :=
          ⟨hyball', hy_mem⟩
        simpa [hclosed] using hy_inter
      exact hyne this
    intro hpy
    exact hyroot (Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).2 hpy)))
  · have hcont : ContinuousAt (fun y : ℝ => p.eval y) x := p.continuousAt_aeval
    have hopen : IsOpen ({0}ᶜ : Set ℝ) := isOpen_ne
    have hmem : p.eval x ∈ ({0}ᶜ : Set ℝ) := by simpa using hx
    exact nhdsWithin_le_nhds (hcont.preimage_mem_nhds (hopen.mem_nhds hmem))

theorem isFracRep_mul
    {a b : FracPoly}
    {an ad bn bd : Poly}
    (ha : IsFracRep a an ad)
    (hb : IsFracRep b bn bd) :
    IsFracRep (a * b) (an * bn) (ad * bd) := by
  rcases ha with ⟨had0, had⟩
  rcases hb with ⟨hbd0, hbd⟩
  have hadf0 : algebraMap Poly FracPoly ad ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective Poly FracPoly)).mpr had0
  have hbdf0 : algebraMap Poly FracPoly bd ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective Poly FracPoly)).mpr hbd0
  refine ⟨mul_ne_zero had0 hbd0, ?_⟩
  calc
    a * b
        = (algebraMap Poly FracPoly an / algebraMap Poly FracPoly ad) *
            (algebraMap Poly FracPoly bn / algebraMap Poly FracPoly bd) := by rw [had, hbd]
    _ = algebraMap Poly FracPoly (an * bn) / algebraMap Poly FracPoly (ad * bd) := by
          field_simp [hadf0, hbdf0]
          simp [map_mul, mul_comm, mul_left_comm]

/-- The value of a rational function at a defined real point is independent of
the chosen polynomial numerator and denominator. -/
theorem eval_eq_of_isFracRep
    {r : FracPoly}
    {num den num' den' : Poly}
    (hrep : IsFracRep r num den)
    (hrep' : IsFracRep r num' den')
    (hdenx : den.eval x ≠ 0)
    (hdenx' : den'.eval x ≠ 0) :
    num.eval x / den.eval x = num'.eval x / den'.eval x := by
  rcases hrep with ⟨hden0, hr⟩
  rcases hrep' with ⟨hden0', hr'⟩
  have hdenf0 : algebraMap Poly FracPoly den ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective Poly FracPoly)).mpr hden0
  have hdenf0' : algebraMap Poly FracPoly den' ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective Poly FracPoly)).mpr hden0'
  have hEq :
      algebraMap Poly FracPoly num * algebraMap Poly FracPoly den' =
        algebraMap Poly FracPoly num' * algebraMap Poly FracPoly den := by
    have hrEq :
        algebraMap Poly FracPoly num / algebraMap Poly FracPoly den =
          algebraMap Poly FracPoly num' / algebraMap Poly FracPoly den' := by
      rw [← hr, ← hr']
    field_simp [hdenf0, hdenf0'] at hrEq
    simpa [mul_comm] using hrEq
  have hpolyEq : num * den' = num' * den := by
    apply IsFractionRing.injective Poly FracPoly
    simpa [map_mul] using hEq
  have hEval :
      num.eval x * den'.eval x = num'.eval x * den.eval x := by
    simpa [Polynomial.eval_mul] using congrArg (fun p : Poly => p.eval x) hpolyEq
  field_simp [hdenx, hdenx']
  simpa [mul_comm, mul_left_comm, mul_assoc] using hEval

/--
NNwd can be checked on any single numerator/denominator representation.

The definition quantifies over all representations of a rational function. This
lemma packages the well-definedness of evaluation at defined real points: once
`r = num / den` is fixed, it is enough to check nonnegativity at the points where
`den` does not vanish.
-/
theorem ratNonnegWhereDefined_iff_of_isFracRep
    {r : FracPoly}
    {num den : Poly}
    (hrep : IsFracRep r num den) :
    RatNonnegWhereDefined r ↔
      ∀ x : ℝ, den.eval x ≠ 0 → 0 ≤ num.eval x / den.eval x := by
  constructor
  · intro hr x hdenx
    exact hr x hrep hdenx
  · intro hnum x num' den' hrep' hdenx'
    by_cases hdenx : den.eval x = 0
    · let f : ℝ → ℝ := fun y => num'.eval y / den'.eval y
      have hcont : ContinuousAt f x :=
        num'.continuousAt_aeval.div den'.continuousAt_aeval hdenx'
      have hden'EventNhds : ∀ᶠ y in nhds x, den'.eval y ≠ 0 := by
        have hmem : den'.eval x ∈ ({0}ᶜ : Set ℝ) := by simpa using hdenx'
        exact den'.continuousAt_aeval.preimage_mem_nhds (IsOpen.mem_nhds isOpen_ne hmem)
      have hden'Event : ∀ᶠ y in nhdsWithin x ({x}ᶜ), den'.eval y ≠ 0 :=
        nhdsWithin_le_nhds hden'EventNhds
      have hdenEvent : ∀ᶠ y in nhdsWithin x ({x}ᶜ), den.eval y ≠ 0 :=
        eventually_eval_ne_zero_punctured_nhds hrep.1 x
      have hnonnegEvent : ∀ᶠ y in nhdsWithin x ({x}ᶜ), f y ∈ Set.Ici (0 : ℝ) := by
        filter_upwards [hdenEvent, hden'Event] with y hdeny hden'y
        have hEq := eval_eq_of_isFracRep hrep' hrep hden'y hdeny
        simpa [f, hEq] using hnum y hdeny
      exact IsClosed.mem_of_tendsto isClosed_Ici hcont.continuousWithinAt.tendsto hnonnegEvent
        (b := nhdsWithin x ({x}ᶜ))
    · have hEq := eval_eq_of_isFracRep hrep' hrep hdenx' hdenx
      rw [hEq]
      exact hnum x hdenx

/--
Recover NNwd from a polynomial numerator after multiplying by a square
denominator.

With `q ^ 2 * r = c`, the rational function `r` has the fixed representation
`c / q ^ 2`; the only point left is that NNwd may be checked on this one
representation.
-/
theorem ratNonnegWhereDefined_of_mul_sq_eq_nonneg
    {r : FracPoly}
    {q c : Poly}
    (hq : q ≠ 0)
    (hscaled : algebraMap Poly FracPoly (q ^ 2) * r = algebraMap Poly FracPoly c)
    (hc : ∀ x : ℝ, 0 ≤ c.eval x) :
    RatNonnegWhereDefined r := by
  refine (ratNonnegWhereDefined_iff_of_isFracRep (r := r) (num := c) (den := q ^ 2) ?_).2 ?_
  · refine ⟨pow_ne_zero 2 hq, ?_⟩
    have hqf0 : algebraMap Poly FracPoly (q ^ 2) ≠ 0 := by
      exact (map_ne_zero_iff _ (IsFractionRing.injective Poly FracPoly)).mpr
        (pow_ne_zero 2 hq)
    calc
      r = (algebraMap Poly FracPoly (q ^ 2) * r) /
          algebraMap Poly FracPoly (q ^ 2) := by
            field_simp [hqf0]
      _ = algebraMap Poly FracPoly c / algebraMap Poly FracPoly (q ^ 2) := by
            rw [hscaled]
  · intro x hq2x
    exact div_nonneg (hc x) (by simpa [Polynomial.eval_pow] using sq_nonneg (q.eval x))

theorem ratNonnegWhereDefined_mul
    {a b : FracPoly}
    (ha : RatNonnegWhereDefined a)
    (hb : RatNonnegWhereDefined b) :
    RatNonnegWhereDefined (a * b) := by
  let an : Poly := IsFractionRing.num Poly a
  let ad : Poly := ↑(IsFractionRing.den Poly a)
  let bn : Poly := IsFractionRing.num Poly b
  let bd : Poly := ↑(IsFractionRing.den Poly b)
  have harep : IsFracRep a an ad := by
    simpa [an, ad] using isFracRep_num_den a
  have hbrep : IsFracRep b bn bd := by
    simpa [bn, bd] using isFracRep_num_den b
  refine (ratNonnegWhereDefined_iff_of_isFracRep (isFracRep_mul harep hbrep)).2 ?_
  intro x hdenx
  have hadx : ad.eval x ≠ 0 := by
    intro h
    exact hdenx (by simp [Polynomial.eval_mul, h])
  have hbdx : bd.eval x ≠ 0 := by
    intro h
    exact hdenx (by simp [Polynomial.eval_mul, h])
  have haVal :
      0 ≤ an.eval x / ad.eval x :=
    (ratNonnegWhereDefined_iff_of_isFracRep harep).1 ha x hadx
  have hbVal :
      0 ≤ bn.eval x / bd.eval x :=
    (ratNonnegWhereDefined_iff_of_isFracRep hbrep).1 hb x hbdx
  have hmul := mul_nonneg haVal hbVal
  have hEq :
      (an * bn).eval x / (ad * bd).eval x =
        (an.eval x / ad.eval x) * (bn.eval x / bd.eval x) := by
    simp only [Polynomial.eval_mul]
    field_simp [hadx, hbdx]
  rwa [hEq]

end MatrixSOS
