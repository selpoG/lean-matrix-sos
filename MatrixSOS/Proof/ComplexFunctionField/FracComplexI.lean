/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.RationalFunction
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.NumDen

/-!
# The complex unit in the fraction field extension
-/

open Matrix Polynomial
open scoped QuadraticAlgebra Matrix
noncomputable section

namespace MatrixSOS

theorem poly_sq_add_sq_eq_zero
    {p q : Poly}
    (h : p ^ 2 + q ^ 2 = 0) :
    p = 0 ∧ q = 0 := by
  have hpEval : ∀ x : ℝ, p.eval x = 0 := by
    intro x
    have hEval : p.eval x ^ 2 + q.eval x ^ 2 = 0 := by
      simpa [Polynomial.eval_add, Polynomial.eval_pow] using congrArg (fun r : Poly => r.eval x) h
    have hpq0 : p.eval x ^ 2 = 0 ∧ q.eval x ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg (sq_nonneg (p.eval x)) (sq_nonneg (q.eval x))).mp hEval
    exact sq_eq_zero_iff.mp hpq0.1
  have hqEval : ∀ x : ℝ, q.eval x = 0 := by
    intro x
    have hEval : p.eval x ^ 2 + q.eval x ^ 2 = 0 := by
      simpa [Polynomial.eval_add, Polynomial.eval_pow] using congrArg (fun r : Poly => r.eval x) h
    have hpq0 : p.eval x ^ 2 = 0 ∧ q.eval x ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg (sq_nonneg (p.eval x)) (sq_nonneg (q.eval x))).mp hEval
    exact sq_eq_zero_iff.mp hpq0.2
  exact ⟨Polynomial.zero_of_eval_zero _ hpEval, Polynomial.zero_of_eval_zero _ hqEval⟩

theorem fracPoly_sq_add_sq_eq_zero
    {r s : FracPoly}
    (h : r ^ 2 + s ^ 2 = 0) :
    r = 0 ∧ s = 0 := by
  rcases IsFractionRing.div_surjective (A := Poly) (K := FracPoly) r with ⟨nr, dr, hdr, hreprr⟩
  rcases IsFractionRing.div_surjective (A := Poly) (K := FracPoly) s with ⟨ns, ds, hds, hreprs⟩
  let q : Poly := dr * ds
  let a : Poly := nr * ds
  let b : Poly := ns * dr
  have hq : q ∈ nonZeroDivisors Poly := by
    refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
    exact mul_ne_zero (nonZeroDivisors.ne_zero hdr) (nonZeroDivisors.ne_zero hds)
  have ha : algebraMap Poly FracPoly q * r = algebraMap Poly FracPoly a := by
    have hdrf0 : algebraMap Poly FracPoly dr ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdr
    calc
      algebraMap Poly FracPoly q * r
          = algebraMap Poly FracPoly q *
              (algebraMap Poly FracPoly nr / algebraMap Poly FracPoly dr) := by
                rw [← hreprr]
      _ = algebraMap Poly FracPoly (nr * ds) := by
            simp [q, map_mul, div_eq_mul_inv]
            field_simp [hdrf0]
  have hb : algebraMap Poly FracPoly q * s = algebraMap Poly FracPoly b := by
    have hdsf0 : algebraMap Poly FracPoly ds ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hds
    calc
      algebraMap Poly FracPoly q * s
          = algebraMap Poly FracPoly q *
              (algebraMap Poly FracPoly ns / algebraMap Poly FracPoly ds) := by
                rw [← hreprs]
      _ = algebraMap Poly FracPoly (ns * dr) := by
            simp [q, map_mul, div_eq_mul_inv]
            field_simp [hdsf0]
  have hqf0 : algebraMap Poly FracPoly q ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have habMap0 : algebraMap Poly FracPoly (a ^ 2 + b ^ 2) = 0 := by
    calc
      algebraMap Poly FracPoly (a ^ 2 + b ^ 2)
          = (algebraMap Poly FracPoly q * r) ^ 2 + (algebraMap Poly FracPoly q * s) ^ 2 := by
              rw [ha, hb]
              simp [map_add, map_pow]
      _ = (algebraMap Poly FracPoly q) ^ 2 * (r ^ 2 + s ^ 2) := by ring
      _ = 0 := by simp [h]
  have hab0 : a ^ 2 + b ^ 2 = 0 := by
    apply (IsFractionRing.injective Poly FracPoly)
    simpa using habMap0
  obtain ⟨ha0, hb0⟩ := poly_sq_add_sq_eq_zero hab0
  have hr0 : r = 0 := by
    have hmul : algebraMap Poly FracPoly q * r = 0 := by simpa [ha0] using ha
    exact (mul_eq_zero.mp hmul).resolve_left hqf0
  have hs0 : s = 0 := by
    have hmul : algebraMap Poly FracPoly q * s = 0 := by simpa [hb0] using hb
    exact (mul_eq_zero.mp hmul).resolve_left hqf0
  exact ⟨hr0, hs0⟩

theorem fracPoly_sq_ne_neg_one (r : FracPoly) : r ^ 2 ≠ (-1 : FracPoly) := by
  intro hr
  have hsum : r ^ 2 + (1 : FracPoly) ^ 2 = 0 := by
    calc
      r ^ 2 + (1 : FracPoly) ^ 2 = r ^ 2 + 1 := by ring
      _ = 0 := by rw [hr]; ring
  have hone : (1 : FracPoly) = 0 := (fracPoly_sq_add_sq_eq_zero hsum).2
  exact one_ne_zero hone

/-- A concrete model of `ℝ(X)(i)` used in the rational ternary/Pfister route. Since `r^2 = -1`
has no solution in `ℝ(X)`, the quadratic algebra `FracPoly[i]` is a field. -/
abbrev FracComplexI := QuadraticAlgebra FracPoly (-1) 0

instance fracComplexIFactNoRoot : Fact (∀ r : FracPoly, r ^ 2 ≠ (-1 : FracPoly) + 0 * r) :=
  ⟨fun r => by simpa using fracPoly_sq_ne_neg_one r⟩

@[simp] theorem fracComplexI_omega_sq :
    ((ω : FracComplexI) * ω) = (-1 : FracComplexI) := by
  ext <;> simp [FracComplexI]

@[simp] theorem fracComplexI_omega_mul_sq (z : FracComplexI) :
    (ω * z) ^ 2 = -(z ^ 2) := by
  ext <;> simp [pow_two, FracComplexI]

/-- The obvious copy of `ℂ` inside `FracComplexI = ℝ(X)(i)`, obtained by sending
`a + b I` to `a + b ω`. This is the coefficient-level map needed when comparing
`FracComplexI` with complex rational functions. -/
noncomputable def complexToFracComplexI : ℂ →ₐ[ℝ] FracComplexI :=
  Complex.lift ⟨(ω : FracComplexI), by simp⟩

@[simp] theorem complexToFracComplexI_I :
    complexToFracComplexI Complex.I = (ω : FracComplexI) := by
  have hω : (ω : FracComplexI) * ω = (-1 : FracComplexI) := by simp
  change Complex.liftAux (ω : FracComplexI) hω Complex.I = (ω : FracComplexI)
  exact Complex.liftAux_apply_I (ω : FracComplexI) hω

instance : Algebra ℂ FracComplexI := RingHom.toAlgebra complexToFracComplexI.toRingHom

/-- The distinguished copy of the variable `X` inside `FracComplexI = ℝ(X)(i)`. -/
def fracComplexIX : FracComplexI :=
  algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly X)

/-- Evaluate a complex-coefficient polynomial at the transcendental element `X ∈ ℝ(X)(i)`. -/
noncomputable def complexPolyEvalInFracComplexI : Polynomial ℂ →ₐ[ℝ] FracComplexI :=
  Polynomial.aevalTower complexToFracComplexI fracComplexIX

@[simp] theorem complexPolyEvalInFracComplexI_X :
    complexPolyEvalInFracComplexI X = fracComplexIX := by
  simp [complexPolyEvalInFracComplexI, fracComplexIX]

@[simp] theorem complexPolyEvalInFracComplexI_C (z : ℂ) :
    complexPolyEvalInFracComplexI (C z) = complexToFracComplexI z := by
  simp [complexPolyEvalInFracComplexI]

/-- Evaluating a real-coefficient polynomial after mapping its coefficients into `ℂ`
agrees with the existing `ℝ[X] → FracComplexI` algebra map. -/
theorem complexPolyEvalInFracComplexI_comp_map_real :
    complexPolyEvalInFracComplexI.comp (Polynomial.mapAlgHom Complex.ofRealAm) =
      IsScalarTower.toAlgHom ℝ Poly FracComplexI := by
  apply Polynomial.algHom_ext
  simpa [fracComplexIX] using
    (IsScalarTower.algebraMap_apply Poly FracPoly FracComplexI X).symm

@[simp] theorem complexPolyEvalInFracComplexI_map_real (p : Poly) :
    complexPolyEvalInFracComplexI (Polynomial.map (algebraMap ℝ ℂ) p) =
      algebraMap Poly FracComplexI p := by
  have h := congrArg (fun f => f p) complexPolyEvalInFracComplexI_comp_map_real
  simpa [Complex.ofRealAm] using h

/-- The concrete polynomial evaluator agrees with the `ℂ`-algebra `aeval` map on
`FracComplexI = ℝ(X)(i)`. This is the comparison needed to lift complex rational functions
into the explicit quadratic extension. -/
theorem complexPolyEvalInFracComplexI_eq_aeval :
    complexPolyEvalInFracComplexI = (Polynomial.aeval fracComplexIX).restrictScalars ℝ := by
  apply Polynomial.algHom_ext'
  · apply Complex.algHom_ext
    simp [complexPolyEvalInFracComplexI_C, complexToFracComplexI_I,
      show (algebraMap ℂ FracComplexI) = complexToFracComplexI by rfl]
  · simp [complexPolyEvalInFracComplexI, fracComplexIX]

/-- The element `X ∈ ℝ(X)(i)` remains transcendental over `ℝ`. -/
theorem fracComplexIX_transcendental_real : Transcendental ℝ fracComplexIX := by
  rw [show fracComplexIX = algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly X) by rfl]
  exact (transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective FracPoly FracComplexI)).2 <|
      (transcendental_algebraMap_iff (IsFractionRing.injective Poly FracPoly)).2
        (Polynomial.transcendental_X ℝ)

/-- The same distinguished element `X` is transcendental over the embedded copy of `ℂ`. -/
theorem fracComplexIX_transcendental_complex : Transcendental ℂ fracComplexIX := by
  exact (Algebra.IsAlgebraic.transcendental_iff (R := ℝ) (S := ℂ) (a := fracComplexIX)).1
    fracComplexIX_transcendental_real

/-- Evaluating complex polynomials at `X ∈ ℝ(X)(i)` is injective. -/
theorem complexPolyEvalInFracComplexI_injective :
    Function.Injective complexPolyEvalInFracComplexI := by
  intro p q hpq
  exact (transcendental_iff_injective (R := ℂ) (A := FracComplexI) (x := fracComplexIX)).1
    fracComplexIX_transcendental_complex <| by
      simpa [complexPolyEvalInFracComplexI_eq_aeval] using hpq

/-- Evaluate a complex rational function at the explicit transcendental element
`X ∈ FracComplexI = ℝ(X)(i)`. -/
noncomputable def complexRatFuncEvalInFracComplexI : RatFunc ℂ →ₐ[ℝ] FracComplexI :=
  RatFunc.liftAlgHom complexPolyEvalInFracComplexI
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      complexPolyEvalInFracComplexI_injective)

@[simp] theorem complexRatFuncEvalInFracComplexI_algebraMap (p : Polynomial ℂ) :
    complexRatFuncEvalInFracComplexI (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
      complexPolyEvalInFracComplexI p := by
  simpa [complexRatFuncEvalInFracComplexI] using
    (RatFunc.liftAlgHom_apply_div (φ := complexPolyEvalInFracComplexI)
      (hφ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        complexPolyEvalInFracComplexI_injective) p 1)

@[simp] theorem complexRatFuncEvalInFracComplexI_X :
    complexRatFuncEvalInFracComplexI (RatFunc.X : RatFunc ℂ) = fracComplexIX := by
  rw [← RatFunc.algebraMap_X, complexRatFuncEvalInFracComplexI_algebraMap]
  simp [complexPolyEvalInFracComplexI, fracComplexIX]

/-- Map a real-coefficient polynomial into complex rational functions by sending each real
coefficient into `ℂ` and then viewing the resulting complex polynomial inside `ℂ(X)`. -/
noncomputable def realPolyToComplexRatFunc : Poly →ₐ[ℝ] RatFunc ℂ :=
  (IsScalarTower.toAlgHom ℝ (Polynomial ℂ) (RatFunc ℂ)).comp
    (Polynomial.mapAlgHom Complex.ofRealAm)

theorem realPolyToComplexRatFunc_injective :
    Function.Injective realPolyToComplexRatFunc := by
  intro p q hpq
  exact (Polynomial.map_injective (f := algebraMap ℝ ℂ)
    (FaithfulSMul.algebraMap_injective ℝ ℂ)) <| by
      simpa [realPolyToComplexRatFunc, Complex.ofRealAm] using hpq

/-- The natural embedding `ℝ(X) → ℂ(X)` obtained by extending coefficients from `ℝ` to `ℂ`. -/
noncomputable def fracPolyToComplexRatFunc : FracPoly →ₐ[ℝ] RatFunc ℂ :=
  IsFractionRing.liftAlgHom (A := Poly) (K := FracPoly) (R := ℝ) (L := RatFunc ℂ)
    (g := realPolyToComplexRatFunc) realPolyToComplexRatFunc_injective

@[simp] theorem fracPolyToComplexRatFunc_alg (p : Poly) :
    fracPolyToComplexRatFunc (algebraMap Poly FracPoly p) = realPolyToComplexRatFunc p := by
  change IsFractionRing.lift realPolyToComplexRatFunc_injective (algebraMap Poly FracPoly p) = _
  exact (IsFractionRing.lift_algebraMap (A := Poly) (K := FracPoly) (L := RatFunc ℂ)
    (g := realPolyToComplexRatFunc) realPolyToComplexRatFunc_injective p)

@[simp] theorem fracPolyToComplexRatFunc_X :
    fracPolyToComplexRatFunc (algebraMap Poly FracPoly X) = RatFunc.X := by
  rw [fracPolyToComplexRatFunc_alg]
  simp [realPolyToComplexRatFunc, RatFunc.algebraMap_X]

instance : Algebra FracPoly (RatFunc ℂ) := RingHom.toAlgebra fracPolyToComplexRatFunc.toRingHom

/-- Map the explicit quadratic extension `ℝ(X)(i)` back into complex rational functions by
sending the quadratic generator `ω` to the constant rational function `I`. -/
noncomputable def fracComplexIToComplexRatFunc : FracComplexI →ₐ[FracPoly] RatFunc ℂ := by
  refine QuadraticAlgebra.lift ?_
  refine ⟨algebraMap ℂ (RatFunc ℂ) Complex.I, ?_⟩
  have hminus :
      algebraMap FracPoly (RatFunc ℂ) (-1 : FracPoly) = algebraMap ℂ (RatFunc ℂ) (-1 : ℂ) := by
    rw [show (-1 : FracPoly) = algebraMap Poly FracPoly (C (-1 : ℝ)) by simp]
    change fracPolyToComplexRatFunc (algebraMap Poly FracPoly (C (-1 : ℝ))) =
      algebraMap ℂ (RatFunc ℂ) (-1 : ℂ)
    rw [fracPolyToComplexRatFunc_alg]
    simp [realPolyToComplexRatFunc]
  calc
    (algebraMap ℂ (RatFunc ℂ) Complex.I : RatFunc ℂ) * algebraMap ℂ (RatFunc ℂ) Complex.I
        = algebraMap ℂ (RatFunc ℂ) (-1 : ℂ) := by
            rw [← map_mul]
            norm_num
    _ = algebraMap FracPoly (RatFunc ℂ) (-1 : FracPoly) := hminus.symm
    _ = (-1 : FracPoly) • (1 : RatFunc ℂ) + (0 : FracPoly) • algebraMap ℂ (RatFunc ℂ) Complex.I := by
          simp

@[simp] theorem fracComplexIToComplexRatFunc_omega :
    fracComplexIToComplexRatFunc (ω : FracComplexI) = algebraMap ℂ (RatFunc ℂ) Complex.I := by
  simp [fracComplexIToComplexRatFunc]

@[simp] theorem fracComplexIToComplexRatFunc_alg (r : FracPoly) :
    fracComplexIToComplexRatFunc (algebraMap FracPoly FracComplexI r) = fracPolyToComplexRatFunc r := by
  have h : algebraMap FracPoly (RatFunc ℂ) r = fracPolyToComplexRatFunc r := rfl
  simpa [fracComplexIToComplexRatFunc] using h

@[simp] theorem fracComplexIToComplexRatFunc_fracComplexIX :
    fracComplexIToComplexRatFunc fracComplexIX = RatFunc.X := by
  have hX : fracPolyToComplexRatFunc (algebraMap Poly FracPoly X) = RatFunc.X := by
    rw [fracPolyToComplexRatFunc_alg]
    simp [realPolyToComplexRatFunc, RatFunc.algebraMap_X]
  rw [show fracComplexIX =
    algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly X) by rfl]
  rw [fracComplexIToComplexRatFunc_alg]
  exact hX

@[simp] theorem complexRatFuncEvalInFracComplexI_fracPolyToComplexRatFunc (r : FracPoly) :
    complexRatFuncEvalInFracComplexI (fracPolyToComplexRatFunc r) = algebraMap FracPoly FracComplexI r := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := Poly) r
  rw [map_div₀, map_div₀]
  have hx :
      complexRatFuncEvalInFracComplexI (realPolyToComplexRatFunc x) =
        algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly x) := by
    calc
      complexRatFuncEvalInFracComplexI (realPolyToComplexRatFunc x)
          = complexRatFuncEvalInFracComplexI
              (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.map (algebraMap ℝ ℂ) x)) := by
                rfl
      _ = complexPolyEvalInFracComplexI (Polynomial.map (algebraMap ℝ ℂ) x) := by
            rw [complexRatFuncEvalInFracComplexI_algebraMap]
      _ = algebraMap Poly FracComplexI x := complexPolyEvalInFracComplexI_map_real x
      _ = algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly x) := by
            rfl
  have hy' :
      complexRatFuncEvalInFracComplexI (realPolyToComplexRatFunc y) =
        algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly y) := by
    calc
      complexRatFuncEvalInFracComplexI (realPolyToComplexRatFunc y)
          = complexRatFuncEvalInFracComplexI
              (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.map (algebraMap ℝ ℂ) y)) := by
                rfl
      _ = complexPolyEvalInFracComplexI (Polynomial.map (algebraMap ℝ ℂ) y) := by
            rw [complexRatFuncEvalInFracComplexI_algebraMap]
      _ = algebraMap Poly FracComplexI y := complexPolyEvalInFracComplexI_map_real y
      _ = algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly y) := by
            rfl
  rw [fracPolyToComplexRatFunc_alg, fracPolyToComplexRatFunc_alg]
  rw [hx, hy']
  rw [map_div₀]

@[simp] theorem complexRatFuncEvalInFracComplexI_fracComplexIToComplexRatFunc_omega :
    complexRatFuncEvalInFracComplexI (fracComplexIToComplexRatFunc ω) = (ω : FracComplexI) := by
  rw [fracComplexIToComplexRatFunc_omega]
  change complexRatFuncEvalInFracComplexI (algebraMap (Polynomial ℂ) (RatFunc ℂ) (C Complex.I)) = ω
  rw [complexRatFuncEvalInFracComplexI_algebraMap]
  simp [complexToFracComplexI_I]

@[simp] theorem complexRatFuncEvalInFracComplexI_fracComplexIToComplexRatFunc_fracComplexIX :
    complexRatFuncEvalInFracComplexI (fracComplexIToComplexRatFunc fracComplexIX) = fracComplexIX := by
  simp [fracComplexIToComplexRatFunc_fracComplexIX, complexRatFuncEvalInFracComplexI_X]

theorem complexRatFuncEvalInFracComplexI_fracComplexIToComplexRatFunc
    (z : FracComplexI) :
    complexRatFuncEvalInFracComplexI (fracComplexIToComplexRatFunc z) = z := by
  rcases z with ⟨x, y⟩
  have hrepr :
      fracComplexIToComplexRatFunc (⟨x, y⟩ : FracComplexI) =
        algebraMap FracPoly (RatFunc ℂ) x +
          algebraMap FracPoly (RatFunc ℂ) y * algebraMap ℂ (RatFunc ℂ) Complex.I := by
    simp [fracComplexIToComplexRatFunc, Algebra.smul_def]
  have hx0 :
      complexRatFuncEvalInFracComplexI (algebraMap FracPoly (RatFunc ℂ) x) =
        algebraMap FracPoly FracComplexI x := by
    exact complexRatFuncEvalInFracComplexI_fracPolyToComplexRatFunc x
  have hy0 :
      complexRatFuncEvalInFracComplexI (algebraMap FracPoly (RatFunc ℂ) y) =
        algebraMap FracPoly FracComplexI y := by
    exact complexRatFuncEvalInFracComplexI_fracPolyToComplexRatFunc y
  have hI :
      complexRatFuncEvalInFracComplexI (algebraMap ℂ (RatFunc ℂ) Complex.I) = (ω : FracComplexI) := by
    change complexRatFuncEvalInFracComplexI (algebraMap (Polynomial ℂ) (RatFunc ℂ) (C Complex.I)) = ω
    rw [complexRatFuncEvalInFracComplexI_algebraMap]
    simp [complexToFracComplexI_I]
  rw [hrepr, map_add, map_mul, hx0, hy0, hI]
  ext <;> simp [FracComplexI]

@[simp] theorem fracComplexIToComplexRatFunc_complexToFracComplexI (z : ℂ) :
    fracComplexIToComplexRatFunc (complexToFracComplexI z) = algebraMap ℂ (RatFunc ℂ) z := by
  have hre :
      algebraMap ℝ FracComplexI z.re =
        algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly (C z.re)) := by
    calc
      algebraMap ℝ FracComplexI z.re = algebraMap Poly FracComplexI (algebraMap ℝ Poly z.re) := by
        simpa using (IsScalarTower.algebraMap_apply ℝ Poly FracComplexI z.re)
      _ = algebraMap Poly FracComplexI (C z.re) := by
        rfl
      _ = algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly (C z.re)) := by
        rfl
  have him :
      z.im • (ω : FracComplexI) =
        algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly (C z.im)) * ω := by
    calc
      z.im • (ω : FracComplexI) = algebraMap ℝ FracComplexI z.im * ω := by
        simp [Algebra.smul_def]
      _ = algebraMap Poly FracComplexI (algebraMap ℝ Poly z.im) * ω := by
        rw [IsScalarTower.algebraMap_apply ℝ Poly FracComplexI]
      _ = algebraMap Poly FracComplexI (C z.im) * ω := by
        rfl
      _ = algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly (C z.im)) * ω := by
        rfl
  have hz :
      algebraMap ℂ (RatFunc ℂ) z =
        algebraMap ℂ (RatFunc ℂ) ((z.re : ℂ) + z.im * Complex.I) := by
    rw [Complex.re_add_im z]
  change fracComplexIToComplexRatFunc (algebraMap ℝ FracComplexI z.re + z.im • (ω : FracComplexI)) =
    algebraMap ℂ (RatFunc ℂ) z
  rw [hz, hre, him, map_add, map_mul, map_add, map_mul,
    fracComplexIToComplexRatFunc_alg, fracComplexIToComplexRatFunc_alg,
    fracComplexIToComplexRatFunc_omega]
  simp [realPolyToComplexRatFunc]

theorem fracComplexIToComplexRatFunc_complexPolyEvalInFracComplexI (p : Polynomial ℂ) :
    fracComplexIToComplexRatFunc (complexPolyEvalInFracComplexI p) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) p := by
  have hp :
      complexPolyEvalInFracComplexI p = ((Polynomial.aeval fracComplexIX).restrictScalars ℝ) p := by
    exact congrArg (fun f : Polynomial ℂ →ₐ[ℝ] FracComplexI => f p) complexPolyEvalInFracComplexI_eq_aeval
  have hcomp :
      (algebraMap ℂ (RatFunc ℂ)).comp (RingHom.id ℂ) =
        fracComplexIToComplexRatFunc.toRingHom.comp (algebraMap ℂ FracComplexI) := by
    ext z
    change algebraMap ℂ (RatFunc ℂ) z = fracComplexIToComplexRatFunc (complexToFracComplexI z)
    exact (fracComplexIToComplexRatFunc_complexToFracComplexI z).symm
  calc
    fracComplexIToComplexRatFunc (complexPolyEvalInFracComplexI p)
        = fracComplexIToComplexRatFunc (((Polynomial.aeval fracComplexIX).restrictScalars ℝ) p) := by
            rw [hp]
    _ = fracComplexIToComplexRatFunc (aeval fracComplexIX p) := by
          rfl
    _ = aeval (fracComplexIToComplexRatFunc fracComplexIX) (p.map (RingHom.id ℂ)) := by
          simpa using Polynomial.map_aeval_eq_aeval_map hcomp p fracComplexIX
    _ = algebraMap (Polynomial ℂ) (RatFunc ℂ) p := by
          simp [fracComplexIToComplexRatFunc_fracComplexIX]

theorem fracComplexIToComplexRatFunc_complexRatFuncEvalInFracComplexI (r : RatFunc ℂ) :
    fracComplexIToComplexRatFunc (complexRatFuncEvalInFracComplexI r) = r := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial ℂ) r
  rw [map_div₀, map_div₀]
  rw [complexRatFuncEvalInFracComplexI_algebraMap, complexRatFuncEvalInFracComplexI_algebraMap]
  rw [fracComplexIToComplexRatFunc_complexPolyEvalInFracComplexI,
    fracComplexIToComplexRatFunc_complexPolyEvalInFracComplexI]

/-- The explicit quadratic extension `FracComplexI = ℝ(X)(i)` is concretely isomorphic to the
complex rational function field `ℂ(X)`. -/
noncomputable def fracComplexIEquivComplexRatFunc : FracComplexI ≃+* RatFunc ℂ :=
  { fracComplexIToComplexRatFunc.toRingHom with
    toFun := fracComplexIToComplexRatFunc
    invFun := complexRatFuncEvalInFracComplexI
    left_inv := complexRatFuncEvalInFracComplexI_fracComplexIToComplexRatFunc
    right_inv := fracComplexIToComplexRatFunc_complexRatFuncEvalInFracComplexI }

/-- `FracComplexI = ℝ(X)(i)` and `ℂ(X)` agree as `ℝ`-algebras. -/
noncomputable def fracComplexIAlgEquivComplexRatFunc : FracComplexI ≃ₐ[ℝ] RatFunc ℂ :=
  { fracComplexIEquivComplexRatFunc with
    commutes' := by
      intro r
      have hr :
          algebraMap ℝ FracComplexI r =
            algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly (C r)) := by
        calc
          algebraMap ℝ FracComplexI r = algebraMap Poly FracComplexI (C r) := by
            calc
              algebraMap ℝ FracComplexI r = algebraMap Poly FracComplexI (algebraMap ℝ Poly r) := by
                simpa using (IsScalarTower.algebraMap_apply ℝ Poly FracComplexI r)
              _ = algebraMap Poly FracComplexI (C r) := by
                rfl
          _ = algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly (C r)) := by
            rfl
      rw [hr]
      change fracComplexIToComplexRatFunc
          (algebraMap FracPoly FracComplexI (algebraMap Poly FracPoly (C r))) =
        algebraMap ℝ (RatFunc ℂ) r
      rw [fracComplexIToComplexRatFunc_alg, fracPolyToComplexRatFunc_alg]
      have hC : RatFunc.C (r : ℂ) = algebraMap ℝ (RatFunc ℂ) r := rfl
      simpa [realPolyToComplexRatFunc] using hC }

end MatrixSOS
