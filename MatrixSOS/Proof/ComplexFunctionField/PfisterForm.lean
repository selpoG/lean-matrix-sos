/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.ComplexFunctionField.FracComplexI
import MatrixSOS.Proof.QuadraticForms

/-!
# Pfister forms over the complex function field
-/

open Matrix Polynomial
open scoped QuadraticAlgebra Matrix
noncomputable section

namespace MatrixSOS

/-- Over `FracComplexI = ℝ(X)(i)`, every diagonal `⟨c,c,d,d⟩` form with `c ≠ 0` is isotropic,
because `-cd` is automatically a sum of two squares. This packages the easy complex-side
isotropy used downstream after the hard square-determinant descent. -/
def pfister2Matrix (a b : FracPoly) : Matrix (Fin 4) (Fin 4) FracPoly :=
  Matrix.diagonal ![1, -a, -b, a * b]

/-- Bilinear form attached to `pfister2Matrix a b`. -/
def pfister2Bilin (a b : FracPoly) : LinearMap.BilinForm FracPoly (Fin 4 → FracPoly) :=
  Matrix.toBilin' (pfister2Matrix a b)

@[simp] theorem pfister2Bilin_toMatrix' (a b : FracPoly) :
    LinearMap.BilinForm.toMatrix' (pfister2Bilin a b) = pfister2Matrix a b := by
  simp [pfister2Bilin]

@[simp] theorem pfister2Bilin_apply (a b : FracPoly) (x y : Fin 4 → FracPoly) :
    pfister2Bilin a b x y =
      x 0 * y 0 - a * (x 1 * y 1) - b * (x 2 * y 2) + (a * b) * (x 3 * y 3) := by
  simp [pfister2Bilin, pfister2Matrix, Matrix.toBilin'_apply', Matrix.mulVec_diagonal,
    dotProduct, Fin.sum_univ_four]
  ring

theorem pfister2Bilin_isSymm (a b : FracPoly) :
    (pfister2Bilin a b).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [pfister2Bilin_apply, pfister2Bilin_apply]
  ring

@[simp] theorem pfister2Matrix_det (a b : FracPoly) :
    (pfister2Matrix a b).det = (a * b) ^ 2 := by
  rw [pfister2Matrix, Matrix.det_diagonal]
  simp [Fin.prod_univ_four]
  ring

theorem pfister2Bilin_nondegenerate
    {a b : FracPoly}
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    (pfister2Bilin a b).Nondegenerate := by
  refine Matrix.Nondegenerate.toBilin' ?_
  rw [Matrix.nondegenerate_iff_det_ne_zero, pfister2Matrix_det]
  exact pow_ne_zero 2 (mul_ne_zero ha0 hb0)

theorem isSquare_pfister2Bilin_det (a b : FracPoly) :
    IsSquare ((LinearMap.BilinForm.toMatrix (Pi.basisFun FracPoly (Fin 4))
      (pfister2Bilin a b)).det) := by
  refine ⟨a * b, ?_⟩
  rw [LinearMap.BilinForm.toMatrix_basisFun, pfister2Bilin_toMatrix', pfister2Matrix_det, pow_two]

/-- The value of the associated `2`-fold Pfister form `⟨1,-a,-b,ab⟩` on a vector over the
explicit quadratic extension `ℝ(X)(i)`. -/
def pfister2ValueComplexI (a b : FracPoly) (z : Fin 4 → FracComplexI) : FracComplexI :=
  z 0 ^ 2 -
    algebraMap FracPoly FracComplexI a * z 1 ^ 2 -
    algebraMap FracPoly FracComplexI b * z 2 ^ 2 +
    algebraMap FracPoly FracComplexI (a * b) * z 3 ^ 2

def fracComplexIReVec (z : Fin 4 → FracComplexI) : Fin 4 → FracPoly := fun i => (z i).re

def fracComplexIImVec (z : Fin 4 → FracComplexI) : Fin 4 → FracPoly := fun i => (z i).im

@[simp] theorem fracComplexIReVec_apply (z : Fin 4 → FracComplexI) (i : Fin 4) :
    fracComplexIReVec z i = (z i).re := rfl

@[simp] theorem fracComplexIImVec_apply (z : Fin 4 → FracComplexI) (i : Fin 4) :
    fracComplexIImVec z i = (z i).im := rfl

@[simp] theorem pfister2ValueComplexI_re
    (a b : FracPoly)
    (z : Fin 4 → FracComplexI) :
    (pfister2ValueComplexI a b z).re =
      pfister2Bilin a b (fracComplexIReVec z) (fracComplexIReVec z) -
        pfister2Bilin a b (fracComplexIImVec z) (fracComplexIImVec z) := by
  simp [pfister2ValueComplexI, pfister2Bilin_apply, fracComplexIReVec, fracComplexIImVec, pow_two]
  ring

@[simp] theorem pfister2ValueComplexI_im
    (a b : FracPoly)
    (z : Fin 4 → FracComplexI) :
    (pfister2ValueComplexI a b z).im =
      2 * pfister2Bilin a b (fracComplexIReVec z) (fracComplexIImVec z) := by
  simp [pfister2ValueComplexI, pfister2Bilin_apply, fracComplexIReVec, fracComplexIImVec, pow_two]
  ring

/-- An isotropic vector for the Pfister form over the explicit quadratic extension `ℝ(X)(i)`
either already yields a global isotropic vector over `ℝ(X)`, or its real and imaginary parts form
the orthogonal equal-norm pair needed for the `⟨c,c,d,d⟩` square-determinant descent. -/
theorem exists_ternary_isotropic_or_pfister2_pair_of_exists_pfister2ValueComplexI_zero
    {a b : FracPoly}
    (hiso : ∃ z : Fin 4 → FracComplexI,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      pfister2ValueComplexI a b z = 0) :
    (∃ x y z : FracPoly, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x ^ 2 = a * y ^ 2 + b * z ^ 2) ∨
      ∃ x y : Fin 4 → FracPoly, ∃ c : FracPoly,
        pfister2Bilin a b x y = 0 ∧
        pfister2Bilin a b x x = c ∧
        pfister2Bilin a b y y = c ∧
        c ≠ 0 := by
  rcases hiso with ⟨z, hzneq, hziso⟩
  let x : Fin 4 → FracPoly := fracComplexIReVec z
  let y : Fin 4 → FracPoly := fracComplexIImVec z
  have hxyeq : pfister2Bilin a b x x = pfister2Bilin a b y y := by
    exact sub_eq_zero.mp (by simpa [x, y] using congrArg QuadraticAlgebra.re hziso)
  have hxy : pfister2Bilin a b x y = 0 := by
    have him : 2 * pfister2Bilin a b x y = 0 := by
      simpa [x, y] using congrArg QuadraticAlgebra.im hziso
    exact (mul_eq_zero.mp him).resolve_left (by norm_num : (2 : FracPoly) ≠ 0)
  have hzFnNonzero : z ≠ 0 := by
    intro hz0
    rcases hzneq with hz0' | hz1 | hz2 | hz3
    · exact hz0' (by simpa using congrArg (fun f : Fin 4 → FracComplexI => f 0) hz0)
    · exact hz1 (by simpa using congrArg (fun f : Fin 4 → FracComplexI => f 1) hz0)
    · exact hz2 (by simpa using congrArg (fun f : Fin 4 → FracComplexI => f 2) hz0)
    · exact hz3 (by simpa using congrArg (fun f : Fin 4 → FracComplexI => f 3) hz0)
  have hxyFn : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hxyFn
    push Not at hxyFn
    apply hzFnNonzero
    funext i
    have hx0i : x i = 0 := by
      simpa using congrArg (fun f : Fin 4 → FracPoly => f i) hxyFn.1
    have hy0i : y i = 0 := by
      simpa using congrArg (fun f : Fin 4 → FracPoly => f i) hxyFn.2
    apply QuadraticAlgebra.ext
    · simpa [x] using hx0i
    · simpa [y] using hy0i
  let c : FracPoly := pfister2Bilin a b x x
  by_cases hc0 : c = 0
  · have hxx0 : pfister2Bilin a b x x = 0 := by simpa [c] using hc0
    have hyy0 : pfister2Bilin a b y y = 0 := by
      simpa [c] using hxyeq.symm.trans hc0
    rcases hxyFn with hxFn | hyFn
    · have hxneq4 : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 ∨ x 3 ≠ 0 := by
        by_contra hxzero
        push Not at hxzero
        rcases hxzero with ⟨hx0, hxrest⟩
        rcases hxrest with ⟨hx1, hxrest⟩
        rcases hxrest with ⟨hx2, hx3⟩
        apply hxFn
        ext i
        fin_cases i
        · simpa [x] using hx0
        · simpa [x] using hx1
        · simpa [x] using hx2
        · simpa [x] using hx3
      left
      have hxpf : x 0 ^ 2 - a * x 1 ^ 2 - b * x 2 ^ 2 + a * b * x 3 ^ 2 = 0 := by
        rw [pfister2Bilin_apply] at hxx0
        ring_nf at hxx0 ⊢
        exact hxx0
      have hpfx :
          ∃ x0 y0 z0 w0 : FracPoly,
            (x0 ≠ 0 ∨ y0 ≠ 0 ∨ z0 ≠ 0 ∨ w0 ≠ 0) ∧
            x0 ^ 2 - a * y0 ^ 2 - b * z0 ^ 2 + a * b * w0 ^ 2 = 0 := by
        exact ⟨x 0, x 1, x 2, x 3, hxneq4, hxpf⟩
      exact exists_ternary_isotropic_of_exists_pfister2_isotropic (K := FracPoly) hpfx
    · have hyneq4 : y 0 ≠ 0 ∨ y 1 ≠ 0 ∨ y 2 ≠ 0 ∨ y 3 ≠ 0 := by
        by_contra hyzero
        push Not at hyzero
        rcases hyzero with ⟨hy0, hyrest⟩
        rcases hyrest with ⟨hy1, hyrest⟩
        rcases hyrest with ⟨hy2, hy3⟩
        apply hyFn
        ext i
        fin_cases i
        · simpa [y] using hy0
        · simpa [y] using hy1
        · simpa [y] using hy2
        · simpa [y] using hy3
      left
      have hypf : y 0 ^ 2 - a * y 1 ^ 2 - b * y 2 ^ 2 + a * b * y 3 ^ 2 = 0 := by
        rw [pfister2Bilin_apply] at hyy0
        ring_nf at hyy0 ⊢
        exact hyy0
      have hpfy :
          ∃ x0 y0 z0 w0 : FracPoly,
            (x0 ≠ 0 ∨ y0 ≠ 0 ∨ z0 ≠ 0 ∨ w0 ≠ 0) ∧
            x0 ^ 2 - a * y0 ^ 2 - b * z0 ^ 2 + a * b * w0 ^ 2 = 0 := by
        exact ⟨y 0, y 1, y 2, y 3, hyneq4, hypf⟩
      exact exists_ternary_isotropic_of_exists_pfister2_isotropic (K := FracPoly) hpfy
  · right
    exact ⟨x, y, c, hxy, by simp [c], by simpa [c] using hxyeq.symm, hc0⟩

def FracComplexIStandardPfisterQuad4IsotropicStatement : Prop :=
  ∀ {u v : FracComplexI},
    ∃ z : Fin 4 → FracComplexI,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal ![1, -u, -v, u * v]) z z = 0

def ComplexRatFuncStandardPfisterQuad4IsotropicStatement : Prop :=
  ∀ {u v : RatFunc ℂ},
    ∃ z : Fin 4 → RatFunc ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal ![1, -u, -v, u * v]) z z = 0

/-- Polynomial cleared-denominator landing point for the literal `ℂ(X)` standard Pfister statement.
This is the first genuinely algebraic reformulation of the remaining complex-side input: after
writing `u = num(u) / denom(u)` and `v = num(v) / denom(v)`, it asks for a nontrivial polynomial
solution of the cleared quadratic equation over `ℂ[X]`. -/
def ComplexRatFuncStandardPfisterQuad4ClearedDenominatorsStatement : Prop :=
  ∀ {u v : RatFunc ℂ},
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      (u.denom * v.denom) * z 0 ^ 2
        - (u.num * v.denom) * z 1 ^ 2
        - (v.num * u.denom) * z 2 ^ 2
        + (u.num * v.num) * z 3 ^ 2 = 0

def ComplexPolyDiagonalQuad4SquareDetIsotropicStatement : Prop :=
  ∀ {d : Fin 4 → Polynomial ℂ},
    (∀ i, d i ≠ 0) →
    IsSquare ((Matrix.diagonal d).det) →
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0

/-- Smaller canonical polynomial landing point: over `ℂ[X]` it suffices to solve the diagonal
square-determinant problem for monic coefficients, since each nonzero leading coefficient is a
complex square and can be absorbed by rescaling the corresponding coordinate. -/
def ComplexPolyMonicDiagonalQuad4SquareDetIsotropicStatement : Prop :=
  ∀ {d : Fin 4 → Polynomial ℂ},
    (∀ i, (d i).Monic) →
    IsSquare ((Matrix.diagonal d).det) →
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0

/-- The remaining monic diagonal square-determinant case after all two-coordinate square
branches have been discharged. This is the genuinely `C₁`/Tsen-shaped part of the complex
polynomial diagonal landing point. -/
def ComplexPolyMonicDiagonalQuad4SquareDetNoPairSquareIsotropicStatement : Prop :=
  ∀ {d : Fin 4 → Polynomial ℂ},
    (∀ i, (d i).Monic) →
    IsSquare ((Matrix.diagonal d).det) →
    ¬ IsSquare (d 0 * d 1) →
    ¬ IsSquare (d 0 * d 2) →
    ¬ IsSquare (d 0 * d 3) →
    ¬ IsSquare (d 1 * d 2) →
    ¬ IsSquare (d 1 * d 3) →
    ¬ IsSquare (d 2 * d 3) →
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0

/-- Matrix-free form of the remaining no-pair-square diagonal case. -/
def ComplexPolyMonicQuad4ProductSquareNoPairSquareIsotropicStatement : Prop :=
  ∀ {d : Fin 4 → Polynomial ℂ},
    (∀ i, (d i).Monic) →
    IsSquare (d 0 * d 1 * d 2 * d 3) →
    ¬ IsSquare (d 0 * d 1) →
    ¬ IsSquare (d 0 * d 2) →
    ¬ IsSquare (d 0 * d 3) →
    ¬ IsSquare (d 1 * d 2) →
    ¬ IsSquare (d 1 * d 3) →
    ¬ IsSquare (d 2 * d 3) →
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0

/-- Standard product diagonal form left after absorbing the fourth coefficient by the square
witness for `d₀*d₁*d₂*d₃`. -/
def ComplexPolyMonicTripleProductQuad4IsotropicStatement : Prop :=
  ∀ {a b c : Polynomial ℂ},
    a.Monic →
    b.Monic →
    c.Monic →
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal ![a, b, c, a * b * c]) z z = 0

/-- The standard product form after all of its two-coordinate square branches are removed. -/
def ComplexPolyMonicTripleProductNoPairSquareQuad4IsotropicStatement : Prop :=
  ∀ {a b c : Polynomial ℂ},
    a.Monic →
    b.Monic →
    c.Monic →
    ¬ IsSquare (a * b) →
    ¬ IsSquare (a * c) →
    ¬ IsSquare (a * (a * b * c)) →
    ¬ IsSquare (b * c) →
    ¬ IsSquare (b * (a * b * c)) →
    ¬ IsSquare (c * (a * b * c)) →
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal ![a, b, c, a * b * c]) z z = 0

/-- The same triple-product form with only the three genuinely distinct pair-square exclusions.
The other three pairs differ from these by multiplying by a polynomial square. -/
def ComplexPolyMonicTripleProductThreeNoPairSquareQuad4IsotropicStatement : Prop :=
  ∀ {a b c : Polynomial ℂ},
    a.Monic →
    b.Monic →
    c.Monic →
    ¬ IsSquare (a * b) →
    ¬ IsSquare (a * c) →
    ¬ IsSquare (b * c) →
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal ![a, b, c, a * b * c]) z z = 0

def ComplexPolyMonicTripleProductThreeNoPairSquareQuad4BoundedIsotropicStatement : Prop :=
  ∀ {a b c : Polynomial ℂ},
    a.Monic →
    b.Monic →
    c.Monic →
    ¬ IsSquare (a * b) →
    ¬ IsSquare (a * c) →
    ¬ IsSquare (b * c) →
    ∃ z : Fin 4 → Polynomial ℂ,
      (∀ i : Fin 4, (z i).natDegree ≤ a.natDegree + b.natDegree + c.natDegree + 1) ∧
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal ![a, b, c, a * b * c]) z z = 0

end MatrixSOS
