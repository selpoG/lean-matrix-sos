/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.RationalFunction.Statements

/-!
# Positivity and sums of squares over rational functions
-/

open Matrix Polynomial
open scoped QuadraticAlgebra Matrix
noncomputable section

namespace MatrixSOS

theorem fracNegativeRealPointValueSquareClosedCounterexampleStatement_of_negativeRealPolyValueSquareClosedCounterexampleStatement
    (hstmt : FracNegativeRealPolyValueSquareClosedCounterexampleStatement) :
    FracNegativeRealPointValueSquareClosedCounterexampleStatement := by
  intro r x num den hrep hdenx hlt
  have hden0 : den ≠ 0 := by
    intro hzero
    exact hdenx (by simp [hzero])
  have hprodEvalNeg : (num * den).eval x < 0 := by
    have hsqPos : 0 < den.eval x ^ 2 := sq_pos_of_ne_zero hdenx
    have hmul := mul_lt_mul_of_pos_right hlt hsqPos
    have hEq :
        num.eval x / den.eval x * den.eval x ^ 2 = num.eval x * den.eval x := by
      field_simp [hdenx]
    have hprodMulNeg : num.eval x * den.eval x < 0 := by
      have hmul' : num.eval x / den.eval x * den.eval x ^ 2 < 0 := by
        simpa [pow_two] using hmul
      rwa [hEq] at hmul'
    simpa [eval_mul] using hprodMulNeg
  rcases hstmt (p := num * den) (x := x) hprodEvalNeg with
    ⟨K, hKField, hKOrder, hKStrict, hKSq, hKAlg, hnegProd⟩
  let : Field K := hKField
  let : LinearOrder K := hKOrder
  let : IsStrictOrderedRing K := hKStrict
  let : NonnegSquareClosed K := hKSq
  let : Algebra FracPoly K := hKAlg
  have hmapDen0 : algebraMap FracPoly K (algebraMap Poly FracPoly den) ≠ 0 := by
    exact map_ne_zero_iff _ (algebraMap FracPoly K).injective |>.2
      ((map_ne_zero_iff _ (IsFractionRing.injective Poly FracPoly)).2 hden0)
  have hdivNeg :
      algebraMap FracPoly K (algebraMap Poly FracPoly (num * den)) /
          (algebraMap FracPoly K (algebraMap Poly FracPoly den)) ^ 2 < 0 := by
    exact div_neg_of_neg_of_pos hnegProd (sq_pos_of_ne_zero hmapDen0)
  have hfracNeg :
      algebraMap FracPoly K (algebraMap Poly FracPoly num) /
        algebraMap FracPoly K (algebraMap Poly FracPoly den) < 0 := by
    have hEq :
        algebraMap FracPoly K (algebraMap Poly FracPoly (num * den)) /
            (algebraMap FracPoly K (algebraMap Poly FracPoly den)) ^ 2 =
          algebraMap FracPoly K (algebraMap Poly FracPoly num) /
            algebraMap FracPoly K (algebraMap Poly FracPoly den) := by
      field_simp [hmapDen0]
      simp [map_mul, mul_comm]
    rwa [hEq] at hdivNeg
  refine ⟨K, hKField, hKOrder, hKStrict, hKSq, hKAlg, ?_⟩
  rcases hrep with ⟨_, hr⟩
  rw [hr]
  simpa using hfracNeg

theorem fracStrictPosOverSquareClosedExtensionsNonnegWhereDefinedStatement_of_negativeRealPointValueSquareClosedCounterexampleStatement
    (hstmt : FracNegativeRealPointValueSquareClosedCounterexampleStatement) :
    FracStrictPosOverSquareClosedExtensionsNonnegWhereDefinedStatement := by
  intro r hpos x num den hrep hdenx
  by_contra hnonneg
  have hlt : num.eval x / den.eval x < 0 := lt_of_not_ge hnonneg
  rcases hstmt hrep hdenx hlt with ⟨K, hKField, hKOrder, hKStrict, hKSq, hKAlg, hneg⟩
  let : Field K := hKField
  let : LinearOrder K := hKOrder
  let : IsStrictOrderedRing K := hKStrict
  let : NonnegSquareClosed K := hKSq
  let : Algebra FracPoly K := hKAlg
  exact (not_lt_of_gt (hpos (K := K))) hneg

theorem fracStrictPosOverSquareClosedExtensionsNonnegWhereDefinedStatement_of_negativeRealPolyValueSquareClosedCounterexampleStatement
    (hstmt : FracNegativeRealPolyValueSquareClosedCounterexampleStatement) :
    FracStrictPosOverSquareClosedExtensionsNonnegWhereDefinedStatement := by
  exact fracStrictPosOverSquareClosedExtensionsNonnegWhereDefinedStatement_of_negativeRealPointValueSquareClosedCounterexampleStatement
    (fracNegativeRealPointValueSquareClosedCounterexampleStatement_of_negativeRealPolyValueSquareClosedCounterexampleStatement
      hstmt)

end MatrixSOS
