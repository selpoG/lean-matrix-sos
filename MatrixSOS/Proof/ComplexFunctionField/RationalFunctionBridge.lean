/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.ComplexFunctionField.PfisterForm

/-!
# Passage between complex function fields and rational functions
-/

open Matrix Polynomial
open scoped QuadraticAlgebra Matrix
noncomputable section

namespace MatrixSOS

theorem complexRatFuncStandardPfisterQuad4ClearedDenominatorsStatement_of_polyDiagonalQuad4SquareDetIsotropicStatement
    (hdiag : ComplexPolyDiagonalQuad4SquareDetIsotropicStatement) :
    ComplexRatFuncStandardPfisterQuad4ClearedDenominatorsStatement := by
  intro u v
  by_cases hu : u = 0
  · refine ⟨![0, 1, 0, 0], Or.inr <| Or.inl (by simp), ?_⟩
    have hunum : u.num = 0 := by
      exact RatFunc.num_eq_zero_iff.mpr hu
    simp [hunum]
  · by_cases hv : v = 0
    · refine ⟨![0, 0, 1, 0], Or.inr <| Or.inr <| Or.inl (by simp), ?_⟩
      have hvnum : v.num = 0 := by
        exact RatFunc.num_eq_zero_iff.mpr hv
      simp [hvnum]
    · let d : Fin 4 → Polynomial ℂ :=
        ![u.denom * v.denom, -(u.num * v.denom), -(v.num * u.denom), u.num * v.num]
      have hd0 : ∀ i, d i ≠ 0 := by
        intro i
        fin_cases i
        · simp [d, RatFunc.denom_ne_zero]
        · change -(u.num * v.denom) ≠ 0
          simpa using neg_ne_zero.mpr (mul_ne_zero (RatFunc.num_ne_zero hu) (RatFunc.denom_ne_zero v))
        · change -(v.num * u.denom) ≠ 0
          simpa using neg_ne_zero.mpr (mul_ne_zero (RatFunc.num_ne_zero hv) (RatFunc.denom_ne_zero u))
        · exact mul_ne_zero (RatFunc.num_ne_zero hu) (RatFunc.num_ne_zero hv)
      have hsqdet : IsSquare ((Matrix.diagonal d).det) := by
        refine ⟨u.num * u.denom * (v.num * v.denom), ?_⟩
        rw [Matrix.det_diagonal]
        simp [d, Fin.prod_univ_four, mul_assoc, mul_left_comm, mul_comm]
      rcases hdiag hd0 hsqdet with ⟨z, hzneq, hziso⟩
      refine ⟨z, hzneq, ?_⟩
      have hziso' :
          z 0 * d 0 * z 0 + (z 1 * d 1 * z 1 + (z 2 * d 2 * z 2 + z 3 * d 3 * z 3)) = 0 := by
        simpa [Matrix.toBilin'_apply', Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_four,
          add_assoc, mul_assoc] using hziso
      calc
        (u.denom * v.denom) * z 0 ^ 2
            - (u.num * v.denom) * z 1 ^ 2
            - (v.num * u.denom) * z 2 ^ 2
            + (u.num * v.num) * z 3 ^ 2
          =
            z 0 * d 0 * z 0 + (z 1 * d 1 * z 1 + (z 2 * d 2 * z 2 + z 3 * d 3 * z 3)) := by
              simp [d]
              ring
        _ = 0 := hziso'

theorem complexRatFuncStandardPfisterQuad4Isotropic_of_clearedDenominators
    {u v : RatFunc ℂ}
    (hpoly :
      ∃ z : Fin 4 → Polynomial ℂ,
        (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
        (u.denom * v.denom) * z 0 ^ 2
          - (u.num * v.denom) * z 1 ^ 2
          - (v.num * u.denom) * z 2 ^ 2
          + (u.num * v.num) * z 3 ^ 2 = 0) :
    ∃ z : Fin 4 → RatFunc ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal ![1, -u, -v, u * v]) z z = 0 := by
  rcases hpoly with ⟨z, hzneq, hzpoly⟩
  let w : Fin 4 → RatFunc ℂ := fun i => algebraMap (Polynomial ℂ) (RatFunc ℂ) (z i)
  refine ⟨w, ?_, ?_⟩
  · rcases hzneq with hz0 | hz1 | hz2 | hz3
    · exact Or.inl fun hw0 => hz0 <| by
        exact (IsFractionRing.injective (R := Polynomial ℂ) (K := RatFunc ℂ)) <|
          (show algebraMap (Polynomial ℂ) (RatFunc ℂ) (z 0) =
              algebraMap (Polynomial ℂ) (RatFunc ℂ) 0 from by simpa [w] using hw0)
    · exact Or.inr <| Or.inl fun hw1 => hz1 <| by
        exact (IsFractionRing.injective (R := Polynomial ℂ) (K := RatFunc ℂ)) <|
          (show algebraMap (Polynomial ℂ) (RatFunc ℂ) (z 1) =
              algebraMap (Polynomial ℂ) (RatFunc ℂ) 0 from by simpa [w] using hw1)
    · exact Or.inr <| Or.inr <| Or.inl fun hw2 => hz2 <| by
        exact (IsFractionRing.injective (R := Polynomial ℂ) (K := RatFunc ℂ)) <|
          (show algebraMap (Polynomial ℂ) (RatFunc ℂ) (z 2) =
              algebraMap (Polynomial ℂ) (RatFunc ℂ) 0 from by simpa [w] using hw2)
    · exact Or.inr <| Or.inr <| Or.inr fun hw3 => hz3 <| by
        exact (IsFractionRing.injective (R := Polynomial ℂ) (K := RatFunc ℂ)) <|
          (show algebraMap (Polynomial ℂ) (RatFunc ℂ) (z 3) =
              algebraMap (Polynomial ℂ) (RatFunc ℂ) 0 from by simpa [w] using hw3)
  · let A : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) u.num
    let B : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) u.denom
    let C : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) v.num
    let D : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) v.denom
    have hB0 : B ≠ 0 := by
      intro hB
      apply RatFunc.denom_ne_zero u
      exact (IsFractionRing.injective (R := Polynomial ℂ) (K := RatFunc ℂ)) <|
        (show algebraMap (Polynomial ℂ) (RatFunc ℂ) u.denom =
            algebraMap (Polynomial ℂ) (RatFunc ℂ) 0 from by simpa [B] using hB)
    have hD0 : D ≠ 0 := by
      intro hD
      apply RatFunc.denom_ne_zero v
      exact (IsFractionRing.injective (R := Polynomial ℂ) (K := RatFunc ℂ)) <|
        (show algebraMap (Polynomial ℂ) (RatFunc ℂ) v.denom =
            algebraMap (Polynomial ℂ) (RatFunc ℂ) 0 from by simpa [D] using hD)
    have hBD0 : B * D ≠ 0 := mul_ne_zero hB0 hD0
    have hu : u = A / B := by
      change u = algebraMap (Polynomial ℂ) (RatFunc ℂ) u.num /
          algebraMap (Polynomial ℂ) (RatFunc ℂ) u.denom
      exact (RatFunc.num_div_denom u).symm
    have hv : v = C / D := by
      change v = algebraMap (Polynomial ℂ) (RatFunc ℂ) v.num /
          algebraMap (Polynomial ℂ) (RatFunc ℂ) v.denom
      exact (RatFunc.num_div_denom v).symm
    have huB : B * u = A := by
      rw [hu]
      field_simp [hB0]
    have hvD : D * v = C := by
      rw [hv]
      field_simp [hD0]
    have hzpoly' :
        algebraMap (Polynomial ℂ) (RatFunc ℂ)
            ((u.denom * v.denom) * z 0 ^ 2
              - (u.num * v.denom) * z 1 ^ 2
              - (v.num * u.denom) * z 2 ^ 2
              + (u.num * v.num) * z 3 ^ 2) = 0 := by
      simpa using congrArg (algebraMap (Polynomial ℂ) (RatFunc ℂ)) hzpoly
    have hclear :
        B * D * Matrix.toBilin' (Matrix.diagonal ![1, -u, -v, u * v]) w w =
          algebraMap (Polynomial ℂ) (RatFunc ℂ)
            ((u.denom * v.denom) * z 0 ^ 2
              - (u.num * v.denom) * z 1 ^ 2
              - (v.num * u.denom) * z 2 ^ 2
              + (u.num * v.num) * z 3 ^ 2) := by
      calc
        B * D * Matrix.toBilin' (Matrix.diagonal ![1, -u, -v, u * v]) w w
            = B * D * w 0 ^ 2 - (B * u) * D * w 1 ^ 2 - (D * v) * B * w 2 ^ 2
                + (B * u) * (D * v) * w 3 ^ 2 := by
              simp [Matrix.toBilin'_apply', Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_four]
              ring
        _ = B * D * w 0 ^ 2 - A * D * w 1 ^ 2 - C * B * w 2 ^ 2 + A * C * w 3 ^ 2 := by
              rw [huB, hvD]
        _ = algebraMap (Polynomial ℂ) (RatFunc ℂ)
              ((u.denom * v.denom) * z 0 ^ 2
                - (u.num * v.denom) * z 1 ^ 2
                - (v.num * u.denom) * z 2 ^ 2
                + (u.num * v.num) * z 3 ^ 2) := by
              simp [A, B, C, D, w, map_add, map_sub, map_mul]
    have hmulzero :
        B * D * Matrix.toBilin' (Matrix.diagonal ![1, -u, -v, u * v]) w w = 0 := by
      rw [hclear, hzpoly']
    exact (mul_eq_zero.mp hmulzero).resolve_left hBD0

theorem complexRatFuncStandardPfisterQuad4IsotropicStatement_of_clearedDenominatorsStatement
    (hpoly : ComplexRatFuncStandardPfisterQuad4ClearedDenominatorsStatement) :
    ComplexRatFuncStandardPfisterQuad4IsotropicStatement := by
  intro u v
  exact complexRatFuncStandardPfisterQuad4Isotropic_of_clearedDenominators (hpoly (u := u) (v := v))

end MatrixSOS
