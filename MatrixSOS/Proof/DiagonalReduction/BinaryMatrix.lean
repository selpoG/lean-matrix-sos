/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.RationalFunction
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS

def binaryReductionMatrix
    {R : Type*}
    [CommRing R]
    (a b u v : R) : Matrix (Fin 2) (Fin 2) R :=
  !![u, -(b * v); v, a * u]

theorem det_binaryReductionMatrix
    {R : Type*}
    [CommRing R]
    (a b u v : R) :
    (binaryReductionMatrix a b u v).det = a * u ^ 2 + b * v ^ 2 := by
  calc
    (binaryReductionMatrix a b u v).det
        = u * (a * u) - (-(b * v)) * v := by
            simp [binaryReductionMatrix, Matrix.det_fin_two_of]
    _ = a * u ^ 2 + b * v ^ 2 := by
          ring

theorem binaryReductionMatrix_transpose_mul_diagonal
    {R : Type*}
    [CommRing R]
    (a b u v : R) :
    (binaryReductionMatrix a b u v).transpose * !![a, 0; 0, b] * binaryReductionMatrix a b u v =
      !![a * u ^ 2 + b * v ^ 2, 0; 0, a * b * (a * u ^ 2 + b * v ^ 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryReductionMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_two] <;> ring

theorem det_binaryReductionMatrix_of_representsOne
    {R : Type*}
    [CommRing R]
    (a b u v : R)
    (h : a * u ^ 2 + b * v ^ 2 = 1) :
    (binaryReductionMatrix a b u v).det = 1 := by
  simpa [h] using det_binaryReductionMatrix a b u v

theorem binaryReductionMatrix_transpose_mul_diagonal_of_representsOne
    {R : Type*}
    [CommRing R]
    (a b u v : R)
    (h : a * u ^ 2 + b * v ^ 2 = 1) :
    (binaryReductionMatrix a b u v).transpose * !![a, 0; 0, b] * binaryReductionMatrix a b u v =
      !![1, 0; 0, a * b] := by
  simpa [h] using binaryReductionMatrix_transpose_mul_diagonal a b u v

theorem exists_binaryReductionMatrix_of_nonneg_where_defined
    (hstmt : FracBinaryRepresentsOneStatement)
    {a b : FracPoly}
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha : RatNonnegWhereDefined a)
    (hb : RatNonnegWhereDefined b) :
    ∃ M : Matrix (Fin 2) (Fin 2) FracPoly,
      M.det = 1 ∧
        M.transpose * !![a, 0; 0, b] * M = !![1, 0; 0, a * b] := by
  rcases hstmt ha0 hb0 ha hb with ⟨u, v, huv⟩
  refine ⟨binaryReductionMatrix a b u v, ?_, ?_⟩
  · exact det_binaryReductionMatrix_of_representsOne a b u v huv
  · exact binaryReductionMatrix_transpose_mul_diagonal_of_representsOne a b u v huv

theorem exists_rat_factorization_of_congr
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    {A B P : Matrix n n FracPoly}
    (hP : P.transpose * A * P = B)
    (hPdet : IsUnit P.det)
    (hB : ∃ R : Matrix n n FracPoly, B = R.transpose * R) :
    ∃ S : Matrix n n FracPoly, A = S.transpose * S := by
  let : Invertible P.det := hPdet.unit.invertible
  let : Invertible P := Matrix.invertibleOfDetInvertible P
  rcases hB with ⟨R, hR⟩
  have hleft : (P⁻¹).transpose * P.transpose = (1 : Matrix n n FracPoly) := by
    calc
      (P⁻¹).transpose * P.transpose = (P * P⁻¹).transpose := by
        rw [Matrix.transpose_mul]
      _ = ((1 : Matrix n n FracPoly)).transpose := by
        exact congrArg Matrix.transpose (Matrix.mul_inv_of_invertible P)
      _ = (1 : Matrix n n FracPoly) := by simp
  have hright : P * P⁻¹ = (1 : Matrix n n FracPoly) := by
    simp
  refine ⟨R * P⁻¹, ?_⟩
  calc
    A = (1 : Matrix n n FracPoly).transpose * A * 1 := by simp
    _ = ((P⁻¹).transpose * P.transpose) * A * (P * P⁻¹) := by
          rw [hleft, hright]
          simp
    _ = (P⁻¹).transpose * (P.transpose * A * P) * P⁻¹ := by
          simp [Matrix.mul_assoc]
    _ = (P⁻¹).transpose * B * P⁻¹ := by rw [hP]
    _ = (P⁻¹).transpose * (R.transpose * R) * P⁻¹ := by rw [hR]
    _ = (R * P⁻¹).transpose * (R * P⁻¹) := by
          simp [Matrix.mul_assoc]

theorem exists_rat_factorization_of_fromBlocks_binaryReduction
    (hstmt : FracBinaryRepresentsOneStatement)
    {m : Type*}
    [Fintype m]
    {a b : FracPoly}
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha : RatNonnegWhereDefined a)
    (hb : RatNonnegWhereDefined b)
    (D : Matrix m m FracPoly)
    (hD : ∃ R : Matrix (Fin 2 ⊕ m) (Fin 2 ⊕ m) FracPoly,
      Matrix.fromBlocks !![1, 0; 0, a * b] 0 0 D = R.transpose * R) :
    ∃ S : Matrix (Fin 2 ⊕ m) (Fin 2 ⊕ m) FracPoly,
      Matrix.fromBlocks !![a, 0; 0, b] 0 0 D = S.transpose * S := by
  classical
  rcases exists_binaryReductionMatrix_of_nonneg_where_defined hstmt ha0 hb0 ha hb with
    ⟨M, hMdet, hM⟩
  let P : Matrix (Fin 2 ⊕ m) (Fin 2 ⊕ m) FracPoly :=
    Matrix.fromBlocks M 0 0 (1 : Matrix m m FracPoly)
  have hP :
      P.transpose * Matrix.fromBlocks !![a, 0; 0, b] 0 0 D * P =
        Matrix.fromBlocks !![1, 0; 0, a * b] 0 0 D := by
    dsimp [P]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    refine (Matrix.fromBlocks_inj).2 ?_
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hM
    · simp
    · simp
    · simp
  have hPdet : IsUnit P.det := by
    dsimp [P]
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp [hMdet]
  exact exists_rat_factorization_of_congr hP hPdet hD

end MatrixSOS
