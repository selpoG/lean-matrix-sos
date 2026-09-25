/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.RationalFunction
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Invertible
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Orthogonal decompositions for bilinear diagonal reduction
-/

open Matrix Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS

theorem Matrix.toBilin'_isSymm_of_isSymm
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    {A : Matrix n n FracPoly}
    (hA : A.IsSymm) :
    (Matrix.toBilin' A).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff_basis (Pi.basisFun FracPoly n)]
  intro i j
  have hij :
      Matrix.toBilin' A ((Pi.basisFun FracPoly n) i) ((Pi.basisFun FracPoly n) j) = A i j := by
    convert Matrix.toBilin'_single A i j using 1
    simp [Pi.basisFun]
  have hji :
      Matrix.toBilin' A ((Pi.basisFun FracPoly n) j) ((Pi.basisFun FracPoly n) i) = A j i := by
    convert Matrix.toBilin'_single A j i using 1
    simp [Pi.basisFun]
  have hAij : A i j = A j i := by
    simpa [Matrix.transpose_apply] using (congrArg (fun M => M i j) hA.eq).symm
  calc
    Matrix.toBilin' A ((Pi.basisFun FracPoly n) i) ((Pi.basisFun FracPoly n) j) = A i j := hij
    _ = A j i := hAij
    _ = Matrix.toBilin' A ((Pi.basisFun FracPoly n) j) ((Pi.basisFun FracPoly n) i) := hji.symm

theorem BilinForm.toMatrix_eq_diagonal_of_iIsOrtho
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (B : LinearMap.BilinForm FracPoly (n → FracPoly))
    (b : Module.Basis n FracPoly (n → FracPoly))
    (hb : B.IsOrthoᵢ b) :
    LinearMap.BilinForm.toMatrix b B = Matrix.diagonal (fun i => B (b i) (b i)) := by
  have hb' := LinearMap.BilinForm.iIsOrtho_def.mp hb
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [LinearMap.BilinForm.toMatrix_apply]
  · simp [LinearMap.BilinForm.toMatrix_apply, hb' i j hij, hij]

theorem exists_orthogonal_basis_toBilin'_diagonal
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (A : Matrix n n FracPoly)
    (hA : A.IsSymm) :
    ∃ b : Module.Basis n FracPoly (n → FracPoly),
      LinearMap.BilinForm.toMatrix b (Matrix.toBilin' A) =
        Matrix.diagonal (fun i => Matrix.toBilin' A (b i) (b i)) := by
  let B : LinearMap.BilinForm FracPoly (n → FracPoly) := Matrix.toBilin' A
  have hB : LinearMap.IsSymm B := by
    exact (LinearMap.BilinForm.isSymm_iff).mp (Matrix.toBilin'_isSymm_of_isSymm hA)
  let : Invertible (2 : FracPoly) := inferInstance
  obtain ⟨bFin, hbFin⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B) hB
  let e : Fin (Module.finrank FracPoly (n → FracPoly)) ≃ n := by
    simpa [Module.finrank_fintype_fun_eq_card] using (Fintype.equivFin n).symm
  let b : Module.Basis n FracPoly (n → FracPoly) := bFin.reindex e
  have hb : B.IsOrthoᵢ b := by
    have hbFin' := LinearMap.BilinForm.iIsOrtho_def.mp hbFin
    intro i j hij
    have hij' : e.symm i ≠ e.symm j := by
      intro hEq
      exact hij (e.symm.injective hEq)
    simpa [b, Module.Basis.reindex] using hbFin' (e.symm i) (e.symm j) hij'
  refine ⟨b, ?_⟩
  exact BilinForm.toMatrix_eq_diagonal_of_iIsOrtho B b hb

theorem toBilin'_toMatrix_basis
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (A : Matrix n n FracPoly)
    (b : Module.Basis n FracPoly (n → FracPoly)) :
    LinearMap.BilinForm.toMatrix b (Matrix.toBilin' A) =
      ((Pi.basisFun FracPoly n).toMatrix b).transpose * A * (Pi.basisFun FracPoly n).toMatrix b := by
  calc
    LinearMap.BilinForm.toMatrix b (Matrix.toBilin' A)
        = ((Pi.basisFun FracPoly n).toMatrix b).transpose *
            LinearMap.BilinForm.toMatrix (Pi.basisFun FracPoly n) (Matrix.toBilin' A) *
            (Pi.basisFun FracPoly n).toMatrix b := by
              exact (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
                (b := Pi.basisFun FracPoly n) (c := b) (B := Matrix.toBilin' A)).symm
    _ = ((Pi.basisFun FracPoly n).toMatrix b).transpose * A * (Pi.basisFun FracPoly n).toMatrix b := by
          rw [LinearMap.BilinForm.toMatrix_basisFun]
          simp [Matrix.mul_assoc]

theorem exists_square_det_of_toBilin'_toMatrix
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (A : Matrix n n FracPoly)
    (b : Module.Basis n FracPoly (n → FracPoly))
    (hdet : ∃ r : FracPoly, A.det = r ^ 2) :
    ∃ r : FracPoly, (LinearMap.BilinForm.toMatrix b (Matrix.toBilin' A)).det = r ^ 2 := by
  rcases hdet with ⟨r, hr⟩
  refine ⟨((Pi.basisFun FracPoly n).toMatrix b).det * r, ?_⟩
  rw [toBilin'_toMatrix_basis, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hr]
  ring

theorem exists_orthogonal_basis_toBilin'_diagonal_with_det_square
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (A : Matrix n n FracPoly)
    (hA : A.IsSymm)
    (hdet : ∃ r : FracPoly, A.det = r ^ 2) :
    ∃ b : Module.Basis n FracPoly (n → FracPoly),
      ∃ d : n → FracPoly, ∃ r : FracPoly,
        LinearMap.BilinForm.toMatrix b (Matrix.toBilin' A) = Matrix.diagonal d ∧
          (Matrix.diagonal d).det = r ^ 2 := by
  rcases exists_orthogonal_basis_toBilin'_diagonal A hA with ⟨b, hb⟩
  rcases exists_square_det_of_toBilin'_toMatrix A b hdet with ⟨r, hr⟩
  refine ⟨b, fun i => Matrix.toBilin' A (b i) (b i), r, hb, ?_⟩
  simpa [hb] using hr
theorem exists_rat_factorization_of_toBilin'_toMatrix_eq
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (A : Matrix n n FracPoly)
    (b : Module.Basis n FracPoly (n → FracPoly))
    (R : Matrix n n FracPoly)
    (hR : LinearMap.BilinForm.toMatrix b (Matrix.toBilin' A) = R.transpose * R) :
    ∃ S : Matrix n n FracPoly, A = S.transpose * S := by
  let M : Matrix n n FracPoly := (Pi.basisFun FracPoly n).toMatrix b
  let V : Matrix n n FracPoly := b.toMatrix (Pi.basisFun FracPoly n)
  refine ⟨R * V, ?_⟩
  have hMV : M * V = (1 : Matrix n n FracPoly) := by
    dsimp [M, V]
    exact Module.Basis.toMatrix_mul_toMatrix_flip
      (b := Pi.basisFun FracPoly n) (b' := b)
  calc
    A = (1 : Matrix n n FracPoly).transpose * A * 1 := by simp
    _ = (M * V).transpose * A * (M * V) := by simp [hMV]
    _ = V.transpose * (M.transpose * A * M) * V := by
          simp [Matrix.mul_assoc]
    _ = V.transpose * (R.transpose * R) * V := by rw [← hR, toBilin'_toMatrix_basis]
    _ = (R * V).transpose * (R * V) := by
          simp [Matrix.mul_assoc]

end MatrixSOS
