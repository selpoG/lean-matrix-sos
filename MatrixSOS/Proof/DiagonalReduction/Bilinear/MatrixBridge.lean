/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.DiagonalReduction.StdBasis

open Matrix Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS

theorem bilinOfPolyMat_toMatrix_basis
    {m : ℕ}
    {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : PolyMat m)
    (b : Module.Basis ι Poly (V m)) :
    LinearMap.BilinForm.toMatrix b (bilinOfPolyMat P) =
      ((stdBasisV m).toMatrix b)ᵀ * P * (stdBasisV m).toMatrix b := by
  calc
    LinearMap.BilinForm.toMatrix b (bilinOfPolyMat P)
      = ((stdBasisV m).toMatrix b)ᵀ *
          LinearMap.BilinForm.toMatrix (stdBasisV m) (bilinOfPolyMat P) *
          (stdBasisV m).toMatrix b := by
            symm
            exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
              (b := stdBasisV m) (c := b) (B := bilinOfPolyMat P)
    _ = ((stdBasisV m).toMatrix b)ᵀ * P * (stdBasisV m).toMatrix b := by
      rw [show stdBasisV m = Pi.basisFun Poly (Fin m) by rfl]
      rw [LinearMap.BilinForm.toMatrix_basisFun]
      simp [toMatrix'_bilinOfPolyMat, Matrix.mul_assoc]

theorem mapEval_bilinOfPolyMat_toMatrix
    {m : ℕ}
    {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : PolyMat m)
    (b : Module.Basis ι Poly (V m))
    (x : ℝ) :
    mapEval x (LinearMap.BilinForm.toMatrix b (bilinOfPolyMat P)) =
      (mapEval x ((stdBasisV m).toMatrix b)).transpose *
        mapEval x P * mapEval x ((stdBasisV m).toMatrix b) := by
  rw [bilinOfPolyMat_toMatrix_basis]
  simp [Matrix.mul_assoc]

theorem bilinOfPolyMat_toMatrix_isSymm
    {m : ℕ}
    {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : PolyMat m)
    (hsymm : P.IsSymm)
    (b : Module.Basis ι Poly (V m)) :
    (LinearMap.BilinForm.toMatrix b (bilinOfPolyMat P)).IsSymm := by
  rw [bilinOfPolyMat_toMatrix_basis]
  rw [Matrix.IsSymm]
  simp [Matrix.transpose_mul, Matrix.mul_assoc, hsymm.eq]

theorem mapEval_bilinOfPolyMat_toMatrix_posSemidef
    {m : ℕ}
    {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : PolyMat m)
    (b : Module.Basis ι Poly (V m))
    (hP : ∀ x : ℝ, (mapEval x P).PosSemidef) :
    ∀ x : ℝ, (mapEval x (LinearMap.BilinForm.toMatrix b (bilinOfPolyMat P))).PosSemidef := by
  intro x
  rw [mapEval_bilinOfPolyMat_toMatrix P b x]
  simpa using Matrix.PosSemidef.conjTranspose_mul_mul_same (hP x)
    (mapEval x ((stdBasisV m).toMatrix b))

theorem exists_factorization_of_bilinOfPolyMat_toMatrix_eq
    {m ℓ : ℕ}
    {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : PolyMat m)
    (b : Module.Basis ι Poly (V m))
    (R : Matrix (Fin ℓ) ι Poly)
    (hR : LinearMap.BilinForm.toMatrix b (bilinOfPolyMat P) = R.transpose * R) :
    ∃ S : Matrix (Fin ℓ) (Fin m) Poly,
      P = S.transpose * S := by
  let M : Matrix (Fin m) ι Poly := (stdBasisV m).toMatrix b
  let V : Matrix ι (Fin m) Poly := b.toMatrix (stdBasisV m)
  refine ⟨R * V, ?_⟩
  have hMV : M * V = (1 : Matrix (Fin m) (Fin m) Poly) := by
    dsimp [M, V]
    exact Module.Basis.toMatrix_mul_toMatrix_flip (b := stdBasisV m) (b' := b)
  have hmat := bilinOfPolyMat_toMatrix_basis P b
  calc
    P = (1 : Matrix (Fin m) (Fin m) Poly).transpose * P * 1 := by simp
    _ = (M * V).transpose * P * (M * V) := by simp [hMV]
    _ = V.transpose * (M.transpose * P * M) * V := by
          simp [Matrix.mul_assoc]
    _ = V.transpose * (R.transpose * R) * V := by rw [← hR, hmat]
    _ = (R * V).transpose * (R * V) := by
          simp [Matrix.mul_assoc]

end MatrixSOS
