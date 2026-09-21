/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.DiagonalReduction.Bilinear.Orthogonal
import MatrixSOS.Proof.RationalFunction.NonnegWhereDefinedAlgebra
import MatrixSOS.Proof.RationalFunction.CommonDenominator
import MatrixSOS.PolyMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Diagonal data for symmetric bilinear forms
-/

open Matrix Polynomial
open scoped Matrix RatFunc

noncomputable section

namespace MatrixSOS

theorem mapEval_isSymm_of_posSemidef
    {n : Type*}
    [Finite n]
    (A : Matrix n n Poly)
    (hA : ∀ x : ℝ, (mapEval x A).PosSemidef) :
    ∀ x : ℝ, (mapEval x A).IsSymm := by
  let _ := Fintype.ofFinite n
  intro x
  simpa using (hA x).isHermitian

theorem isSymm_of_mapEval_posSemidef
    {n : Type*}
    [Finite n]
    (A : Matrix n n Poly)
    (hA : ∀ x : ℝ, (mapEval x A).PosSemidef) :
    A.IsSymm := by
  let _ := Fintype.ofFinite n
  change A.transpose = A
  apply Matrix.ext
  intro i j
  apply Polynomial.funext
  intro x
  have hx : (mapEval x A).IsSymm := mapEval_isSymm_of_posSemidef A hA x
  simpa [mapEval, Matrix.transpose_apply] using
    congrArg (fun M : Matrix n n ℝ => M i j) hx.eq

theorem mapToFrac_isSymm_of_mapEval_posSemidef
    {n : Type*}
    [Finite n]
    (A : Matrix n n Poly)
    (hA : ∀ x : ℝ, (mapEval x A).PosSemidef) :
    (mapToFrac A).IsSymm := by
  exact (isSymm_of_mapEval_posSemidef A hA).map (algebraMap Poly FracPoly)

theorem eval_nonneg_of_transpose_mul_mul_eq_diagonal
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (A B : Matrix n n Poly)
    (d : n → Poly)
    (hA : ∀ x : ℝ, (mapEval x A).PosSemidef)
    (hdiag : B.transpose * A * B = Matrix.diagonal d)
    (i : n)
    (x : ℝ) :
    0 ≤ (d i).eval x := by
  have hcongr : (mapEval x (B.transpose * A * B)).PosSemidef := by
    simpa using Matrix.PosSemidef.conjTranspose_mul_mul_same (hA x) (mapEval x B)
  have hdiag' :
      mapEval x (B.transpose * A * B) =
        Matrix.diagonal (fun j => (d j).eval x) := by
    rw [hdiag]
    ext j k
    by_cases hjk : j = k
    · subst hjk
      simp [mapEval]
    · simp [mapEval, hjk]
  have hdiagPsd : (Matrix.diagonal fun j => (d j).eval x).PosSemidef := by
    simpa [hdiag'] using hcongr
  exact (Matrix.posSemidef_diagonal_iff.mp hdiagPsd) i

theorem exists_orthogonal_basis_diagonal_data_of_real_psd_with_frac_det_square
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (A : Matrix n n Poly)
    (hA : ∀ x : ℝ, (mapEval x A).PosSemidef)
    (hdet : ∃ r : FracPoly, (mapToFrac A).det = r ^ 2) :
    ∃ b : Module.Basis n FracPoly (n → FracPoly),
      ∃ d : n → FracPoly, ∃ r : FracPoly,
        LinearMap.BilinForm.toMatrix b (Matrix.toBilin' (mapToFrac A)) = Matrix.diagonal d ∧
          (Matrix.diagonal d).det = r ^ 2 := by
  exact exists_orthogonal_basis_toBilin'_diagonal_with_det_square
    (mapToFrac A) (mapToFrac_isSymm_of_mapEval_posSemidef A hA) hdet

theorem exists_nonneg_scaled_diagonal_data_of_real_psd
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (A : Matrix n n Poly)
    (hA : ∀ x : ℝ, (mapEval x A).PosSemidef)
    (b : Module.Basis n FracPoly (n → FracPoly))
    (d : n → FracPoly)
    (hdiag : LinearMap.BilinForm.toMatrix b (Matrix.toBilin' (mapToFrac A)) = Matrix.diagonal d) :
    ∃ q : Poly, q ≠ 0 ∧ ∃ c : n → Poly,
      (∀ i, algebraMap Poly FracPoly (q ^ 2) * d i = algebraMap Poly FracPoly (c i)) ∧
        (∀ i x, 0 ≤ (c i).eval x) := by
  let M : Matrix n n FracPoly := (Pi.basisFun FracPoly n).toMatrix b
  rcases exists_poly_matrix_of_mul_common_denominator_matrix M with ⟨q, hq, B, hB⟩
  let c : n → Poly := fun i => (B.transpose * A * B) i i
  have hscaledDiag :
      mapToFrac (B.transpose * A * B) =
        Matrix.diagonal (fun i => algebraMap Poly FracPoly (q ^ 2) * d i) := by
    calc
      mapToFrac (B.transpose * A * B)
          = (mapToFrac B).transpose * mapToFrac A * mapToFrac B := by
              rw [mapToFrac_mul, mapToFrac_mul, mapToFrac_transpose]
      _ = (((algebraMap Poly FracPoly q) • M).transpose) * mapToFrac A *
            ((algebraMap Poly FracPoly q) • M) := by rw [hB]
      _ = (algebraMap Poly FracPoly q * algebraMap Poly FracPoly q) •
            (M.transpose * mapToFrac A * M) := by
            calc
              (((algebraMap Poly FracPoly q) • M).transpose) * mapToFrac A *
                  ((algebraMap Poly FracPoly q) • M)
                  = ((algebraMap Poly FracPoly q) • (M.transpose * mapToFrac A)) *
                      ((algebraMap Poly FracPoly q) • M) := by
                        simp [Matrix.transpose_smul, Matrix.mul_assoc]
              _ = (algebraMap Poly FracPoly q) •
                    ((algebraMap Poly FracPoly q) • (M.transpose * mapToFrac A * M)) := by
                      rw [Matrix.mul_smul]
                      simp [Matrix.mul_assoc]
              _ = (algebraMap Poly FracPoly q * algebraMap Poly FracPoly q) •
                    (M.transpose * mapToFrac A * M) := by
                      rw [smul_smul]
      _ = ((algebraMap Poly FracPoly q) ^ 2) • (M.transpose * mapToFrac A * M) := by
            simp [pow_two]
      _ = ((algebraMap Poly FracPoly q) ^ 2) •
            LinearMap.BilinForm.toMatrix b (Matrix.toBilin' (mapToFrac A)) := by
              rw [toBilin'_toMatrix_basis]
      _ = ((algebraMap Poly FracPoly q) ^ 2) • Matrix.diagonal d := by rw [hdiag]
      _ = Matrix.diagonal (fun i => algebraMap Poly FracPoly (q ^ 2) * d i) := by
            ext i j
            by_cases hij : i = j
            · subst hij
              simp [pow_two]
            · simp [hij]
  have hpolyDiag : B.transpose * A * B = Matrix.diagonal c := by
    apply (mapToFrac_inj).mp
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [c, mapToFrac]
    · have hzero : mapToFrac (B.transpose * A * B) i j = 0 := by
        simpa [hij] using congrArg (fun X => X i j) hscaledDiag
      simpa [c, hij, mapToFrac] using hzero
  refine ⟨q, nonZeroDivisors.ne_zero hq, c, ?_, ?_⟩
  · intro i
    simpa [c, mapToFrac] using (congrArg (fun X => X i i) hscaledDiag).symm
  · intro i x
    simpa [c] using eval_nonneg_of_transpose_mul_mul_eq_diagonal A B c hA hpolyDiag i x

theorem exists_orthogonal_basis_nonneg_diagonal_data_of_real_psd_with_frac_det_square
    {n : Type*}
    [Fintype n]
    [DecidableEq n]
    (A : Matrix n n Poly)
    (hA : ∀ x : ℝ, (mapEval x A).PosSemidef)
    (hdet : ∃ r : FracPoly, (mapToFrac A).det = r ^ 2) :
    ∃ b : Module.Basis n FracPoly (n → FracPoly),
      ∃ d : n → FracPoly, ∃ r : FracPoly,
        LinearMap.BilinForm.toMatrix b (Matrix.toBilin' (mapToFrac A)) = Matrix.diagonal d ∧
          (Matrix.diagonal d).det = r ^ 2 ∧
          (∀ i, RatNonnegWhereDefined (d i)) := by
  rcases exists_orthogonal_basis_diagonal_data_of_real_psd_with_frac_det_square A hA hdet with
    ⟨b, d, r, hdiag, hdiagdet⟩
  rcases exists_nonneg_scaled_diagonal_data_of_real_psd A hA b d hdiag with
    ⟨q, hq, c, hscaled, hnonneg⟩
  refine ⟨b, d, r, hdiag, hdiagdet, ?_⟩
  intro i
  exact ratNonnegWhereDefined_of_mul_sq_eq_nonneg hq (hscaled i) (hnonneg i)

end MatrixSOS
