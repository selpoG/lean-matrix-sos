/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.RationalFunction
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Matrix Polynomial
open scoped Matrix RatFunc

noncomputable section

namespace MatrixSOS

theorem diagonal_sumElim_eq_fromBlocks
    {R : Type*}
    [CommSemiring R]
    {m n : Type*}
    [DecidableEq m]
    [DecidableEq n]
    (a : m → R)
    (d : n → R) :
    Matrix.diagonal (Sum.elim a d) =
      Matrix.fromBlocks (Matrix.diagonal a) 0 0 (Matrix.diagonal d) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.diagonal, Matrix.fromBlocks]

theorem exists_rat_factorization_of_diagonal_reindex
    {m n : Type*}
    [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (e : n ≃ m)
    {d : m → FracPoly}
    (hD : ∃ R : Matrix m m FracPoly, Matrix.diagonal d = R.transpose * R) :
    ∃ S : Matrix n n FracPoly,
      Matrix.diagonal (d ∘ e) = S.transpose * S := by
  rcases hD with ⟨R, hR⟩
  refine ⟨R.submatrix e e, ?_⟩
  calc
    Matrix.diagonal (d ∘ e) = (Matrix.diagonal d).submatrix e e := by
      exact (submatrix_diagonal_equiv d e).symm
    _ = (R.transpose * R).submatrix e e := by rw [hR]
    _ = (R.transpose).submatrix e e * R.submatrix e e := by
          symm
          exact submatrix_mul_equiv R.transpose R e e e
    _ = (R.submatrix e e).transpose * R.submatrix e e := by
          rw [Matrix.transpose_submatrix]

theorem exists_rat_factorization_of_diagonal_sum_one
    {m : Type*}
    [Fintype m]
    [DecidableEq m]
    (d : m → FracPoly)
    (hD : ∃ R : Matrix m m FracPoly, Matrix.diagonal d = R.transpose * R) :
    ∃ S : Matrix (Unit ⊕ m) (Unit ⊕ m) FracPoly,
      Matrix.diagonal (Sum.elim (fun _ : Unit => (1 : FracPoly)) d) = S.transpose * S := by
  rcases hD with ⟨R, hR⟩
  refine ⟨Matrix.fromBlocks (1 : Matrix Unit Unit FracPoly) 0 0 R, ?_⟩
  rw [diagonal_sumElim_eq_fromBlocks, hR]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

theorem exists_square_det_of_diagonal_reindex
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (e : n ≃ m)
    {d : m → FracPoly}
    (hdet : ∃ r : FracPoly, (Matrix.diagonal d).det = r ^ 2) :
    ∃ r : FracPoly, (Matrix.diagonal (d ∘ e)).det = r ^ 2 := by
  rcases hdet with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  calc
    (Matrix.diagonal (d ∘ e)).det = ((Matrix.diagonal d).submatrix e e).det := by
      rw [submatrix_diagonal_equiv]
    _ = (Matrix.diagonal d).det := by
          rw [Matrix.det_submatrix_equiv_self]
    _ = r ^ 2 := hr

end MatrixSOS
