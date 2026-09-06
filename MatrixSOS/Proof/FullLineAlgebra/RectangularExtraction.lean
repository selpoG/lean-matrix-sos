/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.PolyMatrix

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

theorem transpose_submatrix_inl_mul_submatrix_inl_eq_toBlocks₁₁
      {n o : Type*}
      [Fintype n] [Fintype o]
      {α : Type*}
      [AddCommMonoid α] [Mul α]
    (S : Matrix (n ⊕ o) (n ⊕ o) α) :
    (S.submatrix id Sum.inl).transpose * S.submatrix id Sum.inl = (S.transpose * S).toBlocks₁₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply]

theorem eq_transpose_mul_of_fromBlocks_eq_square
      {n o : Type*}
      [Fintype n] [Fintype o]
      {α : Type*}
      [AddCommMonoid α] [Mul α]
    (P : Matrix n n α)
    (D : Matrix o o α)
    (S : Matrix (n ⊕ o) (n ⊕ o) α)
    (hS : Matrix.fromBlocks P 0 0 D = S.transpose * S) :
    P = (S.submatrix id Sum.inl).transpose * S.submatrix id Sum.inl := by
  calc
    P = (Matrix.fromBlocks P 0 0 D).toBlocks₁₁ := by simp
    _ = (S.transpose * S).toBlocks₁₁ := by simp [hS]
    _ = (S.submatrix id Sum.inl).transpose * S.submatrix id Sum.inl := by
      symm
      exact transpose_submatrix_inl_mul_submatrix_inl_eq_toBlocks₁₁ S

theorem exists_rectangular_factorization_of_fromBlocks_eq_square
    {n o : Type*}
    [Fintype n] [Fintype o]
    {α : Type*}
      [AddCommMonoid α] [Mul α]
    (P : Matrix n n α)
    (D : Matrix o o α)
    (S : Matrix (n ⊕ o) (n ⊕ o) α)
    (hS : Matrix.fromBlocks P 0 0 D = S.transpose * S) :
    ∃ Q : Matrix (n ⊕ o) n α, P = Q.transpose * Q := by
  refine ⟨S.submatrix id Sum.inl, ?_⟩
  simpa using eq_transpose_mul_of_fromBlocks_eq_square P D S hS

theorem transpose_mul_reindex_rows_eq
    {r r' c : Type*}
    [Fintype r] [Fintype r'] [Finite c]
    {α : Type*}
    [Semiring α]
    (e : r ≃ r')
  (Q : Matrix r c α) :
    (Matrix.reindex e (Equiv.refl c) Q).transpose * Matrix.reindex e (Equiv.refl c) Q =
      Q.transpose * Q := by
  let _ := Fintype.ofFinite c
  rw [Matrix.transpose_reindex]
  exact
    Matrix.reindexLinearEquiv_mul α α (Equiv.refl c) e (Equiv.refl c) Q.transpose Q

def finSumUnitEquiv (m : ℕ) : Fin m ⊕ Unit ≃ Fin (m + 1) :=
  (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv

theorem exists_fin_rectangular_factorization_of_fromBlocks_eq_square
    {m : ℕ}
    (P : PolyMat m)
    (r : Poly)
    (S : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) Poly)
    (hS : Matrix.fromBlocks P 0 0 (fun _ _ => r) = S.transpose * S) :
    ∃ R : Matrix (Fin (m + 1)) (Fin m) Poly,
      P = R.transpose * R := by
  rcases
      exists_rectangular_factorization_of_fromBlocks_eq_square
        P (fun _ _ => r) S hS with
    ⟨Q, hQ⟩
  refine ⟨Matrix.reindex (finSumUnitEquiv m) (Equiv.refl _) Q, ?_⟩
  calc
    P = Q.transpose * Q := hQ
    _ = (Matrix.reindex (finSumUnitEquiv m) (Equiv.refl _) Q).transpose *
          Matrix.reindex (finSumUnitEquiv m) (Equiv.refl _) Q := by
        symm
        exact transpose_mul_reindex_rows_eq (finSumUnitEquiv m) Q

end MatrixSOS
