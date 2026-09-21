/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.DiagonalReduction.Diagonal.BinaryStep

/-!
# Recursive diagonal reduction of polynomial matrices
-/

open Matrix Polynomial
open scoped Matrix RatFunc

noncomputable section

namespace MatrixSOS

theorem exists_rat_factorization_of_nonneg_diagonal_fin_of_square_det_of_forall_ne_zero
    (hstmt : FracBinaryRepresentsOneStatement)
    (hmul : ∀ {a b : FracPoly},
      RatNonnegWhereDefined a →
      RatNonnegWhereDefined b →
      RatNonnegWhereDefined (a * b)) :
    ∀ {n : ℕ} (d : Fin n → FracPoly),
      (∀ i, RatNonnegWhereDefined (d i)) →
      (∀ i, d i ≠ 0) →
      (∃ r : FracPoly, (Matrix.diagonal d).det = r ^ 2) →
      ∃ R : Matrix (Fin n) (Fin n) FracPoly, Matrix.diagonal d = R.transpose * R
  | 0, d, hnonneg, hne, hdet => by
      refine ⟨0, ?_⟩
      ext i
      exact Fin.elim0 i
  | 1, d, hnonneg, hne, hdet => by
      rcases hdet with ⟨r, hr⟩
      have h0 : d 0 = r ^ 2 := by
        simpa [Matrix.det_diagonal] using hr
      let R : Matrix (Fin 1) (Fin 1) FracPoly := Matrix.diagonal (fun _ => r)
      refine ⟨R, ?_⟩
      ext i j
      fin_cases i
      fin_cases j
      simp [R, Matrix.diagonal, Matrix.mul_apply, h0, pow_two]
  | n + 2, d, hnonneg, hne, hdet => by
      let a : FracPoly := d 0
      let b : FracPoly := d 1
      let tail : Fin n → FracPoly := fun i => d i.succ.succ
      let d' : Fin (n + 1) → FracPoly := Fin.cons (a * b) tail
      have hd :
          d = Fin.cons a (Fin.cons b tail) := by
        ext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro i
          refine Fin.cases ?_ ?_ i
          · rfl
          · intro j
            rfl
      have ha : RatNonnegWhereDefined a := by
        simpa [a] using hnonneg 0
      have hb : RatNonnegWhereDefined b := by
        simpa [b] using hnonneg 1
      have ha0 : a ≠ 0 := by
        simpa [a] using hne 0
      have hb0 : b ≠ 0 := by
        simpa [b] using hne 1
      have hnonnegTail :
          ∀ i, RatNonnegWhereDefined (d' i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact hmul ha hb
        · intro j
          change RatNonnegWhereDefined (d j.succ.succ)
          exact hnonneg j.succ.succ
      have hneTail :
          ∀ i, d' i ≠ 0 := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact mul_ne_zero ha0 hb0
        · intro j
          change d j.succ.succ ≠ 0
          exact hne j.succ.succ
      have hdetHead :
          ∃ r : FracPoly,
            (Matrix.diagonal (Fin.cons a (Fin.cons b tail))).det = r ^ 2 := by
        simpa [hd] using hdet
      have hdetTail :
          ∃ r : FracPoly, (Matrix.diagonal d').det = r ^ 2 := by
        exact exists_square_det_of_diagonal_fin_cons_cons_tail tail hdetHead
      have hTail :
          ∃ R : Matrix (Fin (n + 1)) (Fin (n + 1)) FracPoly,
            Matrix.diagonal d' = R.transpose * R :=
        exists_rat_factorization_of_nonneg_diagonal_fin_of_square_det_of_forall_ne_zero
          hstmt hmul d' hnonnegTail hneTail hdetTail
      have hHead :
          ∃ S : Matrix (Fin (n + 2)) (Fin (n + 2)) FracPoly,
            Matrix.diagonal (Fin.cons a (Fin.cons b tail)) = S.transpose * S := by
        exact exists_rat_factorization_of_diagonal_fin_cons_cons_of_binaryReduction
          hstmt ha0 hb0 ha hb tail hTail
      simpa [hd] using hHead

theorem exists_rat_factorization_of_nonneg_diagonal_with_square_det_of_forall_ne_zero
    (hstmt : FracBinaryRepresentsOneStatement)
    (hmul : ∀ {a b : FracPoly},
      RatNonnegWhereDefined a →
      RatNonnegWhereDefined b →
      RatNonnegWhereDefined (a * b))
    {n : Type*}
    [Fintype n] [DecidableEq n]
    (d : n → FracPoly)
    (hnonneg : ∀ i, RatNonnegWhereDefined (d i))
    (hne : ∀ i, d i ≠ 0)
    (hdet : ∃ r : FracPoly, (Matrix.diagonal d).det = r ^ 2) :
    ∃ R : Matrix n n FracPoly, Matrix.diagonal d = R.transpose * R := by
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  have hnonnegFin : ∀ i, RatNonnegWhereDefined ((d ∘ e.symm) i) := by
    intro i
    exact hnonneg (e.symm i)
  have hneFin : ∀ i, (d ∘ e.symm) i ≠ 0 := by
    intro i
    exact hne (e.symm i)
  have hdetFin :
      ∃ r : FracPoly, (Matrix.diagonal (d ∘ e.symm)).det = r ^ 2 := by
    exact exists_square_det_of_diagonal_reindex e.symm hdet
  have hFin :
      ∃ R : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) FracPoly,
        Matrix.diagonal (d ∘ e.symm) = R.transpose * R :=
    exists_rat_factorization_of_nonneg_diagonal_fin_of_square_det_of_forall_ne_zero
      hstmt hmul (d ∘ e.symm) hnonnegFin hneFin hdetFin
  have hefun : ((d ∘ e.symm) ∘ e) = d := by
    ext i
    simp [e]
  simpa [hefun] using exists_rat_factorization_of_diagonal_reindex e hFin

end MatrixSOS
