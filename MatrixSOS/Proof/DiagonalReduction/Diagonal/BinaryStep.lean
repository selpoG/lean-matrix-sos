/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.DiagonalReduction.Diagonal.SumFinTwo

/-!
# The binary step in diagonal polynomial matrix reduction
-/

open Matrix Polynomial
open scoped Matrix RatFunc

noncomputable section

namespace MatrixSOS

theorem exists_rat_factorization_of_diagonal_sum_head_of_fin_cons
    {n : ℕ}
    (c : FracPoly)
    (d : Fin n → FracPoly)
    (hD : ∃ R : Matrix (Fin (n + 1)) (Fin (n + 1)) FracPoly,
      Matrix.diagonal (Fin.cons c d) = R.transpose * R) :
    ∃ S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) FracPoly,
      Matrix.diagonal (Sum.elim (fun _ : Unit => c) d) = S.transpose * S := by
  let e : Fin (n + 1) ≃ Unit ⊕ Fin n :=
    { toFun := fun i =>
        match finSuccEquiv n i with
        | none => Sum.inl ()
        | some j => Sum.inr j
      invFun := fun i =>
        match i with
        | Sum.inl _ => 0
        | Sum.inr j => j.succ
      left_inv := by
        intro i
        cases h : finSuccEquiv n i with
        | none =>
            have hi : i = 0 := (finSuccEquiv_eq_none).mp h
            simp [hi]
        | some j =>
            have hi : i = j.succ := (finSuccEquiv_eq_some).mp h
            simp [hi]
      right_inv := by
        intro i
        cases i with
        | inl u =>
            simp
        | inr j =>
            simp [finSuccEquiv_succ] }
  have hReindex := exists_rat_factorization_of_diagonal_reindex e.symm hD
  have hfun :
      (Fin.cons c d) ∘ e.symm = Sum.elim (fun _ : Unit => c) d := by
    ext i
    cases i with
    | inl u =>
        simp [e]
    | inr j =>
        simp [e, Fin.cons]
  simpa [hfun] using hReindex

theorem exists_square_det_of_diagonal_fin_cons_cons_tail
    {n : ℕ}
    {a b : FracPoly}
    (d : Fin n → FracPoly)
    (hdet : ∃ r : FracPoly,
      (Matrix.diagonal (Fin.cons a (Fin.cons b d))).det = r ^ 2) :
    ∃ r : FracPoly, (Matrix.diagonal (Fin.cons (a * b) d)).det = r ^ 2 := by
  rcases hdet with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  simpa [Matrix.det_diagonal, Fin.prod_univ_succ, mul_assoc, mul_left_comm, mul_comm] using hr

theorem exists_rat_factorization_of_diagonal_fin_cons_cons_of_sum_head
    {n : ℕ}
    {a b : FracPoly}
    (d : Fin n → FracPoly)
    (hD : ∃ R : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) FracPoly,
      Matrix.diagonal (Sum.elim (fun i : Fin 2 => ![a, b] i) d) = R.transpose * R) :
    ∃ S : Matrix (Fin (n + 2)) (Fin (n + 2)) FracPoly,
      Matrix.diagonal (Fin.cons a (Fin.cons b d)) = S.transpose * S := by
  let e : Fin (n + 2) ≃ Fin 2 ⊕ Fin n :=
    (finCongr (Nat.add_comm n 2)).trans finSumFinEquiv.symm
  have hReindex := exists_rat_factorization_of_diagonal_reindex e hD
  have hzero : e 0 = Sum.inl 0 := by
    change finSumFinEquiv.symm (0 : Fin (2 + n)) = Sum.inl (0 : Fin 2)
    exact finSumFinEquiv_symm_apply_castAdd (n := n) (x := (0 : Fin 2))
  have hone : e 1 = Sum.inl 1 := by
    change finSumFinEquiv.symm (Fin.castAdd n (1 : Fin 2)) = Sum.inl (1 : Fin 2)
    exact finSumFinEquiv_symm_apply_castAdd (n := n) (x := (1 : Fin 2))
  have htail (j : Fin n) : e j.succ.succ = Sum.inr j := by
    change finSumFinEquiv.symm (Fin.cast (Nat.add_comm n 2) j.succ.succ) = Sum.inr j
    calc
      finSumFinEquiv.symm (Fin.cast (Nat.add_comm n 2) j.succ.succ)
          = finSumFinEquiv.symm ((j.addNat 2).cast (Nat.add_comm n 2)) := by
              rfl
      _ = finSumFinEquiv.symm (Fin.natAdd 2 j) := by
            rw [Fin.cast_addNat]
      _ = Sum.inr j := finSumFinEquiv_symm_apply_natAdd (m := 2) (x := j)
  have hfun :
      (Sum.elim (fun i : Fin 2 => ![a, b] i) d) ∘ e = Fin.cons a (Fin.cons b d) := by
    ext i
    refine Fin.cases ?_ ?_ i
    · simp [hzero]
    · intro i
      refine Fin.cases ?_ ?_ i
      · change b = Fin.cases a (Fin.cons b d) (Fin.succ (0 : Fin (n + 1)))
        rw [Fin.cases_succ]
        simp [Fin.cons]
      · intro j
        simp [Function.comp, htail, Fin.cons]
  simpa [hfun] using hReindex

theorem exists_rat_factorization_of_diagonal_fin_cons_cons_of_binaryReduction
    (hstmt : FracBinaryRepresentsOneStatement)
    {n : ℕ}
    {a b : FracPoly}
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha : RatNonnegWhereDefined a)
    (hb : RatNonnegWhereDefined b)
    (d : Fin n → FracPoly)
    (hD : ∃ R : Matrix (Fin (n + 1)) (Fin (n + 1)) FracPoly,
      Matrix.diagonal (Fin.cons (a * b) d) = R.transpose * R) :
    ∃ S : Matrix (Fin (n + 2)) (Fin (n + 2)) FracPoly,
      Matrix.diagonal (Fin.cons a (Fin.cons b d)) = S.transpose * S := by
  have hSumHead := exists_rat_factorization_of_diagonal_sum_head_of_fin_cons (a * b) d hD
  have hStep := exists_rat_factorization_of_diagonal_sumFinTwo_step hstmt ha0 hb0 ha hb d hSumHead
  exact exists_rat_factorization_of_diagonal_fin_cons_cons_of_sum_head d hStep

end MatrixSOS
