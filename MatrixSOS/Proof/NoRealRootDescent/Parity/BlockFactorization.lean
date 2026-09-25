/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.NoRealRootDescent.Divisibility
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Block factorizations for parity descent
-/

open Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS

theorem exists_sqAddSqBlock_factor_of_linearCombinations_dvd
    {κ : Type*}
    {p a b : Poly}
    (hp0 : p ≠ 0)
    (hp : p = a ^ 2 + b ^ 2)
    (Y : Matrix (Unit ⊕ Unit) κ Poly)
    (h1 : ∀ j, p ∣ a * Y (Sum.inl ()) j - b * Y (Sum.inr ()) j)
    (h2 : ∀ j, p ∣ b * Y (Sum.inl ()) j + a * Y (Sum.inr ()) j) :
    ∃ M : Matrix (Unit ⊕ Unit) κ Poly,
      Y =
        Matrix.fromBlocks
          (fun _ _ : Unit => a)
          (fun _ _ : Unit => b)
          (fun _ _ : Unit => -b)
          (fun _ _ : Unit => a) * M := by
  classical
  let m1 : κ → Poly := fun j => Classical.choose (h1 j)
  let m2 : κ → Poly := fun j => Classical.choose (h2 j)
  let M : Matrix (Unit ⊕ Unit) κ Poly := fun i j =>
    match i with
    | Sum.inl _ => m1 j
    | Sum.inr _ => m2 j
  refine ⟨M, ?_⟩
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
      have hm1 : a * Y (Sum.inl ()) j - b * Y (Sum.inr ()) j = p * m1 j :=
        Classical.choose_spec (h1 j)
      have hm2 : b * Y (Sum.inl ()) j + a * Y (Sum.inr ()) j = p * m2 j :=
        Classical.choose_spec (h2 j)
      have hmulEq :
          ((Matrix.fromBlocks
              (fun _ _ : Unit => a)
              (fun _ _ : Unit => b)
              (fun _ _ : Unit => -b)
              (fun _ _ : Unit => a) * M) (Sum.inl i) j) * p =
            Y (Sum.inl i) j * p := by
        calc
          ((Matrix.fromBlocks
              (fun _ _ : Unit => a)
              (fun _ _ : Unit => b)
              (fun _ _ : Unit => -b)
              (fun _ _ : Unit => a) * M) (Sum.inl i) j) * p
              = (a * M (Sum.inl i) j + b * M (Sum.inr ()) j) * p := by
                have hentry :
                    ((Matrix.fromBlocks
                        (fun _ _ : Unit => a)
                        (fun _ _ : Unit => b)
                        (fun _ _ : Unit => -b)
                        (fun _ _ : Unit => a) * M) (Sum.inl i) j) =
                        a * M (Sum.inl i) j + b * M (Sum.inr ()) j := by
                    rw [Matrix.mul_apply]
                    cases i
                    simp [M, Matrix.fromBlocks]
                rw [hentry]
          _ = a * (p * m1 j) + b * (p * m2 j) := by
                simp [M]
                ring
          _ = a * (a * Y (Sum.inl ()) j - b * Y (Sum.inr ()) j) +
                b * (b * Y (Sum.inl ()) j + a * Y (Sum.inr ()) j) := by
                  rw [hm1, hm2]
          _ = Y (Sum.inl i) j * p := by
                rw [hp]
                ring_nf
      exact (mul_right_cancel₀ hp0 hmulEq).symm
  | inr i =>
      have hm1 : a * Y (Sum.inl ()) j - b * Y (Sum.inr ()) j = p * m1 j :=
        Classical.choose_spec (h1 j)
      have hm2 : b * Y (Sum.inl ()) j + a * Y (Sum.inr ()) j = p * m2 j :=
        Classical.choose_spec (h2 j)
      have hmulEq :
          ((Matrix.fromBlocks
              (fun _ _ : Unit => a)
              (fun _ _ : Unit => b)
              (fun _ _ : Unit => -b)
              (fun _ _ : Unit => a) * M) (Sum.inr i) j) * p =
            Y (Sum.inr i) j * p := by
        calc
          ((Matrix.fromBlocks
              (fun _ _ : Unit => a)
              (fun _ _ : Unit => b)
              (fun _ _ : Unit => -b)
              (fun _ _ : Unit => a) * M) (Sum.inr i) j) * p
              = (-b * M (Sum.inl ()) j + a * M (Sum.inr i) j) * p := by
                have hentry :
                    ((Matrix.fromBlocks
                        (fun _ _ : Unit => a)
                        (fun _ _ : Unit => b)
                        (fun _ _ : Unit => -b)
                        (fun _ _ : Unit => a) * M) (Sum.inr i) j) =
                        -b * M (Sum.inl ()) j + a * M (Sum.inr i) j := by
                    rw [Matrix.mul_apply]
                    cases i
                    simp [M, Matrix.fromBlocks]
                rw [hentry]
          _ = -b * (p * m1 j) + a * (p * m2 j) := by
                simp [M]
                ring
          _ = -b * (a * Y (Sum.inl ()) j - b * Y (Sum.inr ()) j) +
                a * (b * Y (Sum.inl ()) j + a * Y (Sum.inr ()) j) := by
                  rw [hm1, hm2]
          _ = Y (Sum.inr i) j * p := by
                rw [hp]
                ring_nf
      exact (mul_right_cancel₀ hp0 hmulEq).symm

theorem exists_sqAddSqBlockDiagonal_factor_of_linearCombinations_dvd
    {o κ : Type*}
    [Fintype o]
    [DecidableEq o]
    {p a b : Poly}
    (hp0 : p ≠ 0)
    (hp : p = a ^ 2 + b ^ 2)
    (Y : Matrix ((Unit ⊕ Unit) × o) κ Poly)
    (h1 : ∀ t j, p ∣ a * Y (Sum.inl (), t) j - b * Y (Sum.inr (), t) j)
    (h2 : ∀ t j, p ∣ b * Y (Sum.inl (), t) j + a * Y (Sum.inr (), t) j) :
    ∃ M : Matrix ((Unit ⊕ Unit) × o) κ Poly,
      Y =
        Matrix.blockDiagonal
          (fun _ : o =>
            Matrix.fromBlocks
              (fun _ _ : Unit => a)
              (fun _ _ : Unit => b)
              (fun _ _ : Unit => -b)
              (fun _ _ : Unit => a)) * M := by
  classical
  let S : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) Poly :=
    Matrix.fromBlocks
      (fun _ _ : Unit => a)
      (fun _ _ : Unit => b)
      (fun _ _ : Unit => -b)
      (fun _ _ : Unit => a)
  have hpair :
      ∀ t : o, ∃ Mt : Matrix (Unit ⊕ Unit) κ Poly,
        (fun i j => Y (i, t) j) = S * Mt := by
    intro t
    exact exists_sqAddSqBlock_factor_of_linearCombinations_dvd hp0 hp
      (fun i j => Y (i, t) j) (h1 t) (h2 t)
  choose Mblock hMblock using hpair
  let M : Matrix ((Unit ⊕ Unit) × o) κ Poly := fun ik j => Mblock ik.2 ik.1 j
  refine ⟨M, ?_⟩
  ext ik j k
  rcases ik with ⟨i, t⟩
  have hrow :
      (Matrix.blockDiagonal (fun _ : o => S) * M) (i, t) j = (S * Mblock t) i j := by
    calc
      (Matrix.blockDiagonal (fun _ : o => S) * M) (i, t) j
          = ∑ x : (Unit ⊕ Unit) × o, Matrix.blockDiagonal (fun _ : o => S) (i, t) x * M x j := by
              rw [Matrix.mul_apply]
      _ = ∑ x : Unit ⊕ Unit, S i x * M (x, t) j := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [Finset.sum_eq_single t]
            · rw [Matrix.blockDiagonal_apply_eq]
            · intro t' _ ht'
              have hne : t ≠ t' := by
                simpa [eq_comm] using ht'
              rw [Matrix.blockDiagonal_apply_ne (M := fun _ : o => S) (i := i) (j := x) hne]
              simp
            · intro ht
              exact (ht (Finset.mem_univ t)).elim
      _ = ∑ x : Unit ⊕ Unit, S i x * Mblock t x j := by
            simp [M]
      _ = (S * Mblock t) i j := by
            simp [Matrix.mul_apply]
  have hpairEq : (fun i' j' => Y (i', t) j') = S * Mblock t := hMblock t
  have hij : Y (i, t) j = (S * Mblock t) i j := by
    simpa using congrArg (fun N : Matrix (Unit ⊕ Unit) κ Poly => N i j) hpairEq
  exact congrArg (fun f : Poly => f.coeff k) (hij.trans hrow.symm)

theorem exists_sqAddSqOddUnitBlockDiagonal_factor_of_linearCombinations_dvd
    {o κ : Type*}
    [Fintype o]
    [DecidableEq o]
    {p a b : Poly}
    (hp0 : p ≠ 0)
    (hp : p = a ^ 2 + b ^ 2)
    (Y : Matrix (((Unit ⊕ Unit) × o) ⊕ Unit) κ Poly)
    (h1 : ∀ t j, p ∣ a * Y (Sum.inl (Sum.inl (), t)) j - b * Y (Sum.inl (Sum.inr (), t)) j)
    (h2 : ∀ t j, p ∣ b * Y (Sum.inl (Sum.inl (), t)) j + a * Y (Sum.inl (Sum.inr (), t)) j)
    (hbot : ∀ j, p ∣ Y (Sum.inr ()) j) :
    ∃ M : Matrix (((Unit ⊕ Unit) × o) ⊕ Unit) κ Poly,
      Y =
        Matrix.fromBlocks
          (Matrix.blockDiagonal
            (fun _ : o =>
              Matrix.fromBlocks
                (fun _ _ : Unit => a)
                (fun _ _ : Unit => b)
                (fun _ _ : Unit => -b)
                (fun _ _ : Unit => a)))
          0 0 (1 : Matrix Unit Unit Poly) * M ∧
      ∀ j, p ∣ M (Sum.inr ()) j := by
  classical
  let S : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) Poly :=
    Matrix.fromBlocks
      (fun _ _ : Unit => a)
      (fun _ _ : Unit => b)
      (fun _ _ : Unit => -b)
      (fun _ _ : Unit => a)
  let D : Matrix ((Unit ⊕ Unit) × o) ((Unit ⊕ Unit) × o) Poly :=
    Matrix.blockDiagonal (fun _ : o => S)
  let Ytop : Matrix ((Unit ⊕ Unit) × o) κ Poly := fun i j => Y (Sum.inl i) j
  rcases exists_sqAddSqBlockDiagonal_factor_of_linearCombinations_dvd hp0 hp Ytop
      (by intro t j; simpa [Ytop] using h1 t j)
      (by intro t j; simpa [Ytop] using h2 t j) with
    ⟨Mtop, htop⟩
  let Ybot : Matrix Unit κ Poly := fun _ j => Y (Sum.inr ()) j
  let M : Matrix (((Unit ⊕ Unit) × o) ⊕ Unit) κ Poly :=
    Matrix.fromRows Mtop Ybot
  have hDM :=
    (Matrix.fromBlocks_mul_fromRows Mtop Ybot D
      (0 : Matrix ((Unit ⊕ Unit) × o) Unit Poly)
      (0 : Matrix Unit ((Unit ⊕ Unit) × o) Poly)
      (1 : Matrix Unit Unit Poly))
  refine ⟨M, ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    cases i with
    | inl i =>
        have htop' :
            (Matrix.fromBlocks D 0 0 (1 : Matrix Unit Unit Poly) * M) (Sum.inl i) j =
              Y (Sum.inl i) j := by
          calc
              (Matrix.fromBlocks D 0 0 (1 : Matrix Unit Unit Poly) * M) (Sum.inl i) j
                  = (Sum.elim (D * Mtop) Ybot (Sum.inl i)) j := by
                        simpa [M, Matrix.fromRows] using
                          congrArg
                            (fun N : Matrix (((Unit ⊕ Unit) × o) ⊕ Unit) κ Poly => N (Sum.inl i) j)
                            hDM
              _ = (D * Mtop) i j := rfl
              _ = Ytop i j := by
                    simpa [D] using congrArg
                      (fun N : Matrix ((Unit ⊕ Unit) × o) κ Poly => N i j) htop.symm
              _ = Y (Sum.inl i) j := rfl
        exact htop'.symm
    | inr i =>
        have hbot' :
            (Matrix.fromBlocks D 0 0 (1 : Matrix Unit Unit Poly) * M) (Sum.inr i) j =
              Y (Sum.inr i) j := by
          calc
              (Matrix.fromBlocks D 0 0 (1 : Matrix Unit Unit Poly) * M) (Sum.inr i) j
                  = (Sum.elim (D * Mtop) Ybot (Sum.inr i)) j := by
                        simpa [M, Matrix.fromRows] using
                          congrArg
                            (fun N : Matrix (((Unit ⊕ Unit) × o) ⊕ Unit) κ Poly => N (Sum.inr i) j)
                            hDM
              _ = Ybot i j := rfl
              _ = Y (Sum.inr ()) j := by simp [Ybot]
              _ = Y (Sum.inr i) j := rfl
        exact hbot'.symm
  · intro j
    change p ∣ Ybot () j
    simpa [Ybot] using hbot j

theorem sqAddSqBlock_transpose_mul
    {α : Type*}
    [CommRing α]
    (a b : α) :
    (Matrix.fromBlocks
        (fun _ _ : Unit => a)
        (fun _ _ : Unit => b)
        (fun _ _ : Unit => -b)
        (fun _ _ : Unit => a) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) α).transpose *
      Matrix.fromBlocks
        (fun _ _ : Unit => a)
        (fun _ _ : Unit => b)
        (fun _ _ : Unit => -b)
        (fun _ _ : Unit => a) =
      (a ^ 2 + b ^ 2) • (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) α) := by
  ext i j
  cases i <;> cases j <;>
      simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.fromBlocks, pow_two] <;> ring_nf

theorem sqAddSqBlockDiagonal_transpose_mul
    {o α : Type*}
    [Fintype o]
    [DecidableEq o]
    [CommRing α]
    (a b : α) :
    (Matrix.blockDiagonal
        (fun _ : o =>
          Matrix.fromBlocks
            (fun _ _ : Unit => a)
            (fun _ _ : Unit => b)
            (fun _ _ : Unit => -b)
            (fun _ _ : Unit => a)) :
          Matrix ((Unit ⊕ Unit) × o) ((Unit ⊕ Unit) × o) α).transpose *
      Matrix.blockDiagonal
        (fun _ : o =>
          Matrix.fromBlocks
            (fun _ _ : Unit => a)
            (fun _ _ : Unit => b)
            (fun _ _ : Unit => -b)
            (fun _ _ : Unit => a)) =
      (a ^ 2 + b ^ 2) • (1 : Matrix ((Unit ⊕ Unit) × o) ((Unit ⊕ Unit) × o) α) := by
  let S : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) α :=
    Matrix.fromBlocks
      (fun _ _ : Unit => a)
      (fun _ _ : Unit => b)
      (fun _ _ : Unit => -b)
      (fun _ _ : Unit => a)
  calc
    (Matrix.blockDiagonal (fun _ : o => S)).transpose * Matrix.blockDiagonal (fun _ : o => S)
        = Matrix.blockDiagonal (fun _ : o => S.transpose * S) := by
            simp
    _ = Matrix.blockDiagonal
          (fun _ : o => (a ^ 2 + b ^ 2) • (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) α)) := by
            simp [S, sqAddSqBlock_transpose_mul]
    _ = (a ^ 2 + b ^ 2) •
          Matrix.blockDiagonal (fun _ : o => (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) α)) := by
            have hs :
                (fun _ : o => (a ^ 2 + b ^ 2) • (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) α)) =
                  (a ^ 2 + b ^ 2) •
                    (fun _ : o => (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) α)) := by
              funext x
              simp
            rw [hs, Matrix.blockDiagonal_smul]
    _ = (a ^ 2 + b ^ 2) • (1 : Matrix ((Unit ⊕ Unit) × o) ((Unit ⊕ Unit) × o) α) := by
          have hone :
              Matrix.blockDiagonal
                  (fun _ : o => (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) α)) =
                (1 : Matrix ((Unit ⊕ Unit) × o) ((Unit ⊕ Unit) × o) α) :=
            Matrix.blockDiagonal_one (m := Unit ⊕ Unit) (o := o) (α := α)
          rw [hone]

theorem sqAddSqOddUnitBlockDiagonal_transpose_mul_explicit
    {o α : Type*}
    [Fintype o]
    [DecidableEq o]
    [CommRing α]
    (a b : α) :
    (Matrix.fromBlocks
        (Matrix.blockDiagonal
          (fun _ : o =>
            Matrix.fromBlocks
              (fun _ _ : Unit => a)
              (fun _ _ : Unit => b)
              (fun _ _ : Unit => -b)
              (fun _ _ : Unit => a)))
        0 0 (1 : Matrix Unit Unit α) :
          Matrix (((Unit ⊕ Unit) × o) ⊕ Unit) (((Unit ⊕ Unit) × o) ⊕ Unit) α).transpose *
      Matrix.fromBlocks
        (Matrix.blockDiagonal
          (fun _ : o =>
            Matrix.fromBlocks
              (fun _ _ : Unit => a)
              (fun _ _ : Unit => b)
              (fun _ _ : Unit => -b)
              (fun _ _ : Unit => a)))
        0 0 (1 : Matrix Unit Unit α) =
      Matrix.fromBlocks
        ((a ^ 2 + b ^ 2) •
          (1 : Matrix ((Unit ⊕ Unit) × o) ((Unit ⊕ Unit) × o) α))
        0 0 (1 : Matrix Unit Unit α) := by
  let D : Matrix ((Unit ⊕ Unit) × o) ((Unit ⊕ Unit) × o) α :=
    Matrix.blockDiagonal
      (fun _ : o =>
        Matrix.fromBlocks
          (fun _ _ : Unit => a)
          (fun _ _ : Unit => b)
          (fun _ _ : Unit => -b)
          (fun _ _ : Unit => a))
  calc
    (Matrix.fromBlocks D 0 0 (1 : Matrix Unit Unit α)).transpose *
        Matrix.fromBlocks D 0 0 (1 : Matrix Unit Unit α) =
      Matrix.fromBlocks (D.transpose * D) 0 0 (1 : Matrix Unit Unit α) := by
        simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    _ =
      Matrix.fromBlocks
        ((a ^ 2 + b ^ 2) •
          (1 : Matrix ((Unit ⊕ Unit) × o) ((Unit ⊕ Unit) × o) α))
        0 0 (1 : Matrix Unit Unit α) := by
          rw [sqAddSqBlockDiagonal_transpose_mul (o := o) a b]

end MatrixSOS
