/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.Polynomial
import Mathlib.Data.Matrix.Basic

/-!
# Polynomial divisibility in descent without real roots
-/

open Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

/-- Entrywise divisibility of a polynomial matrix by a scalar polynomial. -/
def EntrywiseDvdBy {ι κ : Type*} (p : Poly) (A : Matrix ι κ Poly) : Prop :=
  ∀ i j, p ∣ A i j

theorem entrywiseDvdBy_iff_exists_smul
    {ι κ : Type*}
    (p : Poly)
    (A : Matrix ι κ Poly) :
    EntrywiseDvdBy p A ↔ ∃ B : Matrix ι κ Poly, A = p • B := by
  constructor
  · intro h
    refine ⟨fun i j => Classical.choose (h i j), ?_⟩
    funext i j
    change A i j = p * Classical.choose (h i j)
    exact Classical.choose_spec (h i j)
  · rintro ⟨B, rfl⟩ i j
    exact ⟨B i j, by simp [Matrix.smul_apply]⟩

theorem entrywiseDvdBy_of_eq_smul
    {ι κ : Type*}
    {p : Poly}
    {A B : Matrix ι κ Poly}
    (h : A = p • B) :
    EntrywiseDvdBy p A := by
  rw [entrywiseDvdBy_iff_exists_smul]
  exact ⟨B, h⟩

theorem entrywiseDvdBy_sq_of_scaled_gram
    {n : Type*}
    [Fintype n]
    {p : Poly}
    {A Q : Matrix n n Poly}
    (h : (p ^ 2) • A = Q.transpose * Q) :
    EntrywiseDvdBy (p ^ 2) (Q.transpose * Q) := by
  exact entrywiseDvdBy_of_eq_smul h.symm

theorem entrywiseDvdBy_of_sq
    {ι κ : Type*}
    {p : Poly}
    {A : Matrix ι κ Poly}
    (hA : EntrywiseDvdBy (p ^ 2) A) :
    EntrywiseDvdBy p A := by
  intro i j
  exact dvd_trans ⟨p, by simp [pow_two]⟩ (hA i j)

theorem irreducible_associated_X_sub_C_of_isRoot
    {p : Poly}
    (hp : Irreducible p)
    {a : ℝ}
    (ha : p.IsRoot a) :
    Associated p (X - C a) := by
  have hdiv : X - C a ∣ p := Polynomial.dvd_iff_isRoot.mpr ha
  have hdiv' : p ∣ X - C a :=
    (Polynomial.irreducible_X_sub_C a).dvd_symm hp hdiv
  exact associated_of_dvd_dvd hdiv' hdiv

theorem natDegree_eq_two_of_irreducible_of_forall_not_isRoot
    {p : Poly}
    (hp : Irreducible p)
    (hroot : ∀ a : ℝ, ¬ p.IsRoot a) :
    p.natDegree = 2 := by
  have hpos : 0 < p.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hp)
  have hle : p.natDegree ≤ 2 := hp.natDegree_le_two
  have hne1 : p.natDegree ≠ 1 := by
    intro h1
    have hdeg1 : p.degree = 1 := by
      exact (Polynomial.degree_eq_iff_natDegree_eq hp.ne_zero).2 h1
    rcases Polynomial.exists_root_of_degree_eq_one hdeg1 with ⟨a, ha⟩
    exact hroot a ha
  have hge1 : 1 ≤ p.natDegree := Nat.succ_le_of_lt hpos
  have hgt1 : 1 < p.natDegree := lt_of_le_of_ne hge1 (Ne.symm hne1)
  exact le_antisymm hle (Nat.succ_le_of_lt hgt1)

theorem exists_sq_add_sq_of_normalize_of_irreducible_of_forall_not_isRoot
    {p : Poly}
    (hp : Irreducible p)
    (hnoroot : ∀ a : ℝ, ¬ p.IsRoot a) :
    ∃ a b : Poly, normalize p = a ^ 2 + b ^ 2 := by
  have hm : (normalize p).Monic := Polynomial.monic_normalize hp.ne_zero
  have hdeg : (normalize p).natDegree = 2 := by
    have hdegAssoc : degree (normalize p) = degree p :=
      Polynomial.degree_eq_degree_of_associated (normalize_associated p)
    have hdegNorm : (normalize p).degree = 2 := by
      rw [hdegAssoc, Polynomial.degree_eq_natDegree hp.ne_zero,
        natDegree_eq_two_of_irreducible_of_forall_not_isRoot hp hnoroot]
      norm_num
    exact Polynomial.natDegree_eq_of_degree_eq_some hdegNorm
  have hrootNorm : ∀ x : ℝ, (normalize p).eval x ≠ 0 := by
    intro x hx
    have hnormroot : (normalize p).IsRoot x := by
      simpa [Polynomial.IsRoot] using hx
    have hproot : p.IsRoot x := by
      exact ((normalize_associated p).dvd_iff_dvd_right.mp
        (Polynomial.dvd_iff_isRoot.mpr hnormroot) |> Polynomial.dvd_iff_isRoot.mp)
    exact hnoroot x hproot
  have hpos : ∀ x : ℝ, 0 < (normalize p).eval x :=
    eval_pos_of_isMonicOfDegree_two_of_no_real_root ⟨hdeg, hm⟩ hrootNorm
  exact exists_sq_add_sq_of_isMonicOfDegree_two_of_eval_pos ⟨hdeg, hm⟩ hpos

theorem exists_bezout_sq_add_sq_of_normalize_of_irreducible_of_forall_not_isRoot
    {p : Poly}
    (hp : Irreducible p)
    (hnoroot : ∀ a : ℝ, ¬ p.IsRoot a) :
    ∃ a b u v : Poly,
      normalize p = a ^ 2 + b ^ 2 ∧
      u * a + v * b = 1 := by
  rcases exists_sq_add_sq_of_normalize_of_irreducible_of_forall_not_isRoot hp hnoroot with
    ⟨a₀, b₀, hsq⟩
  rcases exists_bezout_coprime_sq_add_sq_factor ⟨a₀, b₀, hsq⟩ with
    ⟨g, a, b, u, v, hfac, hbez⟩
  have hpNorm : Irreducible (normalize p) := by
    exact (normalize_associated p).symm.irreducible hp
  have hgunit : IsUnit g := by
    have hsplit : normalize p = g * (g * (a ^ 2 + b ^ 2)) := by
      simpa [pow_two, mul_assoc] using hfac
    rcases hpNorm.isUnit_or_isUnit hsplit with hg | hga
    · exact hg
    · exact isUnit_of_mul_isUnit_left hga
  let ginv : Poly := ↑(hgunit.unit⁻¹)
  refine ⟨g * a, g * b, ginv * u, ginv * v, ?_, ?_⟩
  · calc
      normalize p = g ^ 2 * (a ^ 2 + b ^ 2) := hfac
      _ = (g * a) ^ 2 + (g * b) ^ 2 := by ring
  · calc
      (ginv * u) * (g * a) + (ginv * v) * (g * b)
          = (ginv * g) * (u * a + v * b) := by
              dsimp [ginv]
              ring
      _ = 1 := by
            dsimp [ginv]
            simp [hbez]

theorem exists_bezout_sq_add_sq_of_irreducible_of_normalized_of_forall_not_isRoot
    {p : Poly}
    (hp : Irreducible p)
    (hnorm : normalize p = p)
    (hnoroot : ∀ a : ℝ, ¬ p.IsRoot a) :
    ∃ a b u v : Poly,
      p = a ^ 2 + b ^ 2 ∧
      u * a + v * b = 1 := by
  rcases exists_bezout_sq_add_sq_of_normalize_of_irreducible_of_forall_not_isRoot hp hnoroot with
    ⟨a, b, u, v, hsq, hbez⟩
  refine ⟨a, b, u, v, ?_, hbez⟩
  simpa [hnorm] using hsq

end MatrixSOS
