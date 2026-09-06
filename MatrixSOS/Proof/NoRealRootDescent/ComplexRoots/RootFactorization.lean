/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.NoRealRootDescent.Divisibility
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

open Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS

theorem exists_complex_root_of_irreducible_of_forall_not_isRoot
    {p : Poly}
    (hp : Irreducible p)
    (hnoroot : ∀ a : ℝ, ¬ p.IsRoot a) :
    ∃ z : ℂ, ((normalize p).map (algebraMap ℝ ℂ)).IsRoot z ∧ z.im ≠ 0 := by
  let f : Poly := normalize p
  have hm : f.Monic := Polynomial.monic_normalize hp.ne_zero
  have hmC : (f.map (algebraMap ℝ ℂ)).Monic := hm.map (algebraMap ℝ ℂ)
  have hnatf : f.natDegree = 2 := by
    have hdegf : f.degree = 2 := by
      rw [show f = normalize p by rfl, Polynomial.degree_normalize,
        Polynomial.degree_eq_natDegree hp.ne_zero,
        natDegree_eq_two_of_irreducible_of_forall_not_isRoot hp hnoroot]
      norm_num
    exact Polynomial.natDegree_eq_of_degree_eq_some hdegf
  have hnat : (f.map (algebraMap ℝ ℂ)).natDegree = 2 := by
    simpa [f] using
      (Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective (normalize p)).trans
        hnatf
  have hdeg : (f.map (algebraMap ℝ ℂ)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hmC.ne_zero, hnat]
    norm_num
  rcases IsAlgClosed.exists_root (f.map (algebraMap ℝ ℂ)) hdeg with ⟨z, hz⟩
  refine ⟨z, hz, ?_⟩
  intro hzim
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [hzim]
  have hrootMap : (f.map (algebraMap ℝ ℂ)).IsRoot (z.re : ℂ) := by
    rw [hzreal] at hz
    simpa using hz
  have hrootReal : f.IsRoot z.re :=
    Polynomial.IsRoot.of_map (f := algebraMap ℝ ℂ) hrootMap (algebraMap ℝ ℂ).injective
  exact hnoroot z.re ((normalize_associated p).dvd_iff_dvd_right.mp
    (Polynomial.dvd_iff_isRoot.mpr hrootReal) |> Polynomial.dvd_iff_isRoot.mp)

open ComplexConjugate in
theorem isRoot_conj_of_isRoot_map_of_real
    {p : Poly}
    {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).IsRoot z) :
    (p.map (algebraMap ℝ ℂ)).IsRoot (conj z) := by
  rw [Polynomial.IsRoot, Polynomial.eval_map] at hz ⊢
  have hconj :
      eval₂ (algebraMap ℝ ℂ) (conj z) p =
        conj (eval₂ (algebraMap ℝ ℂ) z p) := by
    simpa [Polynomial.aeval_def] using Polynomial.aeval_conj p z
  rw [hz] at hconj
  simpa using hconj

open ComplexConjugate in
theorem conj_ne_self_of_im_ne_zero
    {z : ℂ}
    (hz : z.im ≠ 0) :
    conj z ≠ z := by
  intro h
  exact hz (by simpa using (RCLike.conj_eq_iff_im).mp h)

open ComplexConjugate in
theorem exists_complex_conjugate_root_pair_of_irreducible_of_forall_not_isRoot
    {p : Poly}
    (hp : Irreducible p)
    (hnoroot : ∀ a : ℝ, ¬ p.IsRoot a) :
    ∃ z : ℂ,
      ((normalize p).map (algebraMap ℝ ℂ)).IsRoot z ∧
      ((normalize p).map (algebraMap ℝ ℂ)).IsRoot (conj z) ∧
      conj z ≠ z := by
  rcases exists_complex_root_of_irreducible_of_forall_not_isRoot hp hnoroot with ⟨z, hz, hzim⟩
  refine ⟨z, hz, isRoot_conj_of_isRoot_map_of_real hz, conj_ne_self_of_im_ne_zero hzim⟩

theorem sum_eq_neg_coeff_of_monic_quadratic_of_isRoot_of_isRoot_of_ne
    {b c z w : ℂ}
    (hz : (X ^ 2 + C b * X + C c : Polynomial ℂ).IsRoot z)
    (hw : (X ^ 2 + C b * X + C c : Polynomial ℂ).IsRoot w)
    (hzw : z ≠ w) :
    z + w = -b := by
  rw [Polynomial.IsRoot] at hz hw
  have hsub :
      (z - w) * (z + w + b) =
        eval z (X ^ 2 + C b * X + C c : Polynomial ℂ) -
          eval w (X ^ 2 + C b * X + C c : Polynomial ℂ) := by
    simp [Polynomial.eval_add, Polynomial.eval_mul, pow_two]
    ring
  rw [hz, hw, sub_zero] at hsub
  have hmul : z + w + b = 0 := by
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hzw)
  apply eq_neg_iff_add_eq_zero.mpr
  simpa [add_assoc, add_comm, add_left_comm] using hmul

theorem mul_eq_coeff_of_monic_quadratic_of_isRoot_of_isRoot_of_ne
    {b c z w : ℂ}
    (hz : (X ^ 2 + C b * X + C c : Polynomial ℂ).IsRoot z)
    (hw : (X ^ 2 + C b * X + C c : Polynomial ℂ).IsRoot w)
    (hzw : z ≠ w) :
    z * w = c := by
  rw [Polynomial.IsRoot] at hz
  have hsum : z + w = -b :=
    sum_eq_neg_coeff_of_monic_quadratic_of_isRoot_of_isRoot_of_ne hz hw hzw
  have hz' : z ^ 2 + b * z + c = 0 := by
    simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, pow_two,
      mul_assoc, add_assoc, add_left_comm, add_comm] using hz
  have hrew : b * z = -(z * (z + w)) := by
    calc
      b * z = (-(z + w)) * z := by simp [hsum]
      _ = -(z * (z + w)) := by ring
  rw [hrew] at hz'
  have hc : c - z * w = 0 := by
    simpa [pow_two, mul_add, mul_assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz'
  exact eq_comm.mp (sub_eq_zero.mp hc)

theorem normalize_eq_X_sq_add_C_mul_X_add_C_of_irreducible_of_forall_not_isRoot
    {p : Poly}
    (hp : Irreducible p)
    (hnoroot : ∀ a : ℝ, ¬ p.IsRoot a) :
    normalize p =
      X ^ 2 + C ((normalize p).coeff 1) * X + C ((normalize p).coeff 0) := by
  let f : Poly := normalize p
  have hm : f.Monic := Polynomial.monic_normalize hp.ne_zero
  have hdeg : f.natDegree = 2 := by
    have hdegAssoc : degree (normalize p) = degree p :=
      Polynomial.degree_eq_degree_of_associated (normalize_associated p)
    have hdegNorm : (normalize p).degree = 2 := by
      rw [hdegAssoc, Polynomial.degree_eq_natDegree hp.ne_zero,
        natDegree_eq_two_of_irreducible_of_forall_not_isRoot hp hnoroot]
      norm_num
    exact Polynomial.natDegree_eq_of_degree_eq_some hdegNorm
  ext n
  by_cases h0 : n = 0
  · subst n
    simp
  by_cases h1 : n = 1
  · subst n
    simp
  by_cases h2 : n = 2
  · subst n
    have hcoeff : (normalize p).coeff 2 = 1 := by
      change f.coeff 2 = 1
      simpa [hdeg] using hm.coeff_natDegree
    simp [hcoeff]
  have hn : 2 < n := by omega
  have hcoeff : (normalize p).coeff n = 0 := by
    have hn' : (normalize p).natDegree < n := by
      simpa [f, hdeg] using hn
    exact coeff_eq_zero_of_natDegree_lt hn'
  have hX : (X : Poly).coeff n = 0 := by
    simp [coeff_X, show ¬ 1 = n by omega]
  have hC : (C ((normalize p).coeff 0)).coeff n = 0 := by
    simp [coeff_C, h0]
  have hlin : (normalize p).coeff 1 * X.coeff n = 0 := by
    exact mul_eq_zero_of_right _ hX
  simp [hcoeff, coeff_X_pow, hC, hlin, h2]

theorem roots_eq_pair_of_monic_quadratic_of_isRoot_of_isRoot_of_ne
    {b c z w : ℂ}
    (hz : (X ^ 2 + C b * X + C c : Polynomial ℂ).IsRoot z)
    (hw : (X ^ 2 + C b * X + C c : Polynomial ℂ).IsRoot w)
    (hzw : z ≠ w) :
    (X ^ 2 + C b * X + C c : Polynomial ℂ).roots = {z, w} := by
  have hpair :
      (C (1 : ℂ) * X ^ 2 + C b * X + C c : Polynomial ℂ).roots = {z, w} := by
    refine
      (Polynomial.roots_quadratic_eq_pair_iff_of_ne_zero
        (R := ℂ) (a := (1 : ℂ)) (b := b) (c := c) (x1 := z) (x2 := w) one_ne_zero).2 ?_
    constructor
    · simpa [add_comm, eq_comm] using
        congrArg Neg.neg
          (sum_eq_neg_coeff_of_monic_quadratic_of_isRoot_of_isRoot_of_ne hz hw hzw)
    · simpa [mul_comm] using
        (mul_eq_coeff_of_monic_quadratic_of_isRoot_of_isRoot_of_ne hz hw hzw).symm
  simpa using hpair

open ComplexConjugate in
theorem roots_map_normalize_eq_conjugate_pair_of_irreducible_of_forall_not_isRoot
    {p : Poly}
    (hp : Irreducible p)
    (hnoroot : ∀ a : ℝ, ¬ p.IsRoot a) :
    ∃ z : ℂ,
      ((normalize p).map (algebraMap ℝ ℂ)).roots = {z, conj z} := by
  rcases exists_complex_conjugate_root_pair_of_irreducible_of_forall_not_isRoot hp hnoroot with
    ⟨z, hz, hzconj, hneq⟩
  refine ⟨z, ?_⟩
  have hshapeR :
      normalize p =
        X ^ 2 + C ((normalize p).coeff 1) * X + C ((normalize p).coeff 0) :=
    normalize_eq_X_sq_add_C_mul_X_add_C_of_irreducible_of_forall_not_isRoot hp hnoroot
  have hshape :
      (normalize p).map (algebraMap ℝ ℂ) =
        (X ^ 2 + C (((normalize p).coeff 1 : ℝ) : ℂ) * X +
          C (((normalize p).coeff 0 : ℝ) : ℂ) : Polynomial ℂ) := by
    simpa using congrArg (Polynomial.map (algebraMap ℝ ℂ)) hshapeR
  have hz' :
      (X ^ 2 + C (((normalize p).coeff 1 : ℝ) : ℂ) * X +
        C (((normalize p).coeff 0 : ℝ) : ℂ) : Polynomial ℂ).IsRoot z := by
    simpa [hshape] using hz
  have hzconj' :
      (X ^ 2 + C (((normalize p).coeff 1 : ℝ) : ℂ) * X +
        C (((normalize p).coeff 0 : ℝ) : ℂ) : Polynomial ℂ).IsRoot (conj z) := by
    simpa [hshape] using hzconj
  rw [hshape]
  exact roots_eq_pair_of_monic_quadratic_of_isRoot_of_isRoot_of_ne hz' hzconj' hneq.symm

open ComplexConjugate in
theorem map_normalize_eq_mul_X_sub_C_conj_of_irreducible_of_forall_not_isRoot
    {p : Poly}
    (hp : Irreducible p)
    (hnoroot : ∀ a : ℝ, ¬ p.IsRoot a) :
    ∃ z : ℂ,
      (normalize p).map (algebraMap ℝ ℂ) =
        (X - C z) * (X - C (conj z)) := by
  rcases roots_map_normalize_eq_conjugate_pair_of_irreducible_of_forall_not_isRoot hp hnoroot with
    ⟨z, hroots⟩
  refine ⟨z, ?_⟩
  have hm : ((normalize p).map (algebraMap ℝ ℂ)).Monic := by
    exact (Polynomial.monic_normalize hp.ne_zero).map (algebraMap ℝ ℂ)
  have hnatNorm : (normalize p).natDegree = 2 := by
    have hdegAssoc : degree (normalize p) = degree p :=
      Polynomial.degree_eq_degree_of_associated (normalize_associated p)
    have hdegNorm : (normalize p).degree = 2 := by
      rw [hdegAssoc, Polynomial.degree_eq_natDegree hp.ne_zero,
        natDegree_eq_two_of_irreducible_of_forall_not_isRoot hp hnoroot]
      norm_num
    exact Polynomial.natDegree_eq_of_degree_eq_some hdegNorm
  have hcard :
      (((normalize p).map (algebraMap ℝ ℂ)).roots).card =
        ((normalize p).map (algebraMap ℝ ℂ)).natDegree := by
    rw [hroots, Multiset.card_pair]
    simpa using ((Polynomial.natDegree_map_eq_of_injective
      (algebraMap ℝ ℂ).injective (normalize p)).trans hnatNorm).symm
  calc
    (normalize p).map (algebraMap ℝ ℂ)
        = ((((normalize p).map (algebraMap ℝ ℂ)).roots.map fun a => X - C a).prod) := by
            simpa using
              (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard).symm
    _ = (X - C z) * (X - C (conj z)) := by
          rw [hroots]
          simp

open ComplexConjugate in
theorem exists_complex_root_factor_of_irreducible_of_normalized_of_forall_not_isRoot
    {p : Poly}
    (hp : Irreducible p)
    (hnorm : normalize p = p)
    (hnoroot : ∀ a : ℝ, ¬ p.IsRoot a) :
    ∃ z : ℂ,
      p.map (algebraMap ℝ ℂ) = (X - C z) * (X - C (conj z)) ∧
        z.im ≠ 0 := by
  rcases map_normalize_eq_mul_X_sub_C_conj_of_irreducible_of_forall_not_isRoot hp hnoroot with
    ⟨z, hz⟩
  refine ⟨z, ?_, ?_⟩
  · simpa [hnorm] using hz
  · intro hzim
    have hzmap : (p.map (algebraMap ℝ ℂ)).IsRoot z := by
      rw [show p.map (algebraMap ℝ ℂ) = (X - C z) * (X - C (conj z)) by simpa [hnorm] using hz]
      simp [Polynomial.IsRoot]
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hzim]
    have hrootMap : (p.map (algebraMap ℝ ℂ)).IsRoot (z.re : ℂ) := by
      rw [← hzreal]
      exact hzmap
    have hrootReal : p.IsRoot z.re :=
      Polynomial.IsRoot.of_map (f := algebraMap ℝ ℂ) hrootMap (algebraMap ℝ ℂ).injective
    exact hnoroot z.re hrootReal

open ComplexConjugate in
theorem exists_complex_root_sub_I_mul_eq_zero_of_irreducible_of_normalized_of_forall_not_isRoot
    {p a b : Poly}
    (hp : Irreducible p)
    (hnorm : normalize p = p)
    (hnoroot : ∀ x : ℝ, ¬ p.IsRoot x)
    (hsq : p = a ^ 2 + b ^ 2) :
    ∃ z : ℂ,
      p.map (algebraMap ℝ ℂ) = (X - C z) * (X - C (conj z)) ∧
        z.im ≠ 0 ∧
        (eval₂ (algebraMap ℝ ℂ) z a - Complex.I * eval₂ (algebraMap ℝ ℂ) z b = 0) := by
  rcases exists_complex_root_factor_of_irreducible_of_normalized_of_forall_not_isRoot
      hp hnorm hnoroot with ⟨z, hzfac, hzim⟩
  let az : ℂ := eval₂ (algebraMap ℝ ℂ) z a
  let bz : ℂ := eval₂ (algebraMap ℝ ℂ) z b
  have hpz : eval₂ (algebraMap ℝ ℂ) z p = 0 := by
    have hzroot : (p.map (algebraMap ℝ ℂ)).IsRoot z := by
      rw [hzfac]
      simp [Polynomial.IsRoot]
    simpa [Polynomial.IsRoot, Polynomial.eval_map] using hzroot
  have hsqz : az ^ 2 + bz ^ 2 = 0 := by
    have hpz' : eval₂ (algebraMap ℝ ℂ) z (a ^ 2 + b ^ 2) = 0 := by
      simpa [hsq] using hpz
    simpa [az, bz, Polynomial.eval₂_add, Polynomial.eval₂_pow, pow_two] using hpz'
  have hprod :
      (az - Complex.I * bz) * (az + Complex.I * bz) = 0 := by
    calc
      (az - Complex.I * bz) * (az + Complex.I * bz) = az ^ 2 + bz ^ 2 := by
        ring_nf
        norm_num [Complex.I_sq]
      _ = 0 := hsqz
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · exact ⟨z, hzfac, hzim, hminus⟩
  · refine ⟨conj z, ?_, ?_, ?_⟩
    · simpa [mul_comm] using hzfac
    · simpa using hzim
    · have ha_conj :
          eval₂ (algebraMap ℝ ℂ) (conj z) a =
            conj (eval₂ (algebraMap ℝ ℂ) z a) := by
          simpa [Polynomial.aeval_def] using Polynomial.aeval_conj a z
      have hb_conj :
          eval₂ (algebraMap ℝ ℂ) (conj z) b =
            conj (eval₂ (algebraMap ℝ ℂ) z b) := by
          simpa [Polynomial.aeval_def] using Polynomial.aeval_conj b z
      have hplusConj := congrArg conj hplus
      simpa [az, bz, ha_conj, hb_conj, sub_eq_add_neg] using hplusConj

end MatrixSOS
