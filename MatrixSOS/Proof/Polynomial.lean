/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Factorization
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.FieldTheory.Perfect
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.PrincipalIdealDomain

open Polynomial

noncomputable section

namespace MatrixSOS

theorem coeff_pow_two_two_natDegree
    (p : Poly) :
    coeff (p ^ 2) (2 * p.natDegree) = p.leadingCoeff ^ 2 := by
  by_cases hp : p = 0
  · simp [hp]
  · have hlead : p.leadingCoeff ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hp)
    rw [← Polynomial.natDegree_pow' (p := p) (n := 2) hlead]
    rw [coeff_natDegree, leadingCoeff_pow']
    simp [hp]

theorem coeff_pow_two_eq_zero_of_natDegree_lt
    (p : Poly)
    {N : ℕ}
    (h : p.natDegree < N) :
    coeff (p ^ 2) (2 * N) = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hle : natDegree (p ^ 2) ≤ 2 * p.natDegree := natDegree_pow_le (p := p) (n := 2)
  omega

theorem coeff_sum_squares_two_mul
    {ι : Type*}
    [Fintype ι]
    (f : ι → Poly)
    (N : ℕ)
    (hN : ∀ i, natDegree (f i) ≤ N) :
    coeff (∑ i, (f i) ^ 2) (2 * N) =
      Finset.sum (Finset.univ.filter (fun i => natDegree (f i) = N))
        (fun i => (leadingCoeff (f i)) ^ 2) := by
  classical
  have hterm :
      ∀ i,
        coeff ((f i) ^ 2) (2 * N) =
          if natDegree (f i) = N then (leadingCoeff (f i)) ^ 2 else 0 := by
    intro i
    by_cases hi : natDegree (f i) = N
    · rw [if_pos hi, ← hi]
      exact coeff_pow_two_two_natDegree (f i)
    · have hlt : natDegree (f i) < N := lt_of_le_of_ne (hN i) hi
      simp [hi, coeff_pow_two_eq_zero_of_natDegree_lt (f i) hlt]
  calc
    coeff (∑ i, (f i) ^ 2) (2 * N)
        = ∑ i, coeff ((f i) ^ 2) (2 * N) := by simp
    _ = ∑ i, if natDegree (f i) = N then (leadingCoeff (f i)) ^ 2 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hterm i
    _ = Finset.sum (Finset.univ.filter (fun i => natDegree (f i) = N))
          (fun i => (leadingCoeff (f i)) ^ 2) := by
          rw [Finset.sum_filter]

theorem natDegree_le_of_sum_squares
    {ι : Type*}
    [Fintype ι]
    (f : ι → Poly)
    {d : ℕ}
    (hdeg : natDegree (∑ i, (f i) ^ 2) ≤ 2 * d) :
    ∀ i, natDegree (f i) ≤ d := by
  classical
  intro i
  let _ : Nonempty ι := ⟨i⟩
  by_contra hi
  have hdi : d < natDegree (f i) := Nat.lt_of_not_ge hi
  obtain ⟨k, hk_mem, hk_max⟩ :=
    Finset.exists_maximalFor (fun j : ι => natDegree (f j)) (Finset.univ : Finset ι)
      Finset.univ_nonempty
  let N := natDegree (f k)
  have hN : ∀ j : ι, natDegree (f j) ≤ N := by
    intro j
    by_cases hkj : natDegree (f k) ≤ natDegree (f j)
    · exact hk_max (by simp) hkj
    · exact le_of_not_ge hkj
  have hNgt : d < N := lt_of_lt_of_le hdi (hN i)
  have hk_filter : k ∈ Finset.univ.filter (fun j : ι => natDegree (f j) = N) := by
    simp [N]
  have hk_ne_zero : f k ≠ 0 := by
    intro hk0
    have : N = 0 := by simp [N, hk0]
    omega
  have hk_term_pos : 0 < (leadingCoeff (f k)) ^ 2 := by
    exact sq_pos_iff.mpr (leadingCoeff_ne_zero.mpr hk_ne_zero)
  have hsum_pos :
      0 <
        Finset.sum (Finset.univ.filter (fun j : ι => natDegree (f j) = N))
          (fun j => (leadingCoeff (f j)) ^ 2) := by
    refine Finset.sum_pos' (fun j hj => sq_nonneg _) ?_
    exact ⟨k, hk_filter, hk_term_pos⟩
  have hcoeff_ne :
      coeff (∑ j, (f j) ^ 2) (2 * N) ≠ 0 := by
    rw [coeff_sum_squares_two_mul f N hN]
    exact hsum_pos.ne'
  have hdeg_ge : 2 * N ≤ natDegree (∑ j, (f j) ^ 2) :=
    le_natDegree_of_ne_zero hcoeff_ne
  omega

lemma derivative_eval_eq_zero_of_nonneg_of_eval_eq_zero {p : Poly} {x : ℝ}
    (hp : ∀ y : ℝ, 0 ≤ p.eval y) (hx : p.eval x = 0) :
    p.derivative.eval x = 0 := by
  have hlocal : IsLocalMin (fun y : ℝ => p.eval y) x := by
    exact Filter.Eventually.of_forall (fun y => by simpa [hx] using hp y)
  exact IsLocalMin.hasDerivAt_eq_zero hlocal (p.hasDerivAt x)

lemma one_lt_rootMultiplicity_of_nonneg_of_isRoot {p : Poly} (hp0 : p ≠ 0)
    (hp : ∀ y : ℝ, 0 ≤ p.eval y) {x : ℝ} (hx : p.IsRoot x) :
    1 < p.rootMultiplicity x := by
  rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hp0]
  refine ⟨hx, ?_⟩
  exact derivative_eval_eq_zero_of_nonneg_of_eval_eq_zero hp hx

lemma natDegree_ne_one_of_nonneg {p : Poly} (hp0 : p ≠ 0)
    (hp : ∀ y : ℝ, 0 ≤ p.eval y) :
    p.natDegree ≠ 1 := by
  intro hdeg
  rw [Polynomial.natDegree_eq_one] at hdeg
  rcases hdeg with ⟨a, ha0, b, rfl⟩
  by_cases ha : 0 < a
  · have hcalc : (C a * X + C b).eval (-b / a - 1) = -a := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, div_eq_mul_inv]
      field_simp [ha0]
      ring_nf
    have hneg : (C a * X + C b).eval (-b / a - 1) < 0 := by
      rw [hcalc]
      linarith
    exact (not_lt_of_ge (hp (-b / a - 1))) hneg
  · have hlt : a < 0 := lt_of_le_of_ne (le_of_not_gt ha) (by simpa [eq_comm] using ha0)
    have hcalc : (C a * X + C b).eval (-b / a + 1) = a := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, div_eq_mul_inv]
      field_simp [ha0]
      ring_nf
    have hneg : (C a * X + C b).eval (-b / a + 1) < 0 := by
      rw [hcalc]
      linarith
    exact (not_lt_of_ge (hp (-b / a + 1))) hneg

lemma exists_nonneg_factor_of_dvd_of_eval_pos {p q : Poly}
    (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (hq : ∀ x : ℝ, 0 < q.eval x)
    (hdiv : q ∣ p) :
    ∃ r : Poly, p = q * r ∧ ∀ x : ℝ, 0 ≤ r.eval x := by
  rcases hdiv with ⟨r, rfl⟩
  refine ⟨r, rfl, ?_⟩
  intro x
  have hp' : 0 ≤ (q * r).eval x := hp x
  rw [Polynomial.eval_mul] at hp'
  exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hp') (hq x)

lemma exists_sq_add_sq_of_isMonicOfDegree_two_of_eval_pos {f : Poly}
    (hf : Polynomial.IsMonicOfDegree f 2)
    (hpos : ∀ x : ℝ, 0 < f.eval x) :
    ∃ a b : Poly, f = a ^ 2 + b ^ 2 := by
  rw [Polynomial.isMonicOfDegree_two_iff'] at hf
  rcases hf with ⟨u, v, rfl⟩
  let c : ℝ := u / 2
  have hconst : 0 < v - u ^ 2 / 4 := by
    have h := hpos c
    dsimp [c] at h
    have hcalc : ((X ^ 2 - C u * X + C v : Poly).eval (u / 2)) = v - u ^ 2 / 4 := by
      simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
      ring_nf
    rwa [hcalc] at h
  refine ⟨X - C c, C (Real.sqrt (v - u ^ 2 / 4)), ?_⟩
  have hsq : Real.sqrt (v - u ^ 2 / 4) ^ 2 = v - u ^ 2 / 4 := by
    exact Real.sq_sqrt (le_of_lt hconst)
  have hc : (2 : ℝ) * c = u := by
    dsimp [c]
    ring
  have hCpow : C c ^ 2 = C (c ^ 2) := by
    rw [pow_two]
    rw [show C (c ^ 2) = C c * C c by
      rw [pow_two, map_mul]]
  have hmid : 2 * X * C c = C ((2 : ℝ) * c) * X := by
    calc
      2 * X * C c = C (2 : ℝ) * X * C c := by rfl
      _ = C (2 : ℝ) * (C c * X) := by rw [mul_assoc, mul_comm X (C c)]
      _ = (C (2 : ℝ) * C c) * X := by rw [← mul_assoc]
      _ = C ((2 : ℝ) * c) * X := by rw [← map_mul]
  have hsquare : (X - C c) ^ 2 = X ^ 2 - C ((2 : ℝ) * c) * X + C (c ^ 2) := by
    calc
      (X - C c) ^ 2 = X ^ 2 - 2 * X * C c + (C c) ^ 2 := by
        rw [sub_sq]
      _ = X ^ 2 - C ((2 : ℝ) * c) * X + C (c ^ 2) := by
        rw [hmid]
        rw [hCpow]
  calc
    X ^ 2 - C u * X + C v
        = X ^ 2 - C ((2 : ℝ) * c) * X + C (c ^ 2 + Real.sqrt (v - u ^ 2 / 4) ^ 2) := by
            congr 2
            · simp [hc]
            · rw [hsq]
              dsimp [c]
              ring
    _ = X ^ 2 - C ((2 : ℝ) * c) * X + C (c ^ 2) + C (Real.sqrt (v - u ^ 2 / 4)) ^ 2 := by
          simp [pow_two, add_assoc, add_left_comm, add_comm]
    _ = (X - C c) ^ 2 + C (Real.sqrt (v - u ^ 2 / 4)) ^ 2 := by
          rw [hsquare]

lemma exists_sq_add_sq_mul_of_exists_sq_add_sq {p q : Poly}
    (hp : ∃ a b : Poly, p = a ^ 2 + b ^ 2)
    (hq : ∃ a b : Poly, q = a ^ 2 + b ^ 2) :
    ∃ a b : Poly, p * q = a ^ 2 + b ^ 2 := by
  rcases hp with ⟨a, b, rfl⟩
  rcases hq with ⟨c, d, rfl⟩
  exact _root_.sq_add_sq_mul rfl rfl

lemma eval_pos_of_isMonicOfDegree_two_of_no_real_root {f : Poly}
    (hf : Polynomial.IsMonicOfDegree f 2)
    (hroot : ∀ x : ℝ, f.eval x ≠ 0) :
    ∀ x : ℝ, 0 < f.eval x := by
  rw [Polynomial.isMonicOfDegree_two_iff'] at hf
  rcases hf with ⟨u, v, rfl⟩
  let c : ℝ := u / 2
  have hconst : 0 < v - u ^ 2 / 4 := by
    by_contra h
    have hle : v - u ^ 2 / 4 ≤ 0 := le_of_not_gt h
    by_cases hzero : v - u ^ 2 / 4 = 0
    · have hcalc : ((X ^ 2 - C u * X + C v : Poly).eval (u / 2)) = v - u ^ 2 / 4 := by
        simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
        ring_nf
      exact hroot c (by simpa [c, hzero] using hcalc)
    · have hlt : v - u ^ 2 / 4 < 0 := lt_of_le_of_ne hle hzero
      let y : ℝ := Real.sqrt (-(v - u ^ 2 / 4))
      have hy2 : y ^ 2 = -(v - u ^ 2 / 4) := by
        dsimp [y]
        exact Real.sq_sqrt (by linarith)
      have hcalc : ((X ^ 2 - C u * X + C v : Poly).eval (c + y)) = y ^ 2 + (v - u ^ 2 / 4) := by
        dsimp [c]
        simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
        ring_nf
      apply hroot (c + y)
      rw [hcalc, hy2]
      ring
  intro x
  have hcalc : ((X ^ 2 - C u * X + C v : Poly).eval x) = (x - c) ^ 2 + (v - u ^ 2 / 4) := by
    dsimp [c]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
    ring_nf
  rw [hcalc]
  nlinarith [sq_nonneg (x - c), hconst]

lemma eval_nonneg_of_nonneg_off_singleton {p : Poly} {a : ℝ}
    (hp : ∀ x : ℝ, x ≠ a → 0 ≤ p.eval x) :
    0 ≤ p.eval a := by
  by_contra hneg
  have ha : p.eval a < 0 := lt_of_not_ge hneg
  let s : Set ℝ := {x | p.eval x < 0}
  have hs_open : IsOpen s := isOpen_lt (Polynomial.continuous p) continuous_const
  have hs_mem : a ∈ s := ha
  rcases Metric.isOpen_iff.mp hs_open a hs_mem with ⟨ε, hε, hball⟩
  have hx : a + ε / 2 ≠ a := by linarith
  have hxmem : a + ε / 2 ∈ Metric.ball a ε := by
    have hhalf : 0 < ε / 2 := by linarith
    have hεabs : |ε| = ε := abs_of_pos hε
    have habs : |ε| / 2 < ε := by
      rw [hεabs]
      linarith
    simpa [Metric.mem_ball] using habs
  have hlt : p.eval (a + ε / 2) < 0 := hball hxmem
  exact (not_lt_of_ge (hp _ hx)) hlt

lemma exists_nonneg_factor_of_dvd_sq_of_eval_nonneg {p : Poly} {a : ℝ}
    (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (hdiv : (X - C a) ^ 2 ∣ p) :
    ∃ r : Poly, p = (X - C a) ^ 2 * r ∧ ∀ x : ℝ, 0 ≤ r.eval x := by
  rcases hdiv with ⟨r, rfl⟩
  refine ⟨r, rfl, ?_⟩
  intro x
  by_cases hx : x = a
  · rw [hx]
    apply eval_nonneg_of_nonneg_off_singleton (a := a)
    intro y hy
    have hsqpos : 0 < ((X - C a) ^ 2).eval y := by
      have hneq : y - a ≠ 0 := sub_ne_zero.mpr hy
      simpa [Polynomial.eval_pow, Polynomial.eval_sub, sq_pos_iff] using sq_pos_of_ne_zero hneq
    have hmul_nonneg : 0 ≤ (((X - C a) ^ 2) * r).eval y := hp y
    rw [Polynomial.eval_mul] at hmul_nonneg
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hmul_nonneg) hsqpos
  · have hsqpos : 0 < ((X - C a) ^ 2).eval x := by
      have hneq : x - a ≠ 0 := sub_ne_zero.mpr hx
      simpa [Polynomial.eval_pow, Polynomial.eval_sub, sq_pos_iff] using sq_pos_of_ne_zero hneq
    have hmul_nonneg : 0 ≤ (((X - C a) ^ 2) * r).eval x := hp x
    rw [Polynomial.eval_mul] at hmul_nonneg
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hmul_nonneg) hsqpos

lemma exists_sq_add_sq_of_monic_of_nonneg {p : Poly}
    (hm : p.Monic) (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∃ a b : Poly, p = a ^ 2 + b ^ 2 := by
  let P : ℕ → Prop := fun n =>
    ∀ p : Poly, p.Monic → (∀ x : ℝ, 0 ≤ p.eval x) → p.natDegree = n →
      ∃ a b : Poly, p = a ^ 2 + b ^ 2
  have hmain : ∀ n : ℕ, P n := by
    intro n
    refine Nat.case_strong_induction_on n ?_ ?_
    · intro p hm _ hdeg
      have hmono0 : Polynomial.IsMonicOfDegree p 0 := ⟨hdeg, hm⟩
      have hp1 : p = 1 := (Polynomial.isMonicOfDegree_zero_iff).mp hmono0
      refine ⟨1, 0, ?_⟩
      simp [hp1]
    · intro n ih p hm hp hdeg
      rcases n with _ | n
      · exfalso
        exact natDegree_ne_one_of_nonneg hm.ne_zero hp hdeg
      · have hmono2 : Polynomial.IsMonicOfDegree p (n + 2) := ⟨hdeg, hm⟩
        by_cases hroot : ∃ a : ℝ, p.eval a = 0
        · rcases hroot with ⟨a, ha⟩
          have hmult : 1 < rootMultiplicity a p :=
            one_lt_rootMultiplicity_of_nonneg_of_isRoot hm.ne_zero hp ha
          have hdiv2 : (X - C a) ^ 2 ∣ p := by
            exact
              (Polynomial.le_rootMultiplicity_iff hm.ne_zero).mp
                (by omega : 2 ≤ rootMultiplicity a p)
          rcases exists_nonneg_factor_of_dvd_sq_of_eval_nonneg hp hdiv2 with ⟨r, hr, hr_nonneg⟩
          have hfac : Polynomial.IsMonicOfDegree ((X - C a) ^ 2) 2 := by
            simpa [pow_two] using (Polynomial.isMonicOfDegree_X_sub_one (R := ℝ) a).pow 2
          have hr_deg_monic : Polynomial.IsMonicOfDegree r n := by
            have hprod : Polynomial.IsMonicOfDegree (((X - C a) ^ 2) * r) (2 + n) := by
              simpa [hr, add_comm] using hmono2
            exact hfac.of_mul_left hprod
          have hr_sq : ∃ u v : Poly, r = u ^ 2 + v ^ 2 := by
            exact ih n (Nat.le_succ n) r hr_deg_monic.monic hr_nonneg hr_deg_monic.natDegree_eq
          have hfac_sq : ∃ u v : Poly, (X - C a) ^ 2 = u ^ 2 + v ^ 2 := by
            refine ⟨X - C a, 0, by simp⟩
          rcases exists_sq_add_sq_mul_of_exists_sq_add_sq hfac_sq hr_sq with ⟨u, v, huv⟩
          refine ⟨u, v, ?_⟩
          simpa [hr] using huv
        · rcases Polynomial.IsMonicOfDegree.eq_isMonicOfDegree_two_mul_isMonicOfDegree hmono2 with
            ⟨q, r, hq, hr, hqr⟩
          have hq_no_root : ∀ x : ℝ, q.eval x ≠ 0 := by
            intro x hx
            apply hroot
            refine ⟨x, ?_⟩
            rw [hqr, Polynomial.eval_mul, hx, zero_mul]
          have hq_pos : ∀ x : ℝ, 0 < q.eval x :=
            eval_pos_of_isMonicOfDegree_two_of_no_real_root hq hq_no_root
          have hr_nonneg : ∀ x : ℝ, 0 ≤ r.eval x := by
            rcases exists_nonneg_factor_of_dvd_of_eval_pos hp hq_pos ⟨r, hqr⟩ with ⟨s, hs, hsnonneg⟩
            have hs_eq : s = r := by
              apply mul_left_cancel₀ hq.ne_zero
              simpa [hqr] using hs.symm
            simpa [hs_eq] using hsnonneg
          have hq_sq : ∃ u v : Poly, q = u ^ 2 + v ^ 2 :=
            exists_sq_add_sq_of_isMonicOfDegree_two_of_eval_pos hq hq_pos
          have hr_sq : ∃ u v : Poly, r = u ^ 2 + v ^ 2 := by
            exact ih n (Nat.le_succ n) r hr.monic hr_nonneg hr.natDegree_eq
          rcases exists_sq_add_sq_mul_of_exists_sq_add_sq hq_sq hr_sq with ⟨u, v, huv⟩
          refine ⟨u, v, ?_⟩
          simpa [hqr] using huv
  exact hmain p.natDegree p hm hp rfl

lemma leadingCoeff_pos_of_nonneg {p : Poly} (hp0 : p ≠ 0)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    0 < p.leadingCoeff := by
  by_cases hdeg0 : p.degree ≤ 0
  · have hnat : p.natDegree = 0 := by
      exact Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hdeg0
    rcases Polynomial.natDegree_eq_zero.mp hnat with ⟨c, rfl⟩
    have hc0 : c ≠ 0 := by
      intro hc
      apply hp0
      simp [hc]
    simpa using lt_of_le_of_ne (hp 0) (by simpa using hc0.symm)
  · have hdeg : 0 < p.degree := lt_of_not_ge hdeg0
    have hnonneg : 0 ≤ p.leadingCoeff := by
      by_contra hneg
      have hbot : Filter.Tendsto (fun x => p.eval x) Filter.atTop Filter.atBot :=
        Polynomial.tendsto_atBot_of_leadingCoeff_nonpos (P := p) hdeg (le_of_not_ge hneg)
      have hlt : ∀ᶠ x in Filter.atTop, p.eval x < 0 := hbot (Filter.Iio_mem_atBot (0 : ℝ))
      rcases (Filter.eventually_atTop.mp hlt) with ⟨x0, hx0⟩
      exact (not_lt_of_ge (hp x0)) (hx0 x0 le_rfl)
    exact lt_of_le_of_ne hnonneg (Polynomial.leadingCoeff_ne_zero.mpr hp0).symm

lemma exists_sq_add_sq_of_nonneg {p : Poly}
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∃ a b : Poly, p = a ^ 2 + b ^ 2 := by
  by_cases hp0 : p = 0
  · refine ⟨0, 0, by simp [hp0]⟩
  · by_cases hdeg0 : p.degree ≤ 0
    · have hnat : p.natDegree = 0 := by
        exact Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hdeg0
      rcases Polynomial.natDegree_eq_zero.mp hnat with ⟨c, rfl⟩
      refine ⟨C (Real.sqrt c), 0, ?_⟩
      have hc : 0 ≤ c := by simpa using hp 0
      calc
        C c = C ((Real.sqrt c) ^ 2) := by rw [Real.sq_sqrt hc]
        _ = C (Real.sqrt c) * C (Real.sqrt c) := by simp [pow_two, map_mul]
        _ = C (Real.sqrt c) ^ 2 + 0 ^ 2 := by simp [pow_two]
    · have hlc : 0 < p.leadingCoeff := leadingCoeff_pos_of_nonneg hp0 hp
      let q : Poly := p * C p.leadingCoeff⁻¹
      have hq_monic : q.Monic := by
        dsimp [q]
        exact Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one (by
          field_simp [show p.leadingCoeff ≠ 0 by exact Polynomial.leadingCoeff_ne_zero.mpr hp0])
      have hq_nonneg : ∀ x : ℝ, 0 ≤ q.eval x := by
        intro x
        rw [show q.eval x = p.eval x * p.leadingCoeff⁻¹ by
          simp [q, Polynomial.eval_mul]]
        exact mul_nonneg (hp x) (inv_nonneg.mpr hlc.le)
      rcases exists_sq_add_sq_of_monic_of_nonneg hq_monic hq_nonneg with ⟨a, b, hab⟩
      have hconst : ∃ u v : Poly, C p.leadingCoeff = u ^ 2 + v ^ 2 := by
        refine ⟨C (Real.sqrt p.leadingCoeff), 0, ?_⟩
        calc
          C p.leadingCoeff = C ((Real.sqrt p.leadingCoeff) ^ 2) := by rw [Real.sq_sqrt hlc.le]
          _ = C (Real.sqrt p.leadingCoeff) ^ 2 := by simp [pow_two, map_mul]
          _ = C (Real.sqrt p.leadingCoeff) ^ 2 + 0 ^ 2 := by simp
      have hq : C p.leadingCoeff * q = p := by
        calc
          C p.leadingCoeff * q
              = C p.leadingCoeff * (p * C p.leadingCoeff⁻¹) := by rfl
          _ = p * (C p.leadingCoeff * C p.leadingCoeff⁻¹) := by ring
          _ = p * 1 := by rw [← Polynomial.C_mul, mul_inv_cancel₀ hlc.ne', Polynomial.C_1]
          _ = p := by simp
      rcases exists_sq_add_sq_mul_of_exists_sq_add_sq hconst ⟨a, b, hab⟩ with ⟨u, v, huv⟩
      refine ⟨u, v, ?_⟩
      simpa [hq] using huv

lemma exists_coprime_sq_add_sq_factor {p : Poly}
    (hp : ∃ a b : Poly, p = a ^ 2 + b ^ 2) :
    ∃ g a b : Poly, p = g ^ 2 * (a ^ 2 + b ^ 2) ∧ IsCoprime a b := by
  rcases hp with ⟨u, v, hp⟩
  rcases extract_gcd u v with ⟨u', v', hu, hv, hunit⟩
  let g : Poly := gcd u v
  have hu' : u = g * u' := by simpa [g] using hu
  have hv' : v = g * v' := by simpa [g] using hv
  refine ⟨g, u', v', ?_, ?_⟩
  · calc
      p = u ^ 2 + v ^ 2 := hp
      _ = (g * u') ^ 2 + (g * v') ^ 2 := by rw [hu', hv']
      _ = g ^ 2 * (u' ^ 2 + v' ^ 2) := by ring
  · exact (isRelPrime_iff_isCoprime).mp <| (gcd_isUnit_iff_isRelPrime).mp hunit

lemma exists_bezout_coprime_sq_add_sq_factor {p : Poly}
    (hp : ∃ a b : Poly, p = a ^ 2 + b ^ 2) :
    ∃ g a b u v : Poly,
      p = g ^ 2 * (a ^ 2 + b ^ 2) ∧
      u * a + v * b = 1 := by
  rcases exists_coprime_sq_add_sq_factor hp with ⟨g, a, b, hp, hcop⟩
  rcases hcop with ⟨u, v, huv⟩
  exact ⟨g, a, b, u, v, hp, huv⟩

end MatrixSOS
