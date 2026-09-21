/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.FieldTheory.Laurent
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.LaurentSeries

/-!
# Ordered extensions used to test rational-function positivity
-/

open Filter Polynomial
noncomputable section


namespace MatrixSOS

theorem negative_lexLaurentSeries_of_negative_trailingCoeff
    {p : Poly}
    (hp : p.trailingCoeff < 0) :
    toLex (((p : PowerSeries ℝ) : LaurentSeries ℝ)) < 0 := by
  rw [← HahnSeries.leadingCoeff_neg_iff]
  let s : LaurentSeries ℝ := ((p : PowerSeries ℝ) : LaurentSeries ℝ)
  have hp0 : p ≠ 0 := by
    intro hp0
    simpa [hp0] using hp.ne
  have hne : s ≠ 0 := by
    intro hs0
    have hcoeff : s.coeff p.natTrailingDegree = 0 := by simp [s, hs0]
    have : p.trailingCoeff = 0 := by
      simpa [s, Polynomial.trailingCoeff, LaurentSeries.coeff_coe_powerSeries] using hcoeff
    exact hp.ne this
  have horder : s.orderTop = p.natTrailingDegree := by
    apply HahnSeries.orderTop_eq_of_le
    · have hcoeffne : s.coeff p.natTrailingDegree ≠ 0 := by
        simpa [s, Polynomial.trailingCoeff, LaurentSeries.coeff_coe_powerSeries] using
          (Polynomial.coeff_natTrailingDegree_ne_zero.2 hp0)
      simpa using hcoeffne
    · intro j hj
      by_cases hjnonneg : 0 ≤ j
      · rw [Int.eq_natAbs_of_nonneg hjnonneg]
        exact_mod_cast Polynomial.natTrailingDegree_le_of_ne_zero
          (by
            have hj' : (((p : PowerSeries ℝ) : LaurentSeries ℝ).coeff j) ≠ 0 := by
              simpa [s] using hj
            rw [PowerSeries.coeff_coe, ite_eq_right (show ¬ j < 0 from not_lt.mpr hjnonneg)] at hj'
            simpa using hj')
      · exfalso
        have hj' : (((p : PowerSeries ℝ) : LaurentSeries ℝ).coeff j) ≠ 0 := by
          simpa [s] using hj
        rw [PowerSeries.coeff_coe, ite_eq_left (lt_of_not_ge hjnonneg)] at hj'
        exact hj' rfl
  have hsneg : s.leadingCoeff < 0 := by
    have htop : s.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.mpr hne
    have huntop : s.orderTop.untop htop = p.natTrailingDegree := (WithTop.untop_eq_iff htop).mpr horder
    rw [HahnSeries.leadingCoeff_of_ne_zero hne, huntop]
    simpa [s, Polynomial.trailingCoeff, LaurentSeries.coeff_coe_powerSeries] using hp
  simpa [s, ofLex_toLex] using hsneg

theorem negative_lexLaurentSeries_taylor_of_negative_real_poly_value
    {p : Poly} {x : ℝ}
    (hpx : p.eval x < 0) :
    toLex ((((p.comp (X + C x) : Poly) : PowerSeries ℝ) : LaurentSeries ℝ)) < 0 := by
  have hcoeff0 :
      (p.comp (X + C x) : Poly).coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]
    exact hpx.ne
  have htrail :
      (p.comp (X + C x) : Poly).trailingCoeff < 0 := by
    rw [Polynomial.trailingCoeff_eq_coeff_zero hcoeff0]
    simpa [Polynomial.coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]
      using hpx
  simpa using negative_lexLaurentSeries_of_negative_trailingCoeff htrail

end MatrixSOS
