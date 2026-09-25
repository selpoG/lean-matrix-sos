/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.HalfLine
import MatrixSOS.Proof.Interval.Certificates

/-!
# Normalized interval sum-of-squares certificates
-/

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS

def unitIntervalDehomPoly (d : ℕ) (p : Poly) : Poly :=
  ∑ k ∈ Finset.range (d + 1),
    Polynomial.C (p.coeff k) * Polynomial.X ^ k * (1 - Polynomial.X) ^ (d - k)

def unitIntervalDehomMat {ι κ : Type*} (d : ℕ)
    (A : Matrix ι κ Poly) : Matrix ι κ Poly :=
  fun i j => unitIntervalDehomPoly d (A i j)

lemma natDegree_unitIntervalDehomPoly_le (d : ℕ) (p : Poly) :
    (unitIntervalDehomPoly d p).natDegree ≤ d := by
  rw [unitIntervalDehomPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.range (d + 1))
    (f := fun k => Polynomial.C (p.coeff k) * Polynomial.X ^ k * (1 - Polynomial.X) ^ (d - k))
    ?_
  intro k hk
  rw [Finset.mem_range] at hk
  have hkD : k ≤ d := by omega
  have hlin : (1 - Polynomial.X : Poly).natDegree ≤ 1 := by
    compute_degree
  refine le_trans Polynomial.natDegree_mul_le ?_
  have hleft : (Polynomial.C (p.coeff k) * Polynomial.X ^ k).natDegree ≤ k :=
    Polynomial.natDegree_C_mul_X_pow_le (p.coeff k) k
  have hright : ((1 - Polynomial.X : Poly) ^ (d - k)).natDegree ≤ d - k := by
    simpa using Polynomial.natDegree_pow_le_of_le (d - k) hlin
  exact (add_le_add hleft hright).trans (by omega)

lemma natDegree_unitIntervalDehomMat_le {ι κ : Type*} {d : ℕ}
    (A : Matrix ι κ Poly) :
    ∀ i j, natDegree (unitIntervalDehomMat d A i j) ≤ d := by
  intro i j
  exact natDegree_unitIntervalDehomPoly_le d (A i j)

def intervalLeftChartPoly (D : ℕ) (p : Poly) : Poly :=
  ∑ k ∈ Finset.range (D + 1),
    Polynomial.C (p.coeff k) * Polynomial.X ^ k * (1 + Polynomial.X) ^ (D - k)

def intervalLeftChartMat {ι κ : Type*} (D : ℕ)
    (A : Matrix ι κ Poly) : Matrix ι κ Poly :=
  fun i j => intervalLeftChartPoly D (A i j)

lemma natDegree_intervalLeftChartPoly_le (D : ℕ) (p : Poly) :
    (intervalLeftChartPoly D p).natDegree ≤ D := by
  rw [intervalLeftChartPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.range (D + 1))
    (f := fun k => Polynomial.C (p.coeff k) * Polynomial.X ^ k * (1 + Polynomial.X) ^ (D - k))
    ?_
  intro k hk
  rw [Finset.mem_range] at hk
  have hkD : k ≤ D := by omega
  have hlin : (1 + Polynomial.X : Poly).natDegree ≤ 1 := by
    rw [show (1 + Polynomial.X : Poly) = Polynomial.X + Polynomial.C 1 by
      simp [add_comm]]
    rw [Polynomial.natDegree_X_add_C]
  refine le_trans Polynomial.natDegree_mul_le ?_
  have hleft : (Polynomial.C (p.coeff k) * Polynomial.X ^ k).natDegree ≤ k :=
    Polynomial.natDegree_C_mul_X_pow_le (p.coeff k) k
  have hright : ((1 + Polynomial.X : Poly) ^ (D - k)).natDegree ≤ D - k := by
    simpa only [mul_one] using Polynomial.natDegree_pow_le_of_le (D - k) hlin
  exact (add_le_add hleft hright).trans (by omega)

lemma natDegree_intervalLeftChartMat_le {m D : ℕ} {M : PolyMat m} :
    ∀ i j, natDegree (intervalLeftChartMat D M i j) ≤ D := by
  intro i j
  exact natDegree_intervalLeftChartPoly_le D (M i j)

lemma natDegree_transpose_mul_le
    {m ℓ d : ℕ} {A : Matrix (Fin ℓ) (Fin m) Poly}
    (hA : ∀ i j, natDegree (A i j) ≤ d) :
    ∀ i j, natDegree ((A.transpose * A) i j) ≤ 2 * d := by
  intro i j
  rw [Matrix.mul_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.univ)
    (f := fun k => A.transpose i k * A k j)
    ?_
  intro k hk
  refine le_trans Polynomial.natDegree_mul_le ?_
  have hleft : natDegree (A.transpose i k) ≤ d := by
    simpa using hA k i
  exact (add_le_add hleft (hA k j)).trans (by omega)

lemma eval_eq_sum_range_of_natDegree_le {p : Poly} {D : ℕ}
    (h : p.natDegree ≤ D) (x : ℝ) :
    p.eval x = ∑ k ∈ Finset.range (D + 1), p.coeff k * x ^ k := by
  rw [Polynomial.eval_eq_sum_range]
  refine Finset.sum_subset ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  · intro k _ hk
    have hkgt : p.natDegree < k := by
      rw [Finset.mem_range] at hk
      omega
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hkgt]

lemma intervalLeftChartPoly_eval
    {D : ℕ} {p : Poly} (hdeg : p.natDegree ≤ D)
    {u : ℝ} (hden : 1 + u ≠ 0) :
    (intervalLeftChartPoly D p).eval u =
      (1 + u) ^ D * p.eval (u / (1 + u)) := by
  rw [intervalLeftChartPoly, Polynomial.eval_finsetSum,
    eval_eq_sum_range_of_natDegree_le hdeg]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Finset.mem_range] at hk
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_one]
  have hterm :
      (1 + u) ^ D * ((u / (1 + u)) ^ k) =
        u ^ k * (1 + u) ^ (D - k) := by
    have hkD : k ≤ D := by omega
    rw [div_pow]
    field_simp [hden]
    have hpow : (1 + u) ^ k * (1 + u) ^ (D - k) = (1 + u) ^ D := by
      rw [← pow_add]
      congr 1
      omega
    calc
      (1 + u) ^ D * u ^ k = u ^ k * (1 + u) ^ D := by ring
      _ = u ^ k * ((1 + u) ^ k * (1 + u) ^ (D - k)) := by rw [hpow]
      _ = u ^ k * (1 + u) ^ k * (1 + u) ^ (D - k) := by ring
  calc
    p.coeff k * u ^ k * (1 + u) ^ (D - k)
        = p.coeff k * ((1 + u) ^ D * (u / (1 + u)) ^ k) := by rw [hterm]; ring
    _ = (1 + u) ^ D * (p.coeff k * (u / (1 + u)) ^ k) := by ring

lemma unitIntervalDehomPoly_eval
    {d : ℕ} {p : Poly} (hdeg : p.natDegree ≤ d)
    {x : ℝ} (hden : 1 - x ≠ 0) :
    (unitIntervalDehomPoly d p).eval x =
      (1 - x) ^ d * p.eval (x / (1 - x)) := by
  rw [unitIntervalDehomPoly, Polynomial.eval_finsetSum,
    eval_eq_sum_range_of_natDegree_le hdeg]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Finset.mem_range] at hk
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]
  have hterm :
      (1 - x) ^ d * ((x / (1 - x)) ^ k) =
        x ^ k * (1 - x) ^ (d - k) := by
    have hkD : k ≤ d := by omega
    rw [div_pow]
    field_simp [hden]
    have hpow : (1 - x) ^ k * (1 - x) ^ (d - k) = (1 - x) ^ d := by
      rw [← pow_add]
      congr 1
      omega
    calc
      (1 - x) ^ d * x ^ k = x ^ k * (1 - x) ^ d := by ring
      _ = x ^ k * ((1 - x) ^ k * (1 - x) ^ (d - k)) := by rw [hpow]
      _ = x ^ k * (1 - x) ^ k * (1 - x) ^ (d - k) := by ring
  calc
    p.coeff k * x ^ k * (1 - x) ^ (d - k)
        = p.coeff k * ((1 - x) ^ d * (x / (1 - x)) ^ k) := by rw [hterm]; ring
    _ = (1 - x) ^ d * (p.coeff k * (x / (1 - x)) ^ k) := by ring

lemma mapEval_intervalLeftChartMat
    {m D : ℕ} {M : PolyMat m}
    (hdeg : ∀ i j, natDegree (M i j) ≤ D)
    {u : ℝ} (hden : 1 + u ≠ 0) :
    mapEval u (intervalLeftChartMat D M) =
      ((1 + u) ^ D) • mapEval (u / (1 + u)) M := by
  apply Matrix.ext
  intro i j
  simp [mapEval, intervalLeftChartMat, intervalLeftChartPoly_eval (hdeg i j) hden]

lemma mapEval_unitIntervalDehomMat
    {ι κ : Type*} {d : ℕ} {A : Matrix ι κ Poly}
    (hdeg : ∀ i j, natDegree (A i j) ≤ d)
    {x : ℝ} (hden : 1 - x ≠ 0) :
    mapEval x (unitIntervalDehomMat d A) =
      ((1 - x) ^ d) • mapEval (x / (1 - x)) A := by
  ext i j
  simp [mapEval, unitIntervalDehomMat, unitIntervalDehomPoly_eval (hdeg i j) hden]

lemma intervalLeftChartMat_isSymm {m D : ℕ} {M : PolyMat m}
    (hM : M.IsSymm) :
    (intervalLeftChartMat D M).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  exact congrArg (intervalLeftChartPoly D) (hM.apply i j)

lemma nonnegOnNN_intervalLeftChartMat_of_nonnegOnIcc
    {m D : ℕ} {M : PolyMat m}
    (hdeg : ∀ i j, natDegree (M i j) ≤ D)
    (hM : NonnegOnIcc 0 1 M) :
    NonnegOnNN (intervalLeftChartMat D M) := by
  intro u hu
  have hden_pos : 0 < 1 + u := by linarith
  have ht0 : 0 ≤ u / (1 + u) := div_nonneg hu hden_pos.le
  have ht1 : u / (1 + u) ≤ 1 := by
    rw [div_le_one hden_pos]
    linarith
  rw [mapEval_intervalLeftChartMat hdeg hden_pos.ne']
  exact (hM (u / (1 + u)) ht0 ht1).smul (by positivity)

lemma unitInterval_lukacs_eq_of_left_chart_sos
    {m d ℓ₁ ℓ₂ : ℕ} (hd : 0 < d) (M : PolyMat m)
    (A : Matrix (Fin ℓ₁) (Fin m) Poly)
    (B : Matrix (Fin ℓ₂) (Fin m) Poly)
    (hMdeg : ∀ i j, natDegree (M i j) ≤ 2 * d)
    (hAdeg : ∀ i j, natDegree (A i j) ≤ d)
    (hBdeg : ∀ i j, natDegree (B i j) ≤ d - 1)
    (hchart : intervalLeftChartMat (2 * d) M = SOSForm A B) :
    M =
      (unitIntervalDehomMat d A).transpose * unitIntervalDehomMat d A +
      ((Polynomial.X * (1 - Polynomial.X) : Poly) •
        ((unitIntervalDehomMat (d - 1) B).transpose *
          unitIntervalDehomMat (d - 1) B) : PolyMat m) := by
  apply Matrix.ext
  intro i j
  refine Polynomial.eq_of_infinite_eval_eq (R := ℝ) _ _ ?_
  refine (Set.finite_singleton (1 : ℝ)).infinite_compl.mono ?_
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  simp only [Set.mem_ofPred_eq]
  have hx' : 1 ≠ x := fun h => hx h.symm
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr hx'
  let u : ℝ := x / (1 - x)
  have hu_den : 1 + u ≠ 0 := by
    have hcalc : 1 + u = (1 : ℝ) / (1 - x) := by
      dsimp [u]
      field_simp [hden]
      ring
    rw [hcalc]
    exact one_div_ne_zero hden
  have hu_arg : u / (1 + u) = x := by
    dsimp [u]
    field_simp [hden]
    ring
  have hscale : (1 - x) ^ (2 * d) * (1 + u) ^ (2 * d) = 1 := by
    have hcalc : 1 + u = (1 : ℝ) / (1 - x) := by
      dsimp [u]
      field_simp [hden]
      ring
    rw [hcalc, one_div, ← mul_pow]
    simp [hden]
  have hchart_eval := congrArg (fun N => mapEval u N) hchart
  change mapEval u (intervalLeftChartMat (2 * d) M) = mapEval u (SOSForm A B) at hchart_eval
  rw [mapEval_intervalLeftChartMat hMdeg hu_den, hu_arg] at hchart_eval
  have hentry := congrArg (fun N : Matrix (Fin m) (Fin m) ℝ => N i j) hchart_eval
  have hAeval := mapEval_unitIntervalDehomMat (A := A) hAdeg hden
  have hBeval := mapEval_unitIntervalDehomMat (A := B) hBdeg hden
  change (mapEval x M) i j =
    (mapEval x
      ((unitIntervalDehomMat d A).transpose * unitIntervalDehomMat d A +
      ((Polynomial.X * (1 - Polynomial.X) : Poly) •
        ((unitIntervalDehomMat (d - 1) B).transpose *
          unitIntervalDehomMat (d - 1) B) : PolyMat m))) i j
  rw [mapEval_add, mapEval_mul, mapEval_transpose, mapEval_smul,
    mapEval_mul, mapEval_transpose, hAeval, hBeval]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Matrix.add_apply, Matrix.smul_apply]
  simp only [SOSForm, mapEval_add, mapEval_mul, mapEval_transpose, mapEval_smul,
    Polynomial.eval_X, Matrix.add_apply, Matrix.smul_apply] at hentry
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_apply]
  simp only [smul_eq_mul] at hentry ⊢
  let aterm : ℝ :=
    (((mapEval (x / (1 - x)) A).transpose * mapEval (x / (1 - x)) A) i j)
  let bterm : ℝ :=
    (((mapEval (x / (1 - x)) B).transpose * mapEval (x / (1 - x)) B) i j)
  have hentry_scalar :
      (1 + u) ^ (2 * d) * mapEval x M i j = aterm + u * bterm := by
    simpa [aterm, bterm, u] using hentry
  have hpowA : (1 - x) ^ d * (1 - x) ^ d = (1 - x) ^ (2 * d) := by
    rw [← pow_add]
    congr 1
    omega
  have hpowB :
      x * (1 - x) * ((1 - x) ^ (d - 1) * (1 - x) ^ (d - 1)) =
        (1 - x) ^ (2 * d) * u := by
    dsimp [u]
    field_simp [hden]
    calc
      x * (1 - x) ^ 2 * ((1 - x) ^ (d - 1)) ^ 2
          = x * ((1 - x) ^ 2 * ((1 - x) ^ (d - 1) * (1 - x) ^ (d - 1))) := by
              rw [pow_two]
              ring
      _ = x * (1 - x) ^ (2 * d) := by
            rw [← pow_add, ← pow_add]
            rw [show 2 + ((d - 1) + (d - 1)) = 2 * d by omega]
  calc
    mapEval x M i j
        = (1 - x) ^ (2 * d) * ((1 + u) ^ (2 * d) * mapEval x M i j) := by
            rw [← mul_assoc, hscale]
            ring
    _ = (1 - x) ^ (2 * d) * (aterm + u * bterm) := by rw [hentry_scalar]
    _ =
        ((1 - x) ^ d * (1 - x) ^ d) * aterm +
          (x * (1 - x) * ((1 - x) ^ (d - 1) * (1 - x) ^ (d - 1))) * bterm := by
            rw [hpowA, hpowB]
            ring

theorem unitInterval_lukacsSOS_bounded_even
    {m d : ℕ} (hd : 0 < d) (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d)
    (hsymm : M.IsSymm) :
    NonnegOnIcc 0 1 M → IccLukacsCertificateBoundedEven d 0 1 M := by
  intro hM
  have hleftNN := nonnegOnNN_intervalLeftChartMat_of_nonnegOnIcc hdeg hM
  have hleftSymm := intervalLeftChartMat_isSymm (D := 2 * d) hsymm
  rcases halfLine_sos_bounded (intervalLeftChartMat (2 * d) M)
      (d := 2 * d) natDegree_intervalLeftChartMat_le hleftSymm hleftNN with
    ⟨A, B, hAdeg, hBdeg, hAB⟩
  let A' : Matrix (Fin (m + 1)) (Fin m) Poly := unitIntervalDehomMat d A
  let B' : Matrix (Fin (m + 1)) (Fin m) Poly := unitIntervalDehomMat (d - 1) B
  have hAdeg' : ∀ i j, natDegree (A i j) ≤ d := by
    intro i j
    exact (hAdeg i j).trans (by dsimp [evenPartDegreeBound]; omega)
  have hBdeg' : ∀ i j, natDegree (B i j) ≤ d - 1 := by
    intro i j
    exact (hBdeg i j).trans (by dsimp [oddPartDegreeBound]; omega)
  refine ⟨A', B', ?_, ?_, ?_⟩
  · exact natDegree_unitIntervalDehomMat_le A
  · exact natDegree_unitIntervalDehomMat_le B
  · have hEq := unitInterval_lukacs_eq_of_left_chart_sos
      hd M A B hdeg hAdeg' hBdeg' hAB
    simpa [A', B', intervalWeight] using hEq

lemma leftChart_sos_odd_first_factor_degree_drop
    {m d ℓ₁ ℓ₂ : ℕ} {M : PolyMat m}
    {A : Matrix (Fin ℓ₁) (Fin m) Poly}
    {B : Matrix (Fin ℓ₂) (Fin m) Poly}
    (hAdeg : ∀ i j, natDegree (A i j) ≤ d + 1)
    (hBdeg : ∀ i j, natDegree (B i j) ≤ d)
    (hchart : intervalLeftChartMat (2 * d + 1) M = SOSForm A B) :
    ∀ i j, natDegree (A i j) ≤ d := by
  intro i j
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hn' : d + 1 ≤ n := by omega
  suffices htop : (A i j).coeff (d + 1) = 0 by
    by_cases hnEq : n = d + 1
    · simpa [hnEq] using htop
    · have hgt : d + 1 < n := lt_of_le_of_ne hn' (Ne.symm hnEq)
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hAdeg i j) hgt)
  have hentry := congrArg
    (fun N : PolyMat m => (N j j).coeff (2 * d + 2)) hchart
  have hleft_zero :
      (intervalLeftChartMat (2 * d + 1) M j j).coeff (2 * d + 2) = 0 := by
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_intervalLeftChartPoly_le (2 * d + 1) (M j j)) (by omega))
  have hBprod :
      natDegree ((B.transpose * B) j j) ≤ 2 * d :=
    natDegree_transpose_mul_le hBdeg j j
  have hB_coeff_zero :
      ((B.transpose * B) j j).coeff (2 * d + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hBprod (by omega))
  have hATA_zero :
      ((A.transpose * A) j j).coeff (2 * d + 2) = 0 := by
    change (intervalLeftChartMat (2 * d + 1) M j j).coeff (2 * d + 2) =
      (SOSForm A B j j).coeff (2 * d + 2) at hentry
    rw [hleft_zero] at hentry
    simpa [SOSForm, hB_coeff_zero] using hentry.symm
  have hsum :
      (∑ k : Fin ℓ₁, (A k j).coeff (d + 1) * (A k j).coeff (d + 1)) = 0 := by
    rw [Matrix.mul_apply, Polynomial.finsetSum_coeff] at hATA_zero
    simp only [Matrix.transpose_apply] at hATA_zero
    calc
      (∑ k : Fin ℓ₁, (A k j).coeff (d + 1) * (A k j).coeff (d + 1))
          = ∑ k : Fin ℓ₁, (A k j * A k j).coeff (2 * d + 2) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [show 2 * d + 2 = (d + 1) + (d + 1) by omega]
              exact (Polynomial.coeff_mul_add_eq_of_natDegree_le
                (hAdeg k j) (hAdeg k j)).symm
      _ = 0 := hATA_zero
  have hterm_zero :
      (A i j).coeff (d + 1) * (A i j).coeff (d + 1) = 0 := by
    have hfun := (Fintype.sum_eq_zero_iff_of_nonneg
      (fun k => mul_self_nonneg ((A k j).coeff (d + 1)))).1 hsum
    exact congrFun hfun i
  exact sq_eq_zero_iff.mp (by simpa [pow_two] using hterm_zero)

lemma unitInterval_lukacsOddSOS_eq_of_left_chart_sos
    {m d ℓ₁ ℓ₂ : ℕ} (M : PolyMat m)
    (A : Matrix (Fin ℓ₁) (Fin m) Poly)
    (B : Matrix (Fin ℓ₂) (Fin m) Poly)
    (hMdeg : ∀ i j, natDegree (M i j) ≤ 2 * d + 1)
    (hAdeg : ∀ i j, natDegree (A i j) ≤ d)
    (hBdeg : ∀ i j, natDegree (B i j) ≤ d)
    (hchart : intervalLeftChartMat (2 * d + 1) M = SOSForm A B) :
    M =
      (Polynomial.X : Poly) •
        ((unitIntervalDehomMat d B).transpose * unitIntervalDehomMat d B : PolyMat m) +
      ((1 - Polynomial.X : Poly) •
        ((unitIntervalDehomMat d A).transpose * unitIntervalDehomMat d A : PolyMat m)) := by
  apply Matrix.ext
  intro i j
  refine Polynomial.eq_of_infinite_eval_eq (R := ℝ) _ _ ?_
  refine (Set.finite_singleton (1 : ℝ)).infinite_compl.mono ?_
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  simp only [Set.mem_ofPred_eq]
  have hx' : 1 ≠ x := fun h => hx h.symm
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr hx'
  let u : ℝ := x / (1 - x)
  have hu_den : 1 + u ≠ 0 := by
    have hcalc : 1 + u = (1 : ℝ) / (1 - x) := by
      dsimp [u]
      field_simp [hden]
      ring
    rw [hcalc]
    exact one_div_ne_zero hden
  have hu_arg : u / (1 + u) = x := by
    dsimp [u]
    field_simp [hden]
    ring
  have hscale : (1 - x) ^ (2 * d + 1) * (1 + u) ^ (2 * d + 1) = 1 := by
    have hcalc : 1 + u = (1 : ℝ) / (1 - x) := by
      dsimp [u]
      field_simp [hden]
      ring
    rw [hcalc, one_div, ← mul_pow]
    simp [hden]
  have hchart_eval := congrArg (fun N => mapEval u N) hchart
  change mapEval u (intervalLeftChartMat (2 * d + 1) M) = mapEval u (SOSForm A B) at hchart_eval
  rw [mapEval_intervalLeftChartMat hMdeg hu_den, hu_arg] at hchart_eval
  have hentry := congrArg (fun N : Matrix (Fin m) (Fin m) ℝ => N i j) hchart_eval
  have hAeval := mapEval_unitIntervalDehomMat (A := A) hAdeg hden
  have hBeval := mapEval_unitIntervalDehomMat (A := B) hBdeg hden
  change (mapEval x M) i j =
    (mapEval x
      ((Polynomial.X : Poly) •
        ((unitIntervalDehomMat d B).transpose * unitIntervalDehomMat d B : PolyMat m) +
      ((1 - Polynomial.X : Poly) •
        ((unitIntervalDehomMat d A).transpose * unitIntervalDehomMat d A : PolyMat m)))) i j
  rw [mapEval_add, mapEval_smul, mapEval_mul, mapEval_transpose,
    mapEval_smul, mapEval_mul, mapEval_transpose, hAeval, hBeval]
  simp only [Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Matrix.add_apply, Matrix.smul_apply]
  simp only [SOSForm, mapEval_add, mapEval_mul, mapEval_transpose, mapEval_smul,
    Polynomial.eval_X, Matrix.add_apply, Matrix.smul_apply] at hentry
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_apply]
  simp only [smul_eq_mul] at hentry ⊢
  let aterm : ℝ :=
    (((mapEval (x / (1 - x)) A).transpose * mapEval (x / (1 - x)) A) i j)
  let bterm : ℝ :=
    (((mapEval (x / (1 - x)) B).transpose * mapEval (x / (1 - x)) B) i j)
  have hentry_scalar :
      (1 + u) ^ (2 * d + 1) * mapEval x M i j = aterm + u * bterm := by
    simpa [aterm, bterm, u] using hentry
  have hpow : (1 - x) ^ d * (1 - x) ^ d = (1 - x) ^ (2 * d) := by
    rw [← pow_add]
    congr 1
    omega
  have hBscale :
      x * ((1 - x) ^ d * (1 - x) ^ d) =
        (1 - x) ^ (2 * d + 1) * u := by
    dsimp [u]
    field_simp [hden]
    have hpow' : ((1 - x) ^ d) ^ 2 = (1 - x) ^ (2 * d) := by
      rw [pow_two, hpow]
    rw [hpow']
    rw [pow_succ]
    ring
  have hAscale :
      (1 - x) ^ (2 * d + 1) =
        (1 - x) * ((1 - x) ^ d * (1 - x) ^ d) := by
    rw [hpow, pow_succ]
    ring
  calc
    mapEval x M i j
        = (1 - x) ^ (2 * d + 1) * ((1 + u) ^ (2 * d + 1) * mapEval x M i j) := by
            rw [← mul_assoc, hscale]
            ring
    _ = (1 - x) ^ (2 * d + 1) * (aterm + u * bterm) := by rw [hentry_scalar]
    _ =
        (1 - x) * ((1 - x) ^ d * (1 - x) ^ d) * aterm +
          x * ((1 - x) ^ d * (1 - x) ^ d) * bterm := by
            have hmul :
                (1 - x) * ((1 - x) ^ d * (1 - x) ^ d) * u =
                  x * ((1 - x) ^ d * (1 - x) ^ d) := by
              rw [← hAscale, ← hBscale]
            calc
              (1 - x) ^ (2 * d + 1) * (aterm + u * bterm)
                  = (1 - x) * ((1 - x) ^ d * (1 - x) ^ d) *
                      (aterm + u * bterm) := by rw [hAscale]
              _ = (1 - x) * ((1 - x) ^ d * (1 - x) ^ d) * aterm +
                    ((1 - x) * ((1 - x) ^ d * (1 - x) ^ d) * u) * bterm := by ring
              _ = (1 - x) * ((1 - x) ^ d * (1 - x) ^ d) * aterm +
                    x * ((1 - x) ^ d * (1 - x) ^ d) * bterm := by rw [hmul]
    _ =
        x * ((1 - x) ^ d * (1 - x) ^ d) * bterm +
          (1 - x) * ((1 - x) ^ d * (1 - x) ^ d) * aterm := by
            ring

theorem unitInterval_lukacsSOS_bounded_odd
    {m d : ℕ} (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ 2 * d + 1)
    (hsymm : M.IsSymm) :
    NonnegOnIcc 0 1 M → IccLukacsCertificateBoundedOdd d 0 1 M := by
  intro hM
  have hleftNN := nonnegOnNN_intervalLeftChartMat_of_nonnegOnIcc hdeg hM
  have hleftSymm := intervalLeftChartMat_isSymm (D := 2 * d + 1) hsymm
  rcases halfLine_sos_bounded (intervalLeftChartMat (2 * d + 1) M)
      (d := 2 * d + 1) natDegree_intervalLeftChartMat_le hleftSymm hleftNN with
    ⟨A, B, hAdeg, hBdeg, hAB⟩
  let A' : Matrix (Fin (m + 1)) (Fin m) Poly := unitIntervalDehomMat d A
  let B' : Matrix (Fin (m + 1)) (Fin m) Poly := unitIntervalDehomMat d B
  have hAdeg₁ : ∀ i j, natDegree (A i j) ≤ d + 1 := by
    intro i j
    exact (hAdeg i j).trans (by dsimp [evenPartDegreeBound]; omega)
  have hBdeg' : ∀ i j, natDegree (B i j) ≤ d := by
    intro i j
    exact (hBdeg i j).trans (by dsimp [oddPartDegreeBound]; omega)
  have hAdeg' : ∀ i j, natDegree (A i j) ≤ d :=
    leftChart_sos_odd_first_factor_degree_drop hAdeg₁ hBdeg' hAB
  refine ⟨B', A', ?_, ?_, ?_⟩
  · exact natDegree_unitIntervalDehomMat_le B
  · exact natDegree_unitIntervalDehomMat_le A
  · have hEq := unitInterval_lukacsOddSOS_eq_of_left_chart_sos
      M A B hdeg hAdeg' hBdeg' hAB
    simpa [A', B'] using hEq

theorem nonnegOnIcc_of_lukacsSOS
    {m : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificate a b M) :
    NonnegOnIcc a b M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, rfl⟩
  intro x hax hxb
  rw [mapEval_add, mapEval_smul]
  have hweight : 0 ≤ (intervalWeight a b).eval x := by
    simp only [intervalWeight, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    exact mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hxb)
  exact (isMatrixSOS_posSemidef hS₀ x).add ((isMatrixSOS_posSemidef hS₁ x).smul hweight)

theorem nonnegOnIcc_of_lukacsOddSOS
    {m : ℕ} {a b : ℝ} {M : PolyMat m}
    (hcert : IccLukacsCertificateOdd a b M) :
    NonnegOnIcc a b M := by
  rcases hcert with ⟨S₀, S₁, hS₀, hS₁, rfl⟩
  intro x hax hxb
  rw [mapEval_add, mapEval_smul, mapEval_smul]
  have hleft : 0 ≤ (Polynomial.X - Polynomial.C a : Poly).eval x := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_nonneg.mpr hax
  have hright : 0 ≤ (Polynomial.C b - Polynomial.X : Poly).eval x := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_nonneg.mpr hxb
  exact ((isMatrixSOS_posSemidef hS₀ x).smul hleft).add
    ((isMatrixSOS_posSemidef hS₁ x).smul hright)

end MatrixSOS
