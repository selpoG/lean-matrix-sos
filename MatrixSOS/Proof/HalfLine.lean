/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.FullLine.Exact

/-!
# Reduction of half-line positivity to full-line certificates
-/

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS

/--
Degree bound for the even part of a polynomial of degree at most `d` after
writing it as a polynomial in `X ^ 2`.
-/
def evenPartDegreeBound (d : ℕ) : ℕ := d / 2

/--
Degree bound for the odd part of a polynomial of degree at most `d` after
factoring out one `X` and writing the rest as a polynomial in `X ^ 2`.
-/
def oddPartDegreeBound (d : ℕ) : ℕ := (d - 1) / 2

def evenPart (p : Poly) : Poly := Polynomial.contract 2 p

def oddPart (p : Poly) : Poly := Polynomial.contract 2 p.divX

def expandMat {ι κ : Type*} (A : Matrix ι κ Poly) : Matrix ι κ Poly :=
  fun i j => Polynomial.expand ℝ 2 (A i j)

def evenPartMat {ι κ : Type*} (A : Matrix ι κ Poly) : Matrix ι κ Poly :=
  fun i j => evenPart (A i j)

def oddPartMat {ι κ : Type*} (A : Matrix ι κ Poly) : Matrix ι κ Poly :=
  fun i j => oddPart (A i j)

@[simp] lemma coeff_evenPart (p : Poly) (n : ℕ) :
    (evenPart p).coeff n = p.coeff (2 * n) := by
  rw [evenPart, Polynomial.coeff_contract (by decide)]
  ring_nf

@[simp] lemma coeff_oddPart (p : Poly) (n : ℕ) :
    (oddPart p).coeff n = p.coeff (2 * n + 1) := by
  rw [oddPart, Polynomial.coeff_contract (by decide), Polynomial.coeff_divX]
  ring_nf

lemma even_odd_decomp (p : Poly) :
    p = Polynomial.expand ℝ 2 (evenPart p) + X * Polynomial.expand ℝ 2 (oddPart p) := by
  ext n
  have hpos : 0 < 2 := by decide
  rcases n with _ | n
  · rw [Polynomial.coeff_add, Polynomial.coeff_expand hpos, Polynomial.coeff_X_mul_zero]
    simp [coeff_evenPart]
  · rw [Polynomial.coeff_add, Polynomial.coeff_expand hpos, Polynomial.coeff_X_mul,
      Polynomial.coeff_expand hpos]
    by_cases hEven : 2 ∣ n
    · have hOddSucc : ¬ 2 ∣ n + 1 := by omega
      rw [ite_eq_right hOddSucc, ite_eq_left hEven, zero_add]
      rw [coeff_oddPart]
      have hEq : 2 * (n / 2) + 1 = n + 1 := by omega
      simp [hEq]
    · have hEvenSucc : 2 ∣ n + 1 := by omega
      rw [ite_eq_left hEvenSucc, ite_eq_right hEven, add_zero]
      rw [coeff_evenPart]
      have hEq : 2 * ((n + 1) / 2) = n + 1 := by omega
      simp [hEq]

@[simp] lemma evenPart_expand (p : Poly) :
    evenPart (Polynomial.expand ℝ 2 p) = p := by
  simpa [evenPart] using (Polynomial.contract_expand (R := ℝ) (p := 2) (f := p) (by decide))

@[simp] lemma oddPart_expand (p : Poly) :
    oddPart (Polynomial.expand ℝ 2 p) = 0 := by
  ext n
  rw [coeff_oddPart, Polynomial.coeff_expand (by decide)]
  have hodd : ¬ 2 ∣ 2 * n + 1 := by omega
  simp [hodd]

@[simp] lemma oddPart_add (p q : Poly) :
    oddPart (p + q) = oddPart p + oddPart q := by
  ext n
  simp [coeff_oddPart]

@[simp] lemma oddPart_X_mul_expand (p : Poly) :
    oddPart ((Polynomial.X : Poly) * Polynomial.expand ℝ 2 p) = p := by
  have h2 : 0 < (2 : ℕ) := by exact Nat.succ_pos 1
  ext n
  rw [coeff_oddPart, show 2 * n + 1 = 2 * n + 1 by rfl,
    show 2 * n + 1 = (2 * n) + 1 by omega, Polynomial.coeff_X_mul]
  simp [Polynomial.coeff_expand_mul' h2]

lemma natDegree_evenPart_le {p : Poly} {d : ℕ}
    (hp : natDegree p ≤ d) :
    natDegree (evenPart p) ≤ evenPartDegreeBound d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_evenPart]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt hp (by
    dsimp [evenPartDegreeBound] at hN
    omega)

lemma natDegree_oddPart_le {p : Poly} {d : ℕ}
    (hp : natDegree p ≤ d) :
    natDegree (oddPart p) ≤ oddPartDegreeBound d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_oddPart]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt hp (by
    dsimp [oddPartDegreeBound] at hN
    omega)

@[simp] lemma expandMat_transpose {ι κ : Type*} (A : Matrix ι κ Poly) :
    expandMat A.transpose = (expandMat A).transpose := by
  ext i j
  rfl

@[simp] lemma expandMat_add {ι κ : Type*} (A B : Matrix ι κ Poly) :
    expandMat (A + B) = expandMat A + expandMat B := by
  ext i j
  simp [expandMat]

@[simp] lemma expandMat_zero {ι κ : Type*} :
    expandMat (0 : Matrix ι κ Poly) = 0 := by
  ext i j
  simp [expandMat]

@[simp] lemma expandMat_smul {ι κ : Type*} (p : Poly) (A : Matrix ι κ Poly) :
    expandMat (p • A) = Polynomial.expand ℝ 2 p • expandMat A := by
  ext i j
  simp [expandMat]

@[simp] lemma expandMat_mul {ι κ μ : Type*} [Fintype κ]
    (A : Matrix ι κ Poly) (B : Matrix κ μ Poly) :
    expandMat (A * B) = expandMat A * expandMat B := by
  ext i j
  simp [expandMat, Matrix.mul_apply, map_sum]

@[simp] lemma oddPartMat_add {ι κ : Type*} (A B : Matrix ι κ Poly) :
    oddPartMat (A + B) = oddPartMat A + oddPartMat B := by
  ext i j
  simp [oddPartMat, oddPart_add]

@[simp] lemma oddPartMat_expandMat {ι κ : Type*} (A : Matrix ι κ Poly) :
    oddPartMat (expandMat A) = 0 := by
  ext i j
  simp [oddPartMat, expandMat]

@[simp] lemma oddPartMat_X_smul_expandMat {ι κ : Type*} (A : Matrix ι κ Poly) :
    oddPartMat ((Polynomial.X : Poly) • expandMat A) = A := by
  ext i j
  simp [oddPartMat, expandMat, oddPart_X_mul_expand]

@[simp] lemma oddPartMat_transpose_mul_expandMat
    {ι κ μ : Type*} [Fintype ι]
    (A : Matrix ι κ Poly) (B : Matrix ι μ Poly) :
    oddPartMat ((expandMat A).transpose * expandMat B) = 0 := by
  simpa [expandMat_mul, expandMat_transpose] using
    (oddPartMat_expandMat (A := A.transpose * B))

@[simp] lemma oddPartMat_X_smul_transpose_mul_expandMat
    {ι κ μ : Type*} [Fintype ι]
    (A : Matrix ι κ Poly) (B : Matrix ι μ Poly) :
    oddPartMat ((Polynomial.X : Poly) • ((expandMat A).transpose * expandMat B)) =
      A.transpose * B := by
  simpa [expandMat_mul, expandMat_transpose] using
    (oddPartMat_X_smul_expandMat (A := A.transpose * B))

@[simp] lemma oddPartMat_X_sq_smul_transpose_mul_expandMat
    {ι κ μ : Type*} [Fintype ι]
    (A : Matrix ι κ Poly) (B : Matrix ι μ Poly) :
    oddPartMat ((Polynomial.X ^ 2 : Poly) • ((expandMat A).transpose * expandMat B)) = 0 := by
  simpa [expandMat_mul, expandMat_transpose, pow_two, smul_smul] using
    (oddPartMat_expandMat (A := (Polynomial.X : Poly) • (A.transpose * B)))

lemma expandMat_evenOdd_decomp {ι κ : Type*} (A : Matrix ι κ Poly) :
    A = expandMat (evenPartMat A) + (Polynomial.X : Poly) • expandMat (oddPartMat A) := by
  ext i j n
  exact congrArg (fun p : Poly => p.coeff n) <|
    (show A i j =
      expandMat (evenPartMat A) i j + (Polynomial.X : Poly) * expandMat (oddPartMat A) i j by
        simpa [expandMat, evenPartMat, oddPartMat] using even_odd_decomp (A i j))

@[simp] lemma mapEval_expandMat {ι κ : Type*} (x : ℝ)
    (A : Matrix ι κ (Polynomial ℝ)) :
    mapEval x (expandMat A) = mapEval (x ^ 2) A := by
  ext i j
  simp [mapEval, expandMat, Polynomial.expand_eval]

lemma expandMat_isSymm {m : ℕ} {M : PolyMat m} (hM : M.IsSymm) :
    (expandMat M).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  exact congrArg (Polynomial.expand ℝ 2) (hM.apply i j)

lemma natDegree_expandMat_le {m d : ℕ} {M : PolyMat m}
    (hdeg : ∀ i j, natDegree (M i j) ≤ d) :
    ∀ i j, natDegree (expandMat M i j) ≤ 2 * d := by
  intro i j
  simpa [expandMat, mul_comm] using
    (show natDegree (Polynomial.expand ℝ 2 (M i j)) ≤ d * 2 by
      rw [Polynomial.natDegree_expand]
      exact Nat.mul_le_mul_right 2 (hdeg i j))

/--
Pulls nonnegativity on the normalized half-line back along `x ↦ x ^ 2`.
-/
lemma expandMat_posSemidefOn_univ_of_nonnegOnNN
    {m : ℕ} {M : PolyMat m}
    (hM : NonnegOnNN M) :
    ∀ x : ℝ, (mapEval x (expandMat M)).PosSemidef := by
  intro x
  simpa [mapEval_expandMat] using hM (x ^ 2) (sq_nonneg x)

lemma natDegree_evenPartMat_le {m ℓ d : ℕ}
    {R : Matrix (Fin ℓ) (Fin m) Poly}
    (hR : ∀ i j, natDegree (R i j) ≤ d) :
    ∀ i j, natDegree (evenPartMat R i j) ≤ evenPartDegreeBound d := by
  intro i j
  simpa [evenPartMat] using natDegree_evenPart_le (hR i j)

lemma natDegree_oddPartMat_le {m ℓ d : ℕ}
    {R : Matrix (Fin ℓ) (Fin m) Poly}
    (hR : ∀ i j, natDegree (R i j) ≤ d) :
    ∀ i j, natDegree (oddPartMat R i j) ≤ oddPartDegreeBound d := by
  intro i j
  simpa [oddPartMat] using natDegree_oddPart_le (hR i j)

lemma expandMat_injective {ι κ : Type*} :
    Function.Injective (expandMat (ι := ι) (κ := κ)) := by
  intro A B hAB
  funext i j
  exact (Polynomial.expand_injective (R := ℝ) (n := 2) (by decide))
    (congrArg (fun M => M i j) hAB)

theorem sosForm_of_expand_factor
    {m d ℓ : ℕ}
    (M : PolyMat m)
    (R : Matrix (Fin ℓ) (Fin m) Poly)
    (hRdeg : ∀ i j, natDegree (R i j) ≤ d)
    (hR : expandMat M = R.transpose * R) :
    ∃ (A : Matrix (Fin ℓ) (Fin m) Poly)
      (B : Matrix (Fin ℓ) (Fin m) Poly),
      (∀ i j, natDegree (A i j) ≤ evenPartDegreeBound d) ∧
      (∀ i j, natDegree (B i j) ≤ oddPartDegreeBound d) ∧
      M = SOSForm A B := by
  let A : Matrix (Fin ℓ) (Fin m) Poly := evenPartMat R
  let B : Matrix (Fin ℓ) (Fin m) Poly := oddPartMat R
  refine ⟨A, B, ?_, ?_, ?_⟩
  · simpa [A] using natDegree_evenPartMat_le hRdeg
  · simpa [B] using natDegree_oddPartMat_le hRdeg
  · have hRdecomp :
        R = expandMat A + (Polynomial.X : Poly) • expandMat B := by
        simpa [A, B] using expandMat_evenOdd_decomp R
    have hExpanded :
        expandMat M =
          expandMat (A.transpose * A) +
            (Polynomial.X : Poly) • expandMat (A.transpose * B) +
            (Polynomial.X : Poly) • expandMat (B.transpose * A) +
            expandMat ((Polynomial.X : Poly) • (B.transpose * B)) := by
      rw [hR, hRdecomp]
      simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
        smul_add, add_assoc, add_left_comm, pow_two, smul_smul]
    have hCross :
        A.transpose * B + B.transpose * A = 0 := by
      have hOdd := congrArg oddPartMat hExpanded
      simpa [add_assoc, add_left_comm] using hOdd.symm
    have hFinal : expandMat M = expandMat (SOSForm A B) := by
      calc
        expandMat M =
            expandMat (A.transpose * A) +
              (Polynomial.X : Poly) • expandMat (A.transpose * B) +
              (Polynomial.X : Poly) • expandMat (B.transpose * A) +
              expandMat ((Polynomial.X : Poly) • (B.transpose * B)) := hExpanded
        _ =
            expandMat (A.transpose * A) +
              (Polynomial.X : Poly) • expandMat (A.transpose * B + B.transpose * A) +
              expandMat ((Polynomial.X : Poly) • (B.transpose * B)) := by
                simp [smul_add, add_assoc]
        _ =
            expandMat (A.transpose * A) +
              expandMat ((Polynomial.X : Poly) • (B.transpose * B)) := by
                simp [hCross]
        _ = expandMat (SOSForm A B) := by
              rw [SOSForm, expandMat_add]
    exact expandMat_injective hFinal

theorem halfLine_sos_bounded_of_expand_factor
    {m d : ℕ}
    (M : PolyMat m)
    (hfac :
      ∃ (R : Matrix (Fin (m + 1)) (Fin m) Poly),
        (∀ i j, natDegree (R i j) ≤ d) ∧
        expandMat M = R.transpose * R) :
    ∃ (A B : Matrix (Fin (m + 1)) (Fin m) (Polynomial ℝ)),
      (∀ i j, natDegree (A i j) ≤ evenPartDegreeBound d) ∧
      (∀ i j, natDegree (B i j) ≤ oddPartDegreeBound d) ∧
      M = SOSForm A B := by
  rcases hfac with ⟨R, hRdeg, hR⟩
  rcases sosForm_of_expand_factor M R hRdeg hR with ⟨A, B, hAdeg, hBdeg, hAB⟩
  exact ⟨A, B, hAdeg, hBdeg, hAB⟩

theorem halfLine_sos_bounded
    {m d : ℕ}
    (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm)
    (hM : NonnegOnNN M) :
    ∃ (A B : Matrix (Fin (m + 1)) (Fin m) (Polynomial ℝ)),
      (∀ i j, natDegree (A i j) ≤ evenPartDegreeBound d) ∧
      (∀ i j, natDegree (B i j) ≤ oddPartDegreeBound d) ∧
      M = SOSForm A B := by
  let P : PolyMat m := expandMat M
  have hPdeg : ∀ i j, natDegree (P i j) ≤ 2 * d := by
    simpa [P] using natDegree_expandMat_le hdeg
  have hPsymm : P.IsSymm := by
    simpa [P] using expandMat_isSymm hsymm
  have hPnonneg : ∀ x : ℝ, (mapEval x P).PosSemidef := by
    simpa [P] using expandMat_posSemidefOn_univ_of_nonnegOnNN hM
  rcases fullLine_psd_factorization_pos P hPdeg hPsymm hPnonneg with
    ⟨R, hRdeg, hPR⟩
  exact halfLine_sos_bounded_of_expand_factor M
    ⟨R, hRdeg, by simpa [P] using hPR⟩

/--
Bounded normalized half-line SOS certificate with both rectangular factors
having exactly `m + 1` rows.
-/
def NormalizedHalfLineSOSCertificateBounded {m : ℕ} (d : ℕ) (M : PolyMat m) :
    Prop :=
  ∃ (A B : Matrix (Fin (m + 1)) (Fin m) Poly),
    (∀ i j, natDegree (A i j) ≤ evenPartDegreeBound d) ∧
    (∀ i j, natDegree (B i j) ≤ oddPartDegreeBound d) ∧
    M = SOSForm A B

theorem halfLine_sosCertificate_bounded
    {m d : ℕ}
    (M : PolyMat m)
    (hdeg : ∀ i j, natDegree (M i j) ≤ d)
    (hsymm : M.IsSymm)
    (hM : NonnegOnNN M) :
    NormalizedHalfLineSOSCertificateBounded d M := by
  rcases halfLine_sos_bounded M hdeg hsymm hM with
    ⟨A, B, hAdeg, hBdeg, hAB⟩
  exact ⟨A, B, hAdeg, hBdeg, hAB⟩

theorem isMatrixSOS_posSemidef
    {m : ℕ} {M : PolyMat m} (hM : IsMatrixSOS M) :
    ∀ x : ℝ, (mapEval x M).PosSemidef := by
  rcases hM with ⟨ℓ, R, hR⟩
  intro x
  subst M
  simpa using
    (Matrix.posSemidef_conjTranspose_mul_self (A := mapEval x R))

end MatrixSOS
