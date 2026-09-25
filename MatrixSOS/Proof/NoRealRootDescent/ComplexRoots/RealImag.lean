/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.NoRealRootDescent.ComplexRoots.RootFactorization

/-!
# Real and imaginary parts in complex-root descent
-/

open Matrix Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS
def mapEvalComplex {ι κ : Type*} (z : ℂ) (A : Matrix ι κ Poly) : Matrix ι κ ℂ :=
  A.map (Polynomial.eval₂RingHom (algebraMap ℝ ℂ) z)

def complexReVec {n : Type*} (w : n → ℂ) : n → ℝ := fun i => (w i).re

def complexImVec {n : Type*} (w : n → ℂ) : n → ℝ := fun i => (w i).im

def complexPairRealImagFamily {n ι : Type*} (w : ι → n → ℂ) :
    ((Unit ⊕ Unit) × ι) → n → ℝ
  | (Sum.inl (), i) => Real.sqrt 2 • complexReVec (w i)
  | (Sum.inr (), i) => Real.sqrt 2 • complexImVec (w i)

@[simp] theorem complexReVec_apply {n : Type*} (w : n → ℂ) (i : n) :
    complexReVec w i = (w i).re := rfl

@[simp] theorem complexImVec_apply {n : Type*} (w : n → ℂ) (i : n) :
    complexImVec w i = (w i).im := rfl

@[simp] theorem complexPairRealImagFamily_inl
    {n ι : Type*}
    (w : ι → n → ℂ)
    (i : ι) :
    complexPairRealImagFamily w (Sum.inl (), i) = Real.sqrt 2 • complexReVec (w i) := rfl

@[simp] theorem complexPairRealImagFamily_inr
    {n ι : Type*}
    (w : ι → n → ℂ)
    (i : ι) :
    complexPairRealImagFamily w (Sum.inr (), i) = Real.sqrt 2 • complexImVec (w i) := rfl

def complexPairRealImagEuclideanFamily {n ι : Type*} [Fintype n]
    (w : ι → EuclideanSpace ℂ n) :
    ((Unit ⊕ Unit) × ι) → EuclideanSpace ℝ n
  | (Sum.inl (), i) => WithLp.toLp 2 (Real.sqrt 2 • complexReVec (WithLp.ofLp (w i)))
  | (Sum.inr (), i) => WithLp.toLp 2 (Real.sqrt 2 • complexImVec (WithLp.ofLp (w i)))

@[simp] theorem complexPairRealImagEuclideanFamily_inl
    {n ι : Type*}
    [Fintype n]
    (w : ι → EuclideanSpace ℂ n)
    (i : ι) :
    complexPairRealImagEuclideanFamily w (Sum.inl (), i) =
      WithLp.toLp 2 (Real.sqrt 2 • complexReVec (WithLp.ofLp (w i))) := rfl

@[simp] theorem complexPairRealImagEuclideanFamily_inr
    {n ι : Type*}
    [Fintype n]
    (w : ι → EuclideanSpace ℂ n)
    (i : ι) :
    complexPairRealImagEuclideanFamily w (Sum.inr (), i) =
      WithLp.toLp 2 (Real.sqrt 2 • complexImVec (WithLp.ofLp (w i))) := rfl

theorem complexReVec_dot_complexReVec_sub_complexImVec_dot_complexImVec
    {n : Type*}
    [Fintype n]
    (w x : n → ℂ) :
    complexReVec w ⬝ᵥ complexReVec x - complexImVec w ⬝ᵥ complexImVec x = (w ⬝ᵥ x).re := by
  simp [complexReVec, complexImVec, dotProduct, Finset.sum_sub_distrib]

theorem complexReVec_dot_complexImVec_add_complexImVec_dot_complexReVec
    {n : Type*}
    [Fintype n]
    (w x : n → ℂ) :
    complexReVec w ⬝ᵥ complexImVec x + complexImVec w ⬝ᵥ complexReVec x = (w ⬝ᵥ x).im := by
  simp [complexReVec, complexImVec, dotProduct, Finset.sum_add_distrib]

theorem complexReVec_dot_complexReVec_add_complexImVec_dot_complexImVec
    {n : Type*}
    [Fintype n]
    (w x : n → ℂ) :
    complexReVec w ⬝ᵥ complexReVec x + complexImVec w ⬝ᵥ complexImVec x = ((star w) ⬝ᵥ x).re := by
  simp [complexReVec, complexImVec, dotProduct, Finset.sum_add_distrib]

theorem complexReVec_dot_complexImVec_sub_complexImVec_dot_complexReVec
    {n : Type*}
    [Fintype n]
    (w x : n → ℂ) :
    complexReVec w ⬝ᵥ complexImVec x - complexImVec w ⬝ᵥ complexReVec x = ((star w) ⬝ᵥ x).im := by
  rw [dotProduct, dotProduct, sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  simp [complexReVec, complexImVec, dotProduct]

theorem complex_real_imag_dot_eq_half_of_dot_zero_and_star_dot_real
    {n : Type*}
    [Fintype n]
    (w x : n → ℂ)
    {c : ℝ}
    (hbil : w ⬝ᵥ x = 0)
    (hherm : (star w) ⬝ᵥ x = c) :
    complexReVec w ⬝ᵥ complexReVec x = c / 2 ∧
      complexImVec w ⬝ᵥ complexImVec x = c / 2 ∧
      complexReVec w ⬝ᵥ complexImVec x = 0 ∧
      complexImVec w ⬝ᵥ complexReVec x = 0 := by
  have hsub :
      complexReVec w ⬝ᵥ complexReVec x - complexImVec w ⬝ᵥ complexImVec x = 0 := by
    rw [complexReVec_dot_complexReVec_sub_complexImVec_dot_complexImVec, hbil]
    simp
  have hadd :
      complexReVec w ⬝ᵥ complexReVec x + complexImVec w ⬝ᵥ complexImVec x = c := by
    rw [complexReVec_dot_complexReVec_add_complexImVec_dot_complexImVec, hherm]
    simp
  have hsub' :
      complexReVec w ⬝ᵥ complexImVec x - complexImVec w ⬝ᵥ complexReVec x = 0 := by
    rw [complexReVec_dot_complexImVec_sub_complexImVec_dot_complexReVec, hherm]
    simp
  have hadd' :
      complexReVec w ⬝ᵥ complexImVec x + complexImVec w ⬝ᵥ complexReVec x = 0 := by
    rw [complexReVec_dot_complexImVec_add_complexImVec_dot_complexReVec, hbil]
    simp
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem orthonormal_complexPairRealImagEuclideanFamily_of_orthonormal_of_dot_zero
    {n ι : Type*}
    [Fintype n]
    {w : ι → EuclideanSpace ℂ n}
    (hw : Orthonormal ℂ w)
    (hbil : ∀ i j, WithLp.ofLp (w i) ⬝ᵥ WithLp.ofLp (w j) = 0) :
    Orthonormal ℝ (complexPairRealImagEuclideanFamily w) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rcases a with ⟨sa, i⟩
  rcases b with ⟨sb, j⟩
  have hhermComplex : (star (WithLp.ofLp (w i))) ⬝ᵥ WithLp.ofLp (w j) = if i = j then (1 : ℂ) else 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      (orthonormal_iff_ite.mp hw i j)
  have hherm : (star (WithLp.ofLp (w i))) ⬝ᵥ WithLp.ofLp (w j) = ((ite (i = j) 1 0 : ℝ) : ℂ) := by
    by_cases hij : i = j
    · subst hij
      simpa using hhermComplex
    · simpa [hij] using hhermComplex
  rcases complex_real_imag_dot_eq_half_of_dot_zero_and_star_dot_real
      (WithLp.ofLp (w i)) (WithLp.ofLp (w j)) (c := (ite (i = j) 1 0 : ℝ)) (hbil i j) hherm with
    ⟨hrr, hii, hri, hir⟩
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
  rcases sa with _ | _
  · rcases sb with _ | _
    · simp +locals only [WithLp.toLp_smul, Prod.mk.injEq, true_and]
      have hinner :
          inner ℝ (WithLp.toLp 2 (complexReVec (WithLp.ofLp (w i))))
              (WithLp.toLp 2 (complexReVec (WithLp.ofLp (w j)))) =
            complexReVec (WithLp.ofLp (w i)) ⬝ᵥ complexReVec (WithLp.ofLp (w j)) := by
        simpa [dotProduct_comm] using
          (EuclideanSpace.inner_toLp_toLp
            (complexReVec (WithLp.ofLp (w i)))
            (complexReVec (WithLp.ofLp (w j))))
      rw [inner_smul_left, inner_smul_right, hinner]
      by_cases hij : i = j
      · subst hij
        have hrr' :
            complexReVec (WithLp.ofLp (w i)) ⬝ᵥ complexReVec (WithLp.ofLp (w i)) = 1 / 2 := by
          simpa using hrr
        rw [hrr']
        simp
        nlinarith [hsqrt]
      · rw [hrr]
        simp [hij]
    · simp +locals only [WithLp.toLp_smul, Prod.mk.injEq, reduceCtorEq, false_and, ↓reduceIte]
      have hinner :
          inner ℝ (WithLp.toLp 2 (complexReVec (WithLp.ofLp (w i))))
              (WithLp.toLp 2 (complexImVec (WithLp.ofLp (w j)))) =
            complexReVec (WithLp.ofLp (w i)) ⬝ᵥ complexImVec (WithLp.ofLp (w j)) := by
        simpa [dotProduct_comm] using
          (EuclideanSpace.inner_toLp_toLp
            (complexReVec (WithLp.ofLp (w i)))
            (complexImVec (WithLp.ofLp (w j))))
      rw [inner_smul_left, inner_smul_right, hinner]
      rw [hri]
      simp
  · rcases sb with _ | _
    · simp +locals only [WithLp.toLp_smul, Prod.mk.injEq, reduceCtorEq, false_and, ↓reduceIte]
      have hinner :
          inner ℝ (WithLp.toLp 2 (complexImVec (WithLp.ofLp (w i))))
              (WithLp.toLp 2 (complexReVec (WithLp.ofLp (w j)))) =
            complexImVec (WithLp.ofLp (w i)) ⬝ᵥ complexReVec (WithLp.ofLp (w j)) := by
        simpa [dotProduct_comm] using
          (EuclideanSpace.inner_toLp_toLp
            (complexImVec (WithLp.ofLp (w i)))
            (complexReVec (WithLp.ofLp (w j))))
      rw [inner_smul_left, inner_smul_right, hinner]
      rw [hir]
      simp
    · simp +locals only [WithLp.toLp_smul, Prod.mk.injEq, true_and]
      have hinner :
          inner ℝ (WithLp.toLp 2 (complexImVec (WithLp.ofLp (w i))))
              (WithLp.toLp 2 (complexImVec (WithLp.ofLp (w j)))) =
            complexImVec (WithLp.ofLp (w i)) ⬝ᵥ complexImVec (WithLp.ofLp (w j)) := by
        simpa [dotProduct_comm] using
          (EuclideanSpace.inner_toLp_toLp
            (complexImVec (WithLp.ofLp (w i)))
            (complexImVec (WithLp.ofLp (w j))))
      rw [inner_smul_left, inner_smul_right, hinner]
      by_cases hij : i = j
      · subst hij
        have hii' :
            complexImVec (WithLp.ofLp (w i)) ⬝ᵥ complexImVec (WithLp.ofLp (w i)) = 1 / 2 := by
          simpa using hii
        rw [hii']
        simp
        nlinarith [hsqrt]
      · rw [hii]
        simp [hij]

theorem col_dotProduct_col_eq_zero_of_transpose_mul_eq_zero
    {n κ : Type*}
    [Fintype n]
    (Q : Matrix n κ ℂ)
    (hQ : Q.transpose * Q = 0)
    (j k : κ) :
    Q.col j ⬝ᵥ Q.col k = 0 := by
  have hentry := congrArg (fun M : Matrix κ κ ℂ => M j k) hQ
  simpa [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.col_apply] using hentry

theorem col_dotProduct_eq_zero_of_mem_span_cols_of_transpose_mul_eq_zero
    {n κ : Type*}
    [Fintype n]
    (Q : Matrix n κ ℂ)
    (hQ : Q.transpose * Q = 0)
    (j : κ)
    {w : n → ℂ}
    (hw : w ∈ Submodule.span ℂ (Set.range Q.col)) :
    Q.col j ⬝ᵥ w = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨k, rfl⟩
      exact col_dotProduct_col_eq_zero_of_transpose_mul_eq_zero Q hQ j k
  | zero =>
      simp
  | add x y _ _ hx hy =>
      simp [dotProduct_add, hx, hy]
  | smul a x _ hx =>
      simp [dotProduct_smul, hx]

theorem dotProduct_eq_zero_of_mem_span_cols_of_transpose_mul_eq_zero
    {n κ : Type*}
    [Fintype n]
    (Q : Matrix n κ ℂ)
    (hQ : Q.transpose * Q = 0)
    {v w : n → ℂ}
    (hv : v ∈ Submodule.span ℂ (Set.range Q.col))
    (hw : w ∈ Submodule.span ℂ (Set.range Q.col)) :
    v ⬝ᵥ w = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨j, rfl⟩
      exact col_dotProduct_eq_zero_of_mem_span_cols_of_transpose_mul_eq_zero Q hQ j hw
  | zero =>
      simp
  | add x y _ _ hx hy =>
      simp [add_dotProduct, hx, hy]
  | smul a x _ hx =>
      simp [smul_dotProduct, hx]

theorem ofLp_mem_span_cols_of_mem_span_toLp_cols
    {n κ : Type*}
    (Q : Matrix n κ ℂ)
    {w : EuclideanSpace ℂ n}
    (hw : w ∈ Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j))) :
    WithLp.ofLp w ∈ Submodule.span ℂ (Set.range Q.col) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j, rfl⟩
  | zero =>
      simp
  | add x y _ _ hx hy =>
      simpa using Submodule.add_mem (Submodule.span ℂ (Set.range Q.col)) hx hy
  | smul a x _ hx =>
      simpa using Submodule.smul_mem (Submodule.span ℂ (Set.range Q.col)) a hx

theorem dotProduct_eq_zero_of_mem_span_toLp_cols_of_transpose_mul_eq_zero
    {n κ : Type*}
    [Fintype n]
    (Q : Matrix n κ ℂ)
    (hQ : Q.transpose * Q = 0)
    {v w : EuclideanSpace ℂ n}
    (hv : v ∈ Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j)))
    (hw : w ∈ Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j))) :
    WithLp.ofLp v ⬝ᵥ WithLp.ofLp w = 0 := by
  exact dotProduct_eq_zero_of_mem_span_cols_of_transpose_mul_eq_zero Q hQ
    (ofLp_mem_span_cols_of_mem_span_toLp_cols Q hv)
    (ofLp_mem_span_cols_of_mem_span_toLp_cols Q hw)

theorem orthonormal_complexPairRealImagEuclideanFamily_stdOrthonormalBasis_span_toLp_cols_of_transpose_mul_eq_zero
    {n κ : Type*}
    [Fintype n]
    (Q : Matrix n κ ℂ)
    (hQ : Q.transpose * Q = 0) :
    let W : Submodule ℂ (EuclideanSpace ℂ n) :=
      Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j))
    Orthonormal ℝ
      (complexPairRealImagEuclideanFamily
        (fun i : Fin (Module.finrank ℂ W) =>
          (((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ n)))) := by
  intro W
  apply orthonormal_complexPairRealImagEuclideanFamily_of_orthonormal_of_dot_zero
  · convert ((stdOrthonormalBasis ℂ W).orthonormal.comp_linearIsometry W.subtypeₗᵢ) with i
    rfl
  · intro i j
    have hwi :
        (((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ n)) ∈
          Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j)) := by
      change (((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ n)) ∈ W
      exact (stdOrthonormalBasis ℂ W i).property
    have hwj :
        (((stdOrthonormalBasis ℂ W j : W) : EuclideanSpace ℂ n)) ∈
          Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j)) := by
      change (((stdOrthonormalBasis ℂ W j : W) : EuclideanSpace ℂ n)) ∈ W
      exact (stdOrthonormalBasis ℂ W j).property
    exact dotProduct_eq_zero_of_mem_span_toLp_cols_of_transpose_mul_eq_zero Q hQ hwi hwj

theorem two_mul_finrank_span_toLp_cols_le_card_of_transpose_mul_eq_zero
    {n κ : Type*}
    [Fintype n]
    (Q : Matrix n κ ℂ)
    (hQ : Q.transpose * Q = 0) :
    2 * Module.finrank ℂ (Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j))) ≤
      Fintype.card n := by
  let W : Submodule ℂ (EuclideanSpace ℂ n) :=
    Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j))
  have horth :
      Orthonormal ℝ
        (complexPairRealImagEuclideanFamily
          (fun i : Fin (Module.finrank ℂ W) =>
            (((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ n)))) := by
    let horth0 :=
      orthonormal_complexPairRealImagEuclideanFamily_stdOrthonormalBasis_span_toLp_cols_of_transpose_mul_eq_zero
        Q hQ
    dsimp only at horth0
    change Orthonormal ℝ
      (complexPairRealImagEuclideanFamily
        (fun i : Fin (Module.finrank ℂ W) =>
          (((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ n)))) at horth0
    exact horth0
  have hcard :
      Fintype.card (((Unit ⊕ Unit) × Fin (Module.finrank ℂ W))) ≤
        Module.finrank ℝ (EuclideanSpace ℝ n) :=
    horth.linearIndependent.fintype_card_le_finrank
  have hleft : Fintype.card (((Unit ⊕ Unit) × Fin (Module.finrank ℂ W))) = 2 * Module.finrank ℂ W := by
    rw [Fintype.card_prod, Fintype.card_sum]
    simp [Fintype.card_fin]
  have hright : Module.finrank ℝ (EuclideanSpace ℝ n) = Fintype.card n := by
    simp [finrank_euclideanSpace]
  rw [hleft, hright] at hcard
  simpa [W] using hcard

theorem finrank_span_toLp_cols_le_even_pairs_of_transpose_mul_eq_zero
    {m : ℕ}
    {κ : Type*}
    (Q : Matrix ((Unit ⊕ Unit) × Fin m) κ ℂ)
    (hQ : Q.transpose * Q = 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j))) ≤ m := by
  have h :=
    two_mul_finrank_span_toLp_cols_le_card_of_transpose_mul_eq_zero Q hQ
  have h' :
      2 * Module.finrank ℂ (Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j))) ≤
        2 * m := by
    have hcard : Fintype.card ((Unit ⊕ Unit) × Fin m) = 2 * m := by
      rw [Fintype.card_prod, Fintype.card_sum]
      simp [Fintype.card_fin]
    rw [hcard] at h
    exact h
  omega

theorem finrank_span_toLp_cols_le_odd_pairs_of_transpose_mul_eq_zero
    {m : ℕ}
    {κ : Type*}
    (Q : Matrix (((Unit ⊕ Unit) × Fin m) ⊕ Unit) κ ℂ)
    (hQ : Q.transpose * Q = 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j))) ≤ m := by
  have h :=
    two_mul_finrank_span_toLp_cols_le_card_of_transpose_mul_eq_zero Q hQ
  have h' :
      2 * Module.finrank ℂ (Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j))) ≤
        2 * m + 1 := by
    have hcard : Fintype.card (((Unit ⊕ Unit) × Fin m) ⊕ Unit) = 2 * m + 1 := by
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_sum]
      simp [Fintype.card_fin]
    rw [hcard] at h
    exact h
  omega

theorem complexPairRealImagEuclideanFamily_dot_add_I
    {n ι : Type*}
    [Fintype n]
    (w : ι → EuclideanSpace ℂ n)
    (i : ι)
    (x : n → ℂ) :
    (fun k => ((complexPairRealImagEuclideanFamily w (Sum.inl (), i)) k : ℂ)) ⬝ᵥ x +
        Complex.I * ((fun k => ((complexPairRealImagEuclideanFamily w (Sum.inr (), i)) k : ℂ)) ⬝ᵥ x) =
      (Real.sqrt 2 : ℂ) * (WithLp.ofLp (w i) ⬝ᵥ x) := by
  unfold dotProduct
  calc
    ∑ k, (↑((complexPairRealImagEuclideanFamily w (Sum.inl (), i)) k) : ℂ) * x k +
        Complex.I * ∑ k, (↑((complexPairRealImagEuclideanFamily w (Sum.inr (), i)) k) : ℂ) * x k
        = ∑ k, (↑((complexPairRealImagEuclideanFamily w (Sum.inl (), i)) k) : ℂ) * x k +
            ∑ k, Complex.I * ((↑((complexPairRealImagEuclideanFamily w (Sum.inr (), i)) k) : ℂ) * x k) := by
              rw [Finset.mul_sum]
    _ = ∑ k,
          ((↑((complexPairRealImagEuclideanFamily w (Sum.inl (), i)) k) : ℂ) * x k +
            Complex.I * ((↑((complexPairRealImagEuclideanFamily w (Sum.inr (), i)) k) : ℂ) * x k)) := by
            rw [← Finset.sum_add_distrib]
    _ = ∑ k, (Real.sqrt 2 : ℂ) * ((WithLp.ofLp (w i) k) * x k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          calc
            (↑((complexPairRealImagEuclideanFamily w (Sum.inl (), i)) k) : ℂ) * x k +
                Complex.I * ((↑((complexPairRealImagEuclideanFamily w (Sum.inr (), i)) k) : ℂ) * x k)
                = (Real.sqrt 2 : ℂ) *
                    ((((WithLp.ofLp (w i) k).re : ℂ) +
                      Complex.I * (((WithLp.ofLp (w i) k).im : ℂ))) * x k) := by
                        simp [complexPairRealImagEuclideanFamily, complexReVec, complexImVec]
                        ring
            _ = (Real.sqrt 2 : ℂ) * ((WithLp.ofLp (w i) k) * x k) := by
                  have hz :
                      (((WithLp.ofLp (w i) k).re : ℂ) +
                          Complex.I * (((WithLp.ofLp (w i) k).im : ℂ))) =
                        WithLp.ofLp (w i) k := by
                    simpa [mul_comm] using Complex.re_add_im (WithLp.ofLp (w i) k)
                  rw [hz]
    _ = (Real.sqrt 2 : ℂ) * ∑ k, (WithLp.ofLp (w i) k) * x k := by
          rw [Finset.mul_sum]

theorem dotProduct_complexBasis_eq_zero_of_orthogonal_to_pairFamily
    {n ι : Type*}
    [Fintype n]
    (u : EuclideanSpace ℝ n)
    (w : ι → EuclideanSpace ℂ n)
    (i : ι)
    (hRe : u ⬝ᵥ complexPairRealImagEuclideanFamily w (Sum.inl (), i) = 0)
    (hIm : u ⬝ᵥ complexPairRealImagEuclideanFamily w (Sum.inr (), i) = 0) :
    (fun k => (u k : ℂ)) ⬝ᵥ WithLp.ofLp (w i) = 0 := by
  have hReC :
      (fun k => ((complexPairRealImagEuclideanFamily w (Sum.inl (), i)) k : ℂ)) ⬝ᵥ
          (fun k => (u k : ℂ)) = 0 := by
    simpa [dotProduct, mul_comm] using congrArg (fun r : ℝ => (r : ℂ)) hRe
  have hImC :
      (fun k => ((complexPairRealImagEuclideanFamily w (Sum.inr (), i)) k : ℂ)) ⬝ᵥ
          (fun k => (u k : ℂ)) = 0 := by
    simpa [dotProduct, mul_comm] using congrArg (fun r : ℝ => (r : ℂ)) hIm
  have hsqrtC : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 (by positivity : (0 : ℝ) < 2)
  have hwu :
      (Real.sqrt 2 : ℂ) * (WithLp.ofLp (w i) ⬝ᵥ (fun k => (u k : ℂ))) = 0 := by
    have hpair := complexPairRealImagEuclideanFamily_dot_add_I w i (fun k => (u k : ℂ))
    rw [hReC, hImC, zero_add, mul_zero] at hpair
    exact hpair.symm
  have hdot : WithLp.ofLp (w i) ⬝ᵥ (fun k => (u k : ℂ)) = 0 :=
    (mul_eq_zero.mp hwu).resolve_left hsqrtC
  simpa [dotProduct_comm] using hdot

theorem transpose_basisFun_toMatrix_mul_apply_eq_dotProduct
    {n κ : Type*}
    [Fintype n]
    (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    (Q : Matrix n κ ℂ)
    (i : n)
    (j : κ) :
    ((((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose.map (algebraMap ℝ ℂ)) * Q) i j =
      (fun k => ((b i) k : ℂ)) ⬝ᵥ Q.col j := by
  simp [Matrix.mul_apply, dotProduct, Module.Basis.toMatrix_apply]

theorem dotProduct_eq_zero_of_mem_span_of_orthogonal_to_pairFamily
    {n ι : Type*}
    [Fintype n]
    (u : EuclideanSpace ℝ n)
    (w : ι → EuclideanSpace ℂ n)
    (hu : ∀ i,
      u ⬝ᵥ complexPairRealImagEuclideanFamily w (Sum.inl (), i) = 0 ∧
        u ⬝ᵥ complexPairRealImagEuclideanFamily w (Sum.inr (), i) = 0)
    {x : EuclideanSpace ℂ n}
    (hx : x ∈ Submodule.span ℂ (Set.range w)) :
    (fun k => (u k : ℂ)) ⬝ᵥ WithLp.ofLp x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨i, rfl⟩
      exact dotProduct_complexBasis_eq_zero_of_orthogonal_to_pairFamily u w i (hu i).1 (hu i).2
  | zero =>
      simp
  | add x y _ _ hx hy =>
      simp [dotProduct_add, hx, hy]
  | smul a x _ hx =>
      simp [dotProduct_smul, hx]

end MatrixSOS
