/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Mathlib

@[expose] public section

/-!
# Probabilities over finite uniform spaces

`prob p` is the probability that the predicate `p` holds at a uniformly random point of a finite
type. The file proves the two averaging steps of a hybrid argument: a telescoping sum has a term
at least its average (`telescope`), and an average is at most some term (`exists_abs_ge_avg`).
They give the step from many independent samples to one (`multi_sample`): if a test tells `N`
samples of `g` apart from `N` uniform samples with advantage `δ`, then fixing all but one sample
tells one sample of `g` apart from one uniform sample with advantage at least `δ / N`.
-/

namespace NaturalProofs

open Finset

/-- `1` for `true`, `0` for `false`. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

/-- The probability that `p` holds at a uniformly random point of `Ω`. -/
noncomputable def prob {Ω : Type} [Fintype Ω] (p : Ω → Bool) : ℝ :=
  (∑ ω, ind (p ω)) / Fintype.card Ω

variable {Ω Ω' A B I X : Type} [Fintype Ω] [Fintype Ω'] [Fintype A] [Fintype B] [Fintype I]
  [Fintype X]

theorem prob_eq_card_filter (p : Ω → Bool) :
    prob p = ((univ.filter (fun ω => p ω = true)).card : ℝ) / Fintype.card Ω := by
  simp only [prob, ind]
  rw [Finset.sum_boole]

theorem prob_equiv (e : Ω ≃ Ω') (p : Ω' → Bool) : prob (fun ω => p (e ω)) = prob p := by
  simp only [prob]
  rw [Equiv.sum_comp e (fun ω' => ind (p ω')), Fintype.card_congr e]

theorem prob_fst [Nonempty B] (p : A → Bool) : prob (fun ω : A × B => p ω.1) = prob p := by
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [prob, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.mul_sum]
  field_simp

theorem prob_snd [Nonempty A] (p : B → Bool) : prob (fun ω : A × B => p ω.2) = prob p := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [prob, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Some step of a telescoping sum is at least the average step. -/
theorem telescope (q : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ t < N, |q 0 - q N| / N ≤ |q t - q (t + 1)| := by
  by_contra h
  push Not at h
  have hsum : q 0 - q N = ∑ t ∈ range N, (q t - q (t + 1)) := (Finset.sum_range_sub' q N).symm
  have h1 : |q 0 - q N| ≤ ∑ t ∈ range N, |q t - q (t + 1)| :=
    hsum ▸ Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ t ∈ range N, |q t - q (t + 1)| < ∑ _t ∈ range N, |q 0 - q N| / N :=
    Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hN.ne')
      (fun t ht => h t (Finset.mem_range.mp ht))
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hN'] at h2
  linarith

/-- Some term is at least the average in absolute value. -/
theorem exists_abs_ge_avg [Nonempty Ω] (u : Ω → ℝ) :
    ∃ ω, |∑ ω, u ω| / Fintype.card Ω ≤ |u ω| := by
  by_contra h
  push Not at h
  have h1 : |∑ ω, u ω| ≤ ∑ ω, |u ω| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ ω, |u ω| < ∑ _ω : Ω, |∑ ω, u ω| / Fintype.card Ω :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun ω _ => h ω)
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hc] at h2
  linarith

/-- Resampling one coordinate of a uniformly random function keeps it uniform. -/
theorem sum_resample [DecidableEq I] (e : I) (h : (I → X) → ℝ) :
    ∑ ω : I → X, ∑ z : X, h (Function.update ω e z) = Fintype.card X * ∑ ω, h ω := by
  set φ := Equiv.funSplitAt e X
  have hupd : ∀ (x z : X) (r : {j // j ≠ e} → X),
      Function.update (φ.symm (x, r)) e z = φ.symm (z, r) := by
    intro x z r
    funext j
    by_cases hj : j = e
    · subst hj
      simp [φ, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [φ, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  rw [← Equiv.sum_comp φ.symm (fun ω => ∑ z : X, h (Function.update ω e z)),
    ← Equiv.sum_comp φ.symm h]
  simp only [Fintype.sum_prod_type, hupd]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm]

/-- From many samples to one (the hybrid argument). If a test `F` of `N = |I|` values tells
`N` independent samples of `g` apart from `N` uniform values with advantage `δ`, then for some
position `e` and some fixed values `c` at the other positions, the test with one free value at
`e` tells one sample of `g` apart from one uniform value with advantage at least `δ / N`. -/
theorem multi_sample [DecidableEq I] [Nonempty I] [Nonempty A] [Nonempty B] (g : A → B)
    (F : (I → B) → Bool) :
    ∃ (e : I) (c : I → B),
      |prob (fun L : I → A => F (fun i => g (L i))) - prob F| / Fintype.card I ≤
        |prob (fun u : A => F (Function.update c e (g u))) -
          prob (fun y : B => F (Function.update c e y))| := by
  set σ := Fintype.equivFin I
  set N := Fintype.card I
  let hyb : ℕ → (I → A × B) → I → B :=
    fun t ω i => if (σ i : ℕ) < t then (ω i).2 else g (ω i).1
  let q : ℕ → ℝ := fun t => prob (fun ω => F (hyb t ω))
  let ψ := Equiv.arrowProdEquivProdArrow I (fun _ => A) (fun _ => B)
  have hq0 : q 0 = prob (fun L : I → A => F (fun i => g (L i))) := by
    have : (fun ω => F (hyb 0 ω)) =
        fun ω => (fun p : (I → A) × (I → B) => F (fun i => g (p.1 i))) (ψ ω) := by
      funext ω
      simp [hyb, ψ]
    simp only [q]
    rw [this, prob_equiv ψ (fun p : (I → A) × (I → B) => F (fun i => g (p.1 i))),
      prob_fst (fun L : I → A => F (fun i => g (L i)))]
  have hqN : q N = prob F := by
    have : (fun ω => F (hyb N ω)) =
        fun ω => (fun p : (I → A) × (I → B) => F p.2) (ψ ω) := by
      funext ω
      simp only [hyb, ψ, Equiv.arrowProdEquivProdArrow_apply]
      congr 1
      funext i
      simp [(σ i).isLt]
    simp only [q]
    rw [this, prob_equiv ψ (fun p : (I → A) × (I → B) => F p.2), prob_snd F]
  obtain ⟨t, ht, hstep⟩ := telescope q N Fintype.card_pos
  set e := σ.symm ⟨t, ht⟩
  have hσe : (σ e : ℕ) = t := by simp [e]
  let P1 : (I → B) → ℝ := fun c => prob (fun u : A => F (Function.update c e (g u)))
  let P2 : (I → B) → ℝ := fun c => prob (fun y : B => F (Function.update c e y))
  have hupd1 : ∀ ω (z : A × B), hyb t (Function.update ω e z) =
      Function.update (hyb t ω) e (g z.1) := by
    intro ω z
    funext i
    by_cases hi : i = e
    · subst hi
      simp [hyb, hσe]
    · simp [hyb, Function.update_of_ne hi]
  have hupd2 : ∀ ω (z : A × B), hyb (t + 1) (Function.update ω e z) =
      Function.update (hyb t ω) e z.2 := by
    intro ω z
    funext i
    by_cases hi : i = e
    · subst hi
      simp [hyb, hσe]
    · have hne : (σ i : ℕ) ≠ t := by
        intro h'
        apply hi
        apply σ.injective
        exact Fin.ext (h'.trans hσe.symm)
      have : ((σ i : ℕ) < t + 1) ↔ ((σ i : ℕ) < t) := by omega
      simp [hyb, Function.update_of_ne hi, this]
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hinner : ∀ ω : I → A × B,
      ∑ z : A × B, (ind (F (hyb t (Function.update ω e z))) -
        ind (F (hyb (t + 1) (Function.update ω e z)))) =
      Fintype.card A * Fintype.card B * (P1 (hyb t ω) - P2 (hyb t ω)) := by
    intro ω
    simp only [hupd1, hupd2, Fintype.sum_prod_type, Finset.sum_sub_distrib, P1, P2, prob]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    field_simp
  have hdiff : q t - q (t + 1) =
      (∑ ω : I → A × B, (P1 (hyb t ω) - P2 (hyb t ω))) / Fintype.card (I → A × B) := by
    have hres := sum_resample e (fun ω : I → A × B =>
      ind (F (hyb t ω)) - ind (F (hyb (t + 1) ω)))
    simp only [hinner, Fintype.card_prod] at hres
    rw [← Finset.mul_sum, Nat.cast_mul] at hres
    have hsum : ∑ ω, (P1 (hyb t ω) - P2 (hyb t ω)) =
        ∑ ω : I → A × B, (ind (F (hyb t ω)) - ind (F (hyb (t + 1) ω))) := by
      have hAB : (Fintype.card A : ℝ) * Fintype.card B ≠ 0 := mul_ne_zero hA hB
      exact mul_left_cancel₀ hAB hres
    simp only [q, prob]
    rw [hsum, Finset.sum_sub_distrib, sub_div]
  obtain ⟨ω, hω⟩ := exists_abs_ge_avg (fun ω : I → A × B => P1 (hyb t ω) - P2 (hyb t ω))
  refine ⟨e, hyb t ω, ?_⟩
  have hc : (0 : ℝ) < Fintype.card (I → A × B) := by exact_mod_cast Fintype.card_pos
  rw [hq0, hqN] at hstep
  calc _ ≤ |q t - q (t + 1)| := hstep
    _ = |∑ ω : I → A × B, (P1 (hyb t ω) - P2 (hyb t ω))| / Fintype.card (I → A × B) := by
        rw [hdiff, abs_div, abs_of_pos hc]
    _ ≤ _ := hω

end NaturalProofs
