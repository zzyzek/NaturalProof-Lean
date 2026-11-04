/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import NaturalProofs.Defs
public import NaturalProofs.Prob

@[expose] public section

/-!
# Sanity checks on the definitions

Each hypothesis of `natural_proofs_barrier` can hold or fail. The property of all functions is
natural (`isNatural_univ`). The empty property is useful against `P/poly`
(`usefulAgainstPPoly_empty`). The generator that outputs only zeros has hardness below `3`
(`not_hardnessAtLeast_zero`): a circuit that reads one output bit tells it apart from a uniform
string with advantage `1 / 2`.
-/

namespace NaturalProofs

theorem isNatural_univ : IsNatural (fun _ => Set.univ) := by
  classical
  refine ⟨fun _ => Set.univ, fun _ => le_rfl, ⟨0, 0, fun n _ => ⟨⟨[], .const true⟩, ?_, ?_⟩⟩,
    ⟨0, 0, fun n _ => ?_⟩⟩
  · simp [Circuit.size]
  · intro f
    simp [Circuit.eval, Wire.eval]
  · simp

theorem usefulAgainstPPoly_empty : UsefulAgainstPPoly (fun _ => ∅) :=
  fun _ => ⟨0, fun _ _ f hf => by simp at hf⟩

theorem not_hardnessAtLeast_zero (k : ℕ) (hk : 0 < k) :
    ¬ HardnessAtLeast (fun _ _ _ => false) k 3 := by
  intro h
  let j0 : Fin (2 * k) := ⟨0, by omega⟩
  let D : Circuit (Fin (2 * k)) := ⟨[], .input j0⟩
  have h1 : prob (fun x : Fin k → Bool => D.eval ((fun _ _ _ => false) k x)) = 0 := by
    simp [prob, ind, D, Circuit.eval, Wire.eval]
  have h2 : prob (fun y : Fin (2 * k) → Bool => D.eval y) = 1 / 2 := by
    have := prob_equiv (Equiv.funSplitAt j0 Bool) (fun p : Bool × ({j // j ≠ j0} → Bool) => p.1)
    simp only [Equiv.funSplitAt_apply] at this
    change prob (fun y : Fin (2 * k) → Bool => y j0) = 1 / 2
    rw [this, prob_fst (fun b : Bool => b)]
    simp [prob, ind]
  have c1 : (((Finset.univ.filter (fun x : Fin k → Bool =>
      D.eval ((fun _ _ _ => false) k x) = true)).card : ℝ) / 2 ^ k) =
      prob (fun x : Fin k → Bool => D.eval ((fun _ _ _ => false) k x)) := by
    rw [prob_eq_card_filter]
    simp
  have c2 : (((Finset.univ.filter (fun y : Fin (2 * k) → Bool => D.eval y = true)).card : ℝ) /
      2 ^ (2 * k)) = prob (fun y : Fin (2 * k) → Bool => D.eval y) := by
    rw [prob_eq_card_filter]
    simp
  have := h 2 D (by norm_num) (by simp [D, Circuit.size]) (by
    rw [c1, c2, h1, h2]
    norm_num)
  norm_num at this

end NaturalProofs
