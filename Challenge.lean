/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Mathlib

@[expose] public section

/-!
# Definitions of the statement

Every definition that the statement of `NaturalProofs.natural_proofs_barrier` uses, in one
module: Boolean circuits (`Wire` to `Circuit.eval`), natural and useful properties of Boolean
functions (`Property` to `UsefulAgainstPPoly`), and pseudorandom generators (`GenInPPoly`,
`HardnessAtLeast`). The other files prove things about them. The Palomar Challenge
(`Challenge.lean`) is a verbatim copy of this module followed by the statement.

The definitions follow A. A. Razborov and S. Rudich, *Natural proofs*, J. Comput. System Sci.
55 (1997), 24–35, Sections 2 and 4.
-/

namespace NaturalProofs

/-! ### Boolean circuits -/

/-- A wire of a circuit with inputs indexed by `α`: an input variable, a constant, or the output
of gate number `i` (gates are numbered from `0` in the order they are listed). -/
inductive Wire (α : Type) where
  | input (a : α)
  | const (b : Bool)
  | gate (i : ℕ)

/-- A gate with fan-in at most two over the basis `{¬, ∧, ∨}`. -/
inductive Gate (α : Type) where
  | not (w : Wire α)
  | and (w₁ w₂ : Wire α)
  | or (w₁ w₂ : Wire α)

/-- The value of a wire, given the input `x` and the values `vals` of the gates computed so far.
A wire that names a gate not yet computed reads `false`, so every list of gates is a circuit:
such a wire behaves as the constant `false`. -/
def Wire.eval {α : Type} (x : α → Bool) (vals : List Bool) : Wire α → Bool
  | .input a => x a
  | .const b => b
  | .gate i => vals.getD i false

/-- The value of a gate, given the input `x` and the values `vals` of the earlier gates. -/
def Gate.eval {α : Type} (x : α → Bool) (vals : List Bool) : Gate α → Bool
  | .not w => !(w.eval x vals)
  | .and w₁ w₂ => w₁.eval x vals && w₂.eval x vals
  | .or w₁ w₂ => w₁.eval x vals || w₂.eval x vals

/-- The values of all gates of a list, computed in order: gate `i` sees the values of gates
`0, …, i - 1`. -/
def evalGates {α : Type} (x : α → Bool) (gs : List (Gate α)) : List Bool :=
  gs.foldl (fun vals g => vals ++ [g.eval x vals]) []

/-- A single-output Boolean circuit with inputs indexed by `α`: a list of gates and an output
wire. -/
structure Circuit (α : Type) where
  gates : List (Gate α)
  output : Wire α

/-- The size of a circuit is its number of gates. -/
def Circuit.size {α : Type} (C : Circuit α) : ℕ := C.gates.length

/-- The Boolean function computed by a circuit. -/
def Circuit.eval {α : Type} (C : Circuit α) (x : α → Bool) : Bool :=
  C.output.eval x (evalGates x C.gates)

/-! ### Natural properties -/

/-- Boolean functions of `n` variables. A function is its own truth table: a circuit whose
inputs are indexed by `Fin n → Bool` reads a truth table of `2 ^ n` bits. -/
abbrev BoolFn (n : ℕ) := (Fin n → Bool) → Bool

/-- A combinatorial property of Boolean functions: a set `C n` of functions for each `n`. -/
abbrev Property := (n : ℕ) → Set (BoolFn n)

/-- `P/poly`-constructivity: membership `f ∈ C n` is computed from the truth table of `f` by a
circuit of size `2 ^ O(n)`, polynomial in the truth table length `2 ^ n`. -/
def Constructive (C : Property) : Prop :=
  ∃ c n₀ : ℕ, ∀ n ≥ n₀, ∃ D : Circuit (Fin n → Bool),
    D.size ≤ 2 ^ (c * n) ∧ ∀ f : BoolFn n, D.eval f = true ↔ f ∈ C n

open Classical in
/-- Largeness: `C n` contains at least a `2 ^ (-O(n))` fraction of all `2 ^ (2 ^ n)` Boolean
functions of `n` variables. -/
def Large (C : Property) : Prop :=
  ∃ c n₀ : ℕ, ∀ n ≥ n₀,
    2 ^ (2 ^ n) ≤ (Finset.univ.filter (fun f : BoolFn n => f ∈ C n)).card * 2 ^ (c * n)

/-- A `P/poly`-natural property: `C` contains a property `C'` that is constructive and large. -/
def IsNatural (C : Property) : Prop :=
  ∃ C' : Property, (∀ n, C' n ⊆ C n) ∧ Constructive C' ∧ Large C'

/-- Usefulness against `P/poly`: functions in `C` have super-polynomial circuit size. For every
`d`, for all large `n`, every circuit computing a function in `C n` has more than `n ^ d`
gates. -/
def UsefulAgainstPPoly (C : Property) : Prop :=
  ∀ d : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ f ∈ C n, ∀ D : Circuit (Fin n), D.eval = f → n ^ d < D.size

/-! ### Pseudorandom generators -/

/-- A generator `G k : {0,1}^k → {0,1}^(2k)` in `P/poly`: every output bit of `G k` is computed
by a circuit of size polynomial in `k`. -/
def GenInPPoly (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool) : Prop :=
  ∃ c : ℕ, ∀ k (j : Fin (2 * k)), ∃ D : Circuit (Fin k),
    D.size ≤ k ^ c + c ∧ ∀ x, D.eval x = G k x j

/-- The hardness of `G k` is at least `T`. The hardness is the least `S` such that some circuit
`D` of size at most `S` distinguishes the output of `G k` on a uniformly random seed from a
uniformly random string of `2k` bits with advantage at least `1 / S`. -/
def HardnessAtLeast (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool) (k : ℕ) (T : ℝ) :
    Prop :=
  ∀ (S : ℕ) (D : Circuit (Fin (2 * k))), 0 < S → D.size ≤ S →
    (1 : ℝ) / S ≤
      |((Finset.univ.filter (fun x : Fin k → Bool => D.eval (G k x) = true)).card : ℝ) / 2 ^ k -
        ((Finset.univ.filter (fun y : Fin (2 * k) → Bool => D.eval y = true)).card : ℝ) /
          2 ^ (2 * k)| →
    T ≤ S

end NaturalProofs

namespace NaturalProofs

/-- **The natural proofs barrier** (Razborov–Rudich 1997, Theorem 4.1). If there is a generator
`G k : {0,1}^k → {0,1}^(2k)` in `P/poly` whose hardness is at least `2 ^ (k ^ ε)` for some
`ε > 0` and infinitely many `k`, then no `P/poly`-natural property is useful against `P/poly`. -/
theorem natural_proofs_barrier (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
    (hG : GenInPPoly G) (ε : ℝ) (hε : 0 < ε)
    (hH : ∀ k₀ : ℕ, ∃ k ≥ k₀, HardnessAtLeast G k (2 ^ ((k : ℝ) ^ ε))) :
    ¬ ∃ C : Property, IsNatural C ∧ UsefulAgainstPPoly C := by
  sorry

end NaturalProofs
