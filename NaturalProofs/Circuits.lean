/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import NaturalProofs.Defs

@[expose] public section

/-!
# Circuit constructions

Multi-output circuits (`MCircuit`) and the operations the proof uses to build circuits: placing
one circuit after another (`extend`, `comp`), running circuits side by side (`par`), renaming
inputs and outputs (`mapIn`, `mapOut`), and circuits without gates (`wires`). Each operation
comes with its value and its size.

All operations rest on one fact (`evalFrom_rw`): appending a renumbered copy of a gate list after
gates whose values are `acc` computes `acc` followed by the values of the original list.
-/

namespace NaturalProofs

variable {α β γ δ : Type}

/-- The gate values of `gs` computed after gates whose values are `acc`. -/
def evalFrom (x : α → Bool) (acc : List Bool) (gs : List (Gate α)) : List Bool :=
  gs.foldl (fun vals g => vals ++ [g.eval x vals]) acc

theorem evalGates_eq (x : α → Bool) (gs : List (Gate α)) :
    evalGates x gs = evalFrom x [] gs := rfl

theorem evalFrom_append (x : α → Bool) (acc : List Bool) (gs₁ gs₂ : List (Gate α)) :
    evalFrom x acc (gs₁ ++ gs₂) = evalFrom x (evalFrom x acc gs₁) gs₂ := by
  simp [evalFrom, List.foldl_append]

theorem length_evalFrom (x : α → Bool) (acc : List Bool) (gs : List (Gate α)) :
    (evalFrom x acc gs).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [evalFrom]
  | cons g gs ih =>
    simp only [evalFrom, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

theorem length_evalGates (x : α → Bool) (gs : List (Gate α)) :
    (evalGates x gs).length = gs.length := by
  simp [evalGates_eq, length_evalFrom]

/-! ### Renumbering wires -/

/-- Renumber a wire: inputs become the wires `σ a`, gate `i` becomes gate `i + off`. -/
def Wire.rw (off : ℕ) (σ : α → Wire β) : Wire α → Wire β
  | .input a => σ a
  | .const b => .const b
  | .gate i => .gate (i + off)

/-- Renumber the wires of a gate. -/
def Gate.rw (off : ℕ) (σ : α → Wire β) : Gate α → Gate β
  | .not w => .not (w.rw off σ)
  | .and w₁ w₂ => .and (w₁.rw off σ) (w₂.rw off σ)
  | .or w₁ w₂ => .or (w₁.rw off σ) (w₂.rw off σ)

/-- A wire is local to the first `n` gates if it names none of the later gates. -/
def Wire.Local (n : ℕ) : Wire β → Prop
  | .gate j => j < n
  | _ => True

/-- Replace a wire that names a gate beyond the first `n` by the constant `false`, which is the
value it reads after `n` gates. -/
def Wire.san (n : ℕ) : Wire β → Wire β
  | .gate j => if j < n then .gate j else .const false
  | w => w

theorem Wire.local_san (n : ℕ) (w : Wire β) : (w.san n).Local n := by
  cases w with
  | gate j => by_cases h : j < n <;> simp [Wire.san, Wire.Local, h]
  | _ => simp [Wire.san, Wire.Local]

theorem Wire.eval_san (x : β → Bool) (acc : List Bool) (w : Wire β) :
    (w.san acc.length).eval x acc = w.eval x acc := by
  cases w with
  | gate j =>
    by_cases h : j < acc.length
    · simp [Wire.san, h]
    · simp [Wire.san, h, Wire.eval]
  | _ => simp [Wire.san]

theorem Wire.eval_local (x : β → Bool) (acc W : List Bool) (w : Wire β)
    (h : w.Local acc.length) : w.eval x (acc ++ W) = w.eval x acc := by
  cases w with
  | gate j =>
    show (acc ++ W).getD j false = acc.getD j false
    exact List.getD_append _ _ _ _ h
  | _ => simp [Wire.eval]

theorem Wire.eval_rw (x : β → Bool) (acc W : List Bool) (σ : α → Wire β)
    (hσ : ∀ a, (σ a).Local acc.length) (w : Wire α) :
    (w.rw acc.length σ).eval x (acc ++ W) = w.eval (fun a => (σ a).eval x acc) W := by
  cases w with
  | input a =>
    simp only [Wire.rw]
    exact Wire.eval_local _ _ _ _ (hσ a)
  | const b => simp [Wire.rw, Wire.eval]
  | gate i =>
    simp only [Wire.rw, Wire.eval]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp

theorem Gate.eval_rw (x : β → Bool) (acc W : List Bool) (σ : α → Wire β)
    (hσ : ∀ a, (σ a).Local acc.length) (g : Gate α) :
    (g.rw acc.length σ).eval x (acc ++ W) = g.eval (fun a => (σ a).eval x acc) W := by
  cases g <;> simp [Gate.rw, Gate.eval, Wire.eval_rw x acc W σ hσ]

theorem evalFrom_rw (x : β → Bool) (acc W : List Bool) (σ : α → Wire β)
    (hσ : ∀ a, (σ a).Local acc.length) (gs : List (Gate α)) :
    evalFrom x (acc ++ W) (gs.map (Gate.rw acc.length σ)) =
      acc ++ evalFrom (fun a => (σ a).eval x acc) W gs := by
  induction gs generalizing W with
  | nil => simp [evalFrom]
  | cons g gs ih =>
    simp only [List.map_cons, evalFrom, List.foldl_cons] at ih ⊢
    rw [Gate.eval_rw x acc W σ hσ, List.append_assoc, ih]

/-! ### Multi-output circuits -/

/-- A Boolean circuit with inputs indexed by `α` and outputs indexed by `γ`. -/
structure MCircuit (α γ : Type) where
  gates : List (Gate α)
  out : γ → Wire α

namespace MCircuit

/-- The number of gates. -/
def size (C : MCircuit α γ) : ℕ := C.gates.length

/-- The value of output `c` on input `x`. -/
def eval (C : MCircuit α γ) (x : α → Bool) (c : γ) : Bool :=
  (C.out c).eval x (evalGates x C.gates)

/-- The single-output circuit of output `c`. -/
def toCircuit (C : MCircuit α γ) (c : γ) : Circuit α := ⟨C.gates, C.out c⟩

theorem toCircuit_eval (C : MCircuit α γ) (c : γ) (x : α → Bool) :
    (C.toCircuit c).eval x = C.eval x c := rfl

theorem toCircuit_size (C : MCircuit α γ) (c : γ) : (C.toCircuit c).size = C.size := rfl

/-- A single-output circuit as a circuit with one output. -/
def ofCircuit (C : Circuit α) : MCircuit α Unit := ⟨C.gates, fun _ => C.output⟩

theorem ofCircuit_eval (C : Circuit α) (x : α → Bool) (u : Unit) :
    (ofCircuit C).eval x u = C.eval x := rfl

theorem ofCircuit_size (C : Circuit α) : (ofCircuit C).size = C.size := rfl

/-- A circuit without gates whose outputs are the wires `w`: inputs and constants. -/
def wires (w : γ → Wire α) : MCircuit α γ := ⟨[], w⟩

theorem wires_eval (w : γ → Wire α) (x : α → Bool) (c : γ) :
    (wires w).eval x c = (w c).eval x [] := rfl

theorem wires_size (w : γ → Wire α) : (wires w).size = 0 := rfl

/-- A circuit with the single gate `g`. -/
def gate1 (g : Gate α) : MCircuit α Unit := ⟨[g], fun _ => .gate 0⟩

theorem gate1_eval (g : Gate α) (x : α → Bool) (u : Unit) :
    (gate1 g).eval x u = g.eval x [] := by
  simp [gate1, eval, evalGates, Wire.eval]

theorem gate1_size (g : Gate α) : (gate1 g).size = 1 := rfl

/-- Rename the outputs: output `c'` of the new circuit is output `g c'` of `C`. -/
def mapOut (g : δ → γ) (C : MCircuit α γ) : MCircuit α δ := ⟨C.gates, C.out ∘ g⟩

theorem mapOut_eval (g : δ → γ) (C : MCircuit α γ) (x : α → Bool) (c : δ) :
    (C.mapOut g).eval x c = C.eval x (g c) := rfl

theorem mapOut_size (g : δ → γ) (C : MCircuit α γ) : (C.mapOut g).size = C.size := rfl

/-- Rename the inputs: input `a` of `C` reads input `f a` of the new circuit. -/
def mapIn (f : α → β) (C : MCircuit α γ) : MCircuit β γ :=
  ⟨C.gates.map (Gate.rw 0 (fun a => .input (f a))), fun c => (C.out c).rw 0 (fun a => .input (f a))⟩

theorem mapIn_eval (f : α → β) (C : MCircuit α γ) (x : β → Bool) (c : γ) :
    (C.mapIn f).eval x c = C.eval (x ∘ f) c := by
  have hσ : ∀ a, (Wire.input (f a) : Wire β).Local ([] : List Bool).length :=
    fun _ => trivial
  have h := evalFrom_rw x [] [] (fun a => .input (f a)) hσ C.gates
  simp only [List.nil_append, List.length_nil] at h
  simp only [eval, mapIn, evalGates_eq]
  rw [h]
  have := Wire.eval_rw x [] (evalFrom (fun a => (Wire.input (f a) : Wire β).eval x []) [] C.gates)
    (fun a => .input (f a)) hσ (C.out c)
  simp only [List.nil_append, List.length_nil] at this
  rw [this]
  rfl

theorem mapIn_size (f : α → β) (C : MCircuit α γ) : (C.mapIn f).size = C.size := by
  simp [mapIn, size]

/-- The input renaming used by `extend`: `C` reads the inputs of `E` and the outputs of `E`. -/
def extendσ (E : MCircuit β α) : β ⊕ α → Wire β :=
  Sum.elim Wire.input (fun a => (E.out a).san E.gates.length)

/-- Place `C` after `E`. The inputs of `C` are the inputs of `E` (`Sum.inl`) and the outputs of
`E` (`Sum.inr`). The outputs are those of `E` (`Sum.inl`) and those of `C` (`Sum.inr`). -/
def extend (E : MCircuit β α) (C : MCircuit (β ⊕ α) γ) : MCircuit β (α ⊕ γ) where
  gates := E.gates ++ C.gates.map (Gate.rw E.gates.length (extendσ E))
  out := Sum.elim (fun a => (E.out a).san E.gates.length)
    (fun c => (C.out c).rw E.gates.length (extendσ E))

theorem extend_size (E : MCircuit β α) (C : MCircuit (β ⊕ α) γ) :
    (extend E C).size = E.size + C.size := by
  simp [extend, size]

theorem extend_eval (E : MCircuit β α) (C : MCircuit (β ⊕ α) γ) (x : β → Bool) :
    (extend E C).eval x =
      Sum.elim (E.eval x) (C.eval (Sum.elim x (E.eval x))) := by
  set V := evalGates x E.gates with hV
  have hlen : V.length = E.gates.length := length_evalGates x E.gates
  have hσ : ∀ s, (extendσ E s).Local V.length := by
    intro s
    cases s with
    | inl b => trivial
    | inr a => rw [hlen]; exact Wire.local_san _ _
  have hx : (fun s => (extendσ E s).eval x V) = Sum.elim x (E.eval x) := by
    funext s
    cases s with
    | inl b => rfl
    | inr a =>
      simp only [extendσ, Sum.elim_inr]
      rw [← hlen, Wire.eval_san]
      rfl
  have hgates : evalGates x (extend E C).gates = V ++ evalGates (Sum.elim x (E.eval x)) C.gates := by
    have key := evalFrom_rw x V [] _ hσ C.gates
    simp only [List.append_nil] at key
    simp only [extend, evalGates_eq, evalFrom_append]
    rw [← evalGates_eq, ← hV, ← hlen, key, hx]
  funext s
  cases s with
  | inl a =>
    simp only [eval, hgates, Sum.elim_inl]
    simp only [extend, Sum.elim_inl]
    rw [← hlen, Wire.eval_local _ _ _ _ (Wire.local_san _ _), Wire.eval_san]
  | inr c =>
    simp only [eval, hgates, Sum.elim_inr]
    simp only [extend, Sum.elim_inr]
    rw [← hlen, Wire.eval_rw x V _ _ hσ, hx]

/-- Composition: `C` reads the outputs of `E`. -/
def comp (C : MCircuit α γ) (E : MCircuit β α) : MCircuit β γ :=
  (extend E (C.mapIn Sum.inr)).mapOut Sum.inr

theorem comp_eval (C : MCircuit α γ) (E : MCircuit β α) (x : β → Bool) (c : γ) :
    (C.comp E).eval x c = C.eval (E.eval x) c := by
  simp only [comp, mapOut_eval, extend_eval, Sum.elim_inr, mapIn_eval]
  rfl

theorem comp_size (C : MCircuit α γ) (E : MCircuit β α) :
    (C.comp E).size = E.size + C.size := by
  simp [comp, mapOut_size, extend_size, mapIn_size]

/-- Single-output circuits `E a`, one for each `a` in the list `l`, side by side. Output `a` is
the output of `E a` (and `false` for `a` not in `l`). -/
def par [DecidableEq α] (E : α → MCircuit β Unit) : List α → MCircuit β α
  | [] => wires (fun _ => .const false)
  | a :: l =>
    (extend (E a) ((par E l).mapIn Sum.inl)).mapOut
      (fun b => if b = a then Sum.inl () else Sum.inr b)

theorem par_eval [DecidableEq α] (E : α → MCircuit β Unit) (l : List α) (x : β → Bool)
    (b : α) (hb : b ∈ l) : (par E l).eval x b = (E b).eval x () := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
    simp only [par, mapOut_eval, extend_eval]
    by_cases h : b = a
    · subst h
      simp
    · simp only [h, ite_false, Sum.elim_inr, mapIn_eval]
      exact ih (by simpa [h] using hb)

theorem par_size_le [DecidableEq α] (E : α → MCircuit β Unit) (l : List α) (B : ℕ)
    (hE : ∀ a, (E a).size ≤ B) : (par E l).size ≤ l.length * B := by
  induction l with
  | nil => simp [par, wires_size]
  | cons a l ih =>
    simp only [par, mapOut_size, extend_size, mapIn_size, List.length_cons]
    have := hE a
    nlinarith

/-- `par` over all elements of a finite type. -/
noncomputable def parAll [Fintype α] [DecidableEq α] (E : α → MCircuit β Unit) : MCircuit β α :=
  par E (Finset.univ : Finset α).toList

theorem parAll_eval [Fintype α] [DecidableEq α] (E : α → MCircuit β Unit) (x : β → Bool)
    (b : α) : (parAll E).eval x b = (E b).eval x () :=
  par_eval E _ x b (by simp)

theorem parAll_size_le [Fintype α] [DecidableEq α] (E : α → MCircuit β Unit) (B : ℕ)
    (hE : ∀ a, (E a).size ≤ B) : (parAll E).size ≤ Fintype.card α * B := by
  have := par_size_le E (Finset.univ : Finset α).toList B hE
  rw [Finset.length_toList, Finset.card_univ] at this
  exact this

end MCircuit

end NaturalProofs
