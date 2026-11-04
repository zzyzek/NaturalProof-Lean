/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import NaturalProofs.Circuits
public import NaturalProofs.Prob

@[expose] public section

/-!
# The Goldreich–Goldwasser–Micali functions

From a generator `G k : {0,1}^k → {0,1}^(2k)` and a seed `s`, the function `prf G k n s` of `n`
variables walks down a binary tree of depth `n`: the root is labelled `s`, and the children of a
node labelled `v` are labelled with the two halves of `G k v`. The value at `x` is the first bit
of the label of the leaf reached by following the bits of `x`.

The proof that these functions look random to circuits that read the whole truth table goes
through the hybrids `hybF i`. Hybrid `i` labels the nodes at depth `i` independently at random
and labels the deeper nodes by `G` as above. Hybrid `0` is `prf` on a random seed, and hybrid
`n` is a uniformly random function. The step from hybrid `i` to hybrid `i + 1` replaces `2 ^ i`
samples of `G` by uniform strings, and `multi_sample` reduces it to a single sample.
`level_hybrid` combines these steps, and `distC` is the resulting circuit that tells one output
of `G` apart from a uniform string.
-/

namespace NaturalProofs

open MCircuit

/-- Bit strings of length `k`. -/
abbrev Bits (k : ℕ) := Fin k → Bool

/-- The left (`b = false`) or right (`b = true`) half of a string of length `2k`. -/
def half {k : ℕ} (b : Bool) (y : Fin (2 * k) → Bool) : Bits k :=
  fun j => y ⟨(if b then k else 0) + j, by have := j.isLt; split <;> omega⟩

/-- The first bit of a string (`false` for the empty string). -/
def firstBit {k : ℕ} (v : Bits k) : Bool := if h : 0 < k then v ⟨0, h⟩ else false

variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)

/-- The label reached from a node labelled `v` by following the bits `bs`. -/
def walk {k : ℕ} (v : Bits k) (bs : List Bool) : Bits k :=
  bs.foldl (fun v b => half b (G k v)) v

/-- The function of `n` variables with seed `s`. -/
def prf (k n : ℕ) (s : Bits k) : BoolFn n := fun x => firstBit (walk G s (List.ofFn x))

/-- The first `i` bits of `x` (padded with `false` past `n`). -/
def pre {n : ℕ} (i : ℕ) (x : Fin n → Bool) : Fin i → Bool := fun j => (List.ofFn x).getD j false

/-- Hybrid `i`: the nodes at depth `i` carry the labels `L`. -/
def hybF {k n : ℕ} (i : ℕ) (L : (Fin i → Bool) → Bits k) : BoolFn n :=
  fun x => firstBit (walk G (L (pre i x)) ((List.ofFn x).drop i))

/-- Labels at depth `i + 1` from pairs of labels at depth `i`. -/
def expand {k i : ℕ} (M : (Fin i → Bool) → Fin (2 * k) → Bool) : (Fin (i + 1) → Bool) → Bits k :=
  fun q => half (q (Fin.last i)) (M (Fin.init q))

/-! ### Hybrids -/

theorem init_pre {n : ℕ} (i : ℕ) (x : Fin n → Bool) : Fin.init (pre (i + 1) x) = pre i x := by
  funext j
  simp [Fin.init, pre]

theorem pre_last {n : ℕ} (i : ℕ) (x : Fin n → Bool) :
    pre (i + 1) x (Fin.last i) = (List.ofFn x).getD i false := by
  simp [pre]

theorem expand_pre {k n : ℕ} (i : ℕ) (M : (Fin i → Bool) → Fin (2 * k) → Bool)
    (x : Fin n → Bool) :
    expand M (pre (i + 1) x) = half ((List.ofFn x).getD i false) (M (pre i x)) := by
  simp [expand, init_pre, pre_last]

theorem hybF_succ {k n : ℕ} (i : ℕ) (hi : i < n) (L : (Fin i → Bool) → Bits k) :
    (hybF G i L : BoolFn n) = hybF G (i + 1) (expand (fun p => G k (L p))) := by
  funext x
  simp only [hybF, expand_pre]
  have hlen : i < (List.ofFn x).length := by simpa using hi
  rw [List.drop_eq_getElem_cons hlen, List.getD_eq_getElem _ _ hlen]
  simp [walk]

theorem expand_injective (k i : ℕ) :
    Function.Injective (expand : ((Fin i → Bool) → Fin (2 * k) → Bool) → _ → Bits k) := by
  intro M M' h
  funext p j
  by_cases hj : k ≤ (j : ℕ)
  · have := congrFun (congrFun h (Fin.snoc p true)) ⟨j - k, by omega⟩
    simp only [expand, Fin.init_snoc, Fin.snoc_last, half] at this
    convert this using 2 <;> exact Fin.ext (by simp; omega)
  · have := congrFun (congrFun h (Fin.snoc p false)) ⟨j, by omega⟩
    simp only [expand, Fin.init_snoc, Fin.snoc_last, half] at this
    convert this using 2 <;> exact Fin.ext (by simp)

theorem expand_bijective (k i : ℕ) :
    Function.Bijective (expand : ((Fin i → Bool) → Fin (2 * k) → Bool) → _ → Bits k) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨expand_injective k i, ?_⟩
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_mul, ← pow_mul, pow_succ]
  ring_nf

theorem hybF_zero {k n : ℕ} (L : (Fin 0 → Bool) → Bits k) (p : Fin 0 → Bool) :
    (hybF G 0 L : BoolFn n) = prf G k n (L p) := by
  funext x
  simp only [hybF, prf, List.drop_zero]
  congr 2
  exact congrArg L (Subsingleton.elim _ _)

theorem hybF_top {k n : ℕ} (L : (Fin n → Bool) → Bits k) :
    (hybF G n L : BoolFn n) = fun x => firstBit (L x) := by
  funext x
  have hpre : pre n x = x := by
    funext j
    simp [pre]
  simp [hybF, hpre, walk, List.drop_eq_nil_of_le (by simp : (List.ofFn x).length ≤ n)]

/-- The hybrid argument over the levels of the tree. A test `T` of truth tables that tells the
functions `prf G k n s` (random seed `s`) apart from random functions with advantage `δ` tells
apart, for some depth `i < n` and some fixed labels, one output of `G k` from a uniform string
with advantage at least `δ / (n 2 ^ i)`. -/
theorem level_hybrid {k : ℕ} (hk : 0 < k) (n : ℕ) (hn : 0 < n) (T : BoolFn n → Bool) :
    ∃ i < n, ∃ (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool),
      |prob (fun s => T (prf G k n s)) - prob T| / (n * 2 ^ i) ≤
        |prob (fun u : Bits k => T (hybF G (i + 1) (expand (Function.update c e (G k u))))) -
          prob (fun y : Fin (2 * k) → Bool => T (hybF G (i + 1) (expand (Function.update c e y))))| := by
  let Q : ℕ → ℝ := fun i => prob (fun L : (Fin i → Bool) → Bits k => T (hybF G i L))
  have hQ0 : Q 0 = prob (fun s => T (prf G k n s)) := by
    have key : (fun L : (Fin 0 → Bool) → Bits k => T (hybF G 0 L)) =
        fun L => T (prf G k n (Equiv.funUnique (Fin 0 → Bool) (Bits k) L)) := by
      funext L
      rw [hybF_zero G L (fun j => j.elim0)]
      congr 2
    simp only [Q]
    rw [key]
    exact prob_equiv (Equiv.funUnique (Fin 0 → Bool) (Bits k)) (fun s => T (prf G k n s))
  have hQn : Q n = prob T := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    let φ := (Equiv.arrowCongr (Equiv.refl (Fin n → Bool))
        (Fin.consEquiv (fun _ : Fin (k' + 1) => Bool)).symm).trans
      (Equiv.arrowProdEquivProdArrow (Fin n → Bool) (fun _ => Bool) (fun _ => Fin k' → Bool))
    have : (fun L : (Fin n → Bool) → Bits (k' + 1) => T (hybF G n L)) =
        fun L => (fun p : BoolFn n × ((Fin n → Bool) → Fin k' → Bool) => T p.1) (φ L) := by
      funext L
      simp [hybF_top, φ, firstBit]
    simp only [Q]
    rw [this, prob_equiv φ (fun p : BoolFn n × ((Fin n → Bool) → Fin k' → Bool) => T p.1),
      prob_fst T]
  obtain ⟨i, hi, hstep⟩ := telescope Q n hn
  let F : ((Fin i → Bool) → Fin (2 * k) → Bool) → Bool := fun M => T (hybF G (i + 1) (expand M))
  have hQi : Q i = prob (fun L : (Fin i → Bool) → Bits k => F (fun p => G k (L p))) := by
    simp only [Q, F, ← hybF_succ G i hi]
  have hQi1 : Q (i + 1) = prob F := by
    simp only [Q, F]
    exact (prob_equiv (Equiv.ofBijective _ (expand_bijective k i))
      (fun L : (Fin (i + 1) → Bool) → Bits k => T (hybF G (i + 1) L))).symm
  obtain ⟨e, c, hms⟩ := multi_sample (G k) F
  refine ⟨i, hi, e, c, ?_⟩
  rw [hQ0, hQn, hQi, hQi1] at hstep
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat] at hms
  have h2 : (0 : ℝ) < 2 ^ i := by positivity
  calc _ = |prob (fun s => T (prf G k n s)) - prob T| / n / 2 ^ i := by rw [div_div]
    _ ≤ |prob (fun L : (Fin i → Bool) → Bits k => F (fun p => G k (L p))) - prob F| / 2 ^ i :=
        div_le_div_of_nonneg_right hstep h2.le
    _ ≤ _ := hms

/-! ### Circuits -/

section Circuits

variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))

/-- A circuit for `G k` from circuits `gc k j` for its output bits. -/
noncomputable def genC (k : ℕ) : MCircuit (Fin k) (Fin (2 * k)) :=
  parAll (fun j => ofCircuit (gc k j))

theorem genC_eval (hgc : ∀ k j x, (gc k j).eval x = G k x j) (k : ℕ) (x : Fin k → Bool) :
    (genC gc k).eval x = G k x := by
  funext j
  simp [genC, parAll_eval, ofCircuit_eval, hgc]

theorem genC_size (k B : ℕ) (hB : ∀ j, (gc k j).size ≤ B) : (genC gc k).size ≤ 2 * k * B := by
  have := parAll_size_le (fun j => ofCircuit (gc k j)) B (fun j => hB j)
  simpa [genC] using this

/-- The value of a bit source: an input bit (`Sum.inl`) or a constant (`Sum.inr`). -/
def bitval (x : β → Bool) (s : β ⊕ Bool) : Bool := Sum.elim x id s

/-- `if s then y (k + j) else y j`, with four gates. -/
def muxC (k : ℕ) (s : β ⊕ Bool) (j : Fin k) : MCircuit (β ⊕ (Fin k ⊕ Fin (2 * k))) Unit :=
  let bw : Wire (β ⊕ (Fin k ⊕ Fin (2 * k))) :=
    match s with
    | .inl b => .input (.inl b)
    | .inr c => .const c
  let hi : Wire (β ⊕ (Fin k ⊕ Fin (2 * k))) := .input (.inr (.inr ⟨k + j, by omega⟩))
  let lo : Wire (β ⊕ (Fin k ⊕ Fin (2 * k))) := .input (.inr (.inr ⟨j, by omega⟩))
  ⟨[.not bw, .and bw hi, .and (.gate 0) lo, .or (.gate 1) (.gate 2)], fun _ => .gate 3⟩

theorem muxC_eval (k : ℕ) (s : β ⊕ Bool) (j : Fin k) (z : β ⊕ (Fin k ⊕ Fin (2 * k)) → Bool) :
    (muxC k s j).eval z () =
      if bitval (fun b => z (.inl b)) s then z (.inr (.inr ⟨k + j, by omega⟩))
      else z (.inr (.inr ⟨j, by omega⟩)) := by
  cases s with
  | inl b =>
    cases h : z (.inl b) <;>
      simp [muxC, MCircuit.eval, evalGates, Gate.eval, Wire.eval, bitval, h]
  | inr c =>
    cases c <;> simp [muxC, MCircuit.eval, evalGates, Gate.eval, Wire.eval, bitval]

/-- One step down the tree: from a circuit for a label `v`, a circuit for `half b (G k v)`,
where the bit `b` comes from the source `s`. -/
noncomputable def stepC {k : ℕ} (s : β ⊕ Bool) (Cv : MCircuit β (Fin k)) : MCircuit β (Fin k) :=
  ((Cv.extend ((genC gc k).mapIn Sum.inr)).extend (parAll (muxC k s))).mapOut Sum.inr

theorem stepC_eval (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k : ℕ} (s : β ⊕ Bool)
    (Cv : MCircuit β (Fin k)) (x : β → Bool) :
    (stepC gc s Cv).eval x = half (bitval x s) (G k (Cv.eval x)) := by
  funext j
  simp only [stepC, mapOut_eval, extend_eval, Sum.elim_inr, Sum.elim_inl, parAll_eval,
    muxC_eval, mapIn_eval, Sum.elim_comp_inr, genC_eval G gc hgc, half]
  rcases s with b | b
  · cases h : x b <;> simp [bitval, h]
  · cases b <;> simp [bitval]

theorem stepC_size {k B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (s : β ⊕ Bool)
    (Cv : MCircuit β (Fin k)) : (stepC gc s Cv).size ≤ Cv.size + (2 * k * B + 4 * k) := by
  have h1 := genC_size gc k B hB
  have h2 := parAll_size_le (muxC k s) 4 (fun j => le_refl _)
  simp only [stepC, mapOut_size, extend_size, mapIn_size, Fintype.card_fin] at h2 ⊢
  omega

/-- A walk down the tree along the bit sources `ss`, from a circuit for the start label. -/
noncomputable def walkC {k : ℕ} (Cv : MCircuit β (Fin k)) (ss : List (β ⊕ Bool)) :
    MCircuit β (Fin k) :=
  ss.foldl (fun C s => stepC gc s C) Cv

theorem walkC_eval (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k : ℕ} (Cv : MCircuit β (Fin k))
    (ss : List (β ⊕ Bool)) (x : β → Bool) :
    (walkC gc Cv ss).eval x = walk G (Cv.eval x) (ss.map (bitval x)) := by
  induction ss generalizing Cv with
  | nil => rfl
  | cons s ss ih =>
    simp only [walkC, List.foldl_cons] at ih ⊢
    rw [ih, stepC_eval G gc hgc]
    rfl

theorem walkC_size {k B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (Cv : MCircuit β (Fin k))
    (ss : List (β ⊕ Bool)) :
    (walkC gc Cv ss).size ≤ Cv.size + ss.length * (2 * k * B + 4 * k) := by
  induction ss generalizing Cv with
  | nil => simp [walkC]
  | cons s ss ih =>
    simp only [walkC, List.foldl_cons, List.length_cons] at ih ⊢
    have := ih (stepC gc s Cv)
    have := stepC_size gc hB s Cv
    nlinarith

/-- A circuit for `prf G k n s`: the seed is wired in as constants. -/
noncomputable def prfC {k : ℕ} (hk : 0 < k) (n : ℕ) (s : Bits k) : Circuit (Fin n) :=
  ((walkC gc (wires (fun j => .const (s j))) ((List.finRange n).map Sum.inl)).mapOut
    (fun _ : Unit => (⟨0, hk⟩ : Fin k))).toCircuit ()

theorem prfC_eval (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k : ℕ} (hk : 0 < k) (n : ℕ)
    (s : Bits k) : (prfC gc hk n s).eval = prf G k n s := by
  funext x
  simp only [prfC, toCircuit_eval, mapOut_eval, walkC_eval G gc hgc, prf, firstBit, hk,
    dite_true, List.map_map]
  congr 2
  rw [List.ofFn_eq_map]
  rfl

theorem prfC_size {k B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (hk : 0 < k) (n : ℕ) (s : Bits k) :
    (prfC gc hk n s).size ≤ n * (2 * k * B + 4 * k) := by
  have := walkC_size gc hB (wires (fun j => .const (s j))) ((List.finRange n).map Sum.inl)
  simpa [prfC, toCircuit_size, mapOut_size, wires_size] using this

/-- The start label for the leaf `x` in the distinguisher: half of the free input `y` if the
depth-`i` ancestor of `x` is `e`, and a constant otherwise. -/
noncomputable def startC {k n : ℕ} (i : ℕ) (e : Fin i → Bool)
    (c : (Fin i → Bool) → Fin (2 * k) → Bool) (x : Fin n → Bool) :
    MCircuit (Fin (2 * k)) (Fin k) :=
  let b := (List.ofFn x).getD i false
  if pre i x = e then
    wires (fun j => .input ⟨(if b then k else 0) + j, by have := j.isLt; split <;> omega⟩)
  else wires (fun j => .const (half b (c (pre i x)) j))

theorem startC_eval {k n : ℕ} (i : ℕ) (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool)
    (x : Fin n → Bool) (y : Fin (2 * k) → Bool) :
    (startC i e c x).eval y =
      half ((List.ofFn x).getD i false) (Function.update c e y (pre i x)) := by
  funext j
  by_cases h : pre i x = e
  · simp [startC, h, wires_eval, Wire.eval, half]
  · simp [startC, h, wires_eval, Wire.eval]

/-- The circuit for leaf `x` of hybrid `i + 1` with labels `expand (update c e y)`. -/
noncomputable def leafC {k n : ℕ} (hk : 0 < k) (i : ℕ) (e : Fin i → Bool)
    (c : (Fin i → Bool) → Fin (2 * k) → Bool) (x : Fin n → Bool) : MCircuit (Fin (2 * k)) Unit :=
  (walkC gc (startC i e c x) (((List.ofFn x).drop (i + 1)).map Sum.inr)).mapOut
    (fun _ => (⟨0, hk⟩ : Fin k))

theorem leafC_eval (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k n : ℕ} (hk : 0 < k) (i : ℕ)
    (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool) (x : Fin n → Bool)
    (y : Fin (2 * k) → Bool) :
    (leafC gc hk i e c x).eval y () = hybF G (i + 1) (expand (Function.update c e y)) x := by
  simp only [leafC, mapOut_eval, walkC_eval G gc hgc, startC_eval, hybF, expand_pre,
    List.map_map, firstBit, hk, dite_true]
  congr 3
  conv_rhs => rw [← List.map_id ((List.ofFn x).drop (i + 1))]
  rfl

/-- The distinguisher: the test `D` applied to the truth table of hybrid `i + 1` with labels
`expand (update c e y)`, as a circuit of the free input `y`. -/
noncomputable def distC {k n : ℕ} (hk : 0 < k) (i : ℕ) (e : Fin i → Bool)
    (c : (Fin i → Bool) → Fin (2 * k) → Bool) (D : Circuit (Fin n → Bool)) :
    Circuit (Fin (2 * k)) :=
  ((ofCircuit D).comp (parAll (leafC gc hk i e c))).toCircuit ()

theorem distC_eval (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k n : ℕ} (hk : 0 < k) (i : ℕ)
    (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool) (D : Circuit (Fin n → Bool))
    (y : Fin (2 * k) → Bool) :
    (distC gc hk i e c D).eval y = D.eval (hybF G (i + 1) (expand (Function.update c e y))) := by
  simp only [distC, toCircuit_eval, comp_eval, ofCircuit_eval]
  congr 1
  funext x
  rw [parAll_eval, leafC_eval G gc hgc]

theorem distC_size {k n B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (hk : 0 < k) (i : ℕ)
    (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool) (D : Circuit (Fin n → Bool)) :
    (distC gc hk i e c D).size ≤ 2 ^ n * (n * (2 * k * B + 4 * k)) + D.size := by
  have hleaf : ∀ x : Fin n → Bool, (leafC gc hk i e c x).size ≤ n * (2 * k * B + 4 * k) := by
    intro x
    have := walkC_size gc hB (startC i e c x) (((List.ofFn x).drop (i + 1)).map Sum.inr)
    have h0 : (startC (k := k) i e c x).size = 0 := by
      unfold startC
      dsimp only
      split <;> rfl
    have hl : (((List.ofFn x).drop (i + 1)).map (Sum.inr : Bool → Fin (2 * k) ⊕ Bool)).length ≤ n := by
      simp
    simp only [leafC, mapOut_size, h0, zero_add] at this ⊢
    exact this.trans (Nat.mul_le_mul_right _ hl)
  have := parAll_size_le (leafC gc hk i e c) _ hleaf
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
  simp only [distC, toCircuit_size, comp_size, ofCircuit_size]
  omega

end Circuits

end NaturalProofs
