# The natural proofs barrier in Lean 4

A Lean 4 proof of Theorem 4.1 of A. A. Razborov and S. Rudich, *Natural proofs*, J. Comput.
System Sci. 55 (1997), 24–35 ([doi:10.1006/jcss.1997.1494](https://doi.org/10.1006/jcss.1997.1494)).

> If a generator `G_k : {0,1}^k → {0,1}^(2k)` in `P/poly` has hardness at least `2^(k^ε)` for
> some `ε > 0` and infinitely many `k`, then no `P/poly`-natural combinatorial property is
> useful against `P/poly`.

```lean
theorem NaturalProofs.natural_proofs_barrier
    (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
    (hG : GenInPPoly G) (ε : ℝ) (hε : 0 < ε)
    (hH : ∀ k₀ : ℕ, ∃ k ≥ k₀, HardnessAtLeast G k (2 ^ ((k : ℝ) ^ ε))) :
    ¬ ∃ C : Property, IsNatural C ∧ UsefulAgainstPPoly C
```

## What is verified

The Lean kernel checks the proof of `natural_proofs_barrier`, which uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`. The statement and every definition it uses are
in [NaturalProofs/Defs.lean](NaturalProofs/Defs.lean).

What this does not cover:

- The hypothesis of the theorem, the existence of a hard generator, is an open problem in
  cryptography. The theorem is conditional on it, as in the paper.
- The statement is about circuits. It involves no algorithm and no running time.
- Only Theorem 4.1 is formalized. The corollary from hard functions stated after it, Theorems
  4.2 and 4.3 (the `AC0[2]` results), the examples of Section 3 and the formal complexity measures
  of Section 5 are not.
- That the definitions match the paper was checked by reading, not by machine. The differences
  are listed under [Definitions](#definitions).

## Definitions

- **Circuits** (`Circuit α`): a list of gates over `{¬, ∧, ∨}` with fan-in at most two, and an
  output wire. A wire is an input, a constant or the number of a gate. Size is the number of
  gates. A wire that names a gate not yet computed reads `false`, so every list of gates is a
  circuit, computing what the circuit with that wire replaced by the constant `false` computes.
- **Boolean functions** (`BoolFn n = (Fin n → Bool) → Bool`) are their own truth tables. A
  circuit with inputs indexed by `Fin n → Bool` reads the `2^n` bits of a truth table.
- **Natural** (`IsNatural C`): `C` contains a property `C'` that is *constructive* (membership
  is decided from the truth table by circuits of size `2^(c n)` for all `n ≥ n₀`) and *large*
  (`C' n` holds a fraction at least `2^(-c n)` of all functions, for all `n ≥ n₀`).
- **Useful against `P/poly`** (`UsefulAgainstPPoly C`): for every `d`, for all large `n`, every
  circuit computing a function in `C n` has more than `n^d` gates. This is the paper's
  Section 2.2 form (every sequence with `f_n ∈ C_n` infinitely often is outside `P/poly`). It
  agrees with the Section 2.1 form (every sequence with `f_n ∈ C_n` for all `n` has
  super-polynomial size) when every `C_n` is nonempty. Read literally, the Section 2.1 form holds
  vacuously when some `C_n` is empty. The property of all functions of at least one variable
  would then be natural and useful, and the theorem would fail whenever a generator meeting its
  hypothesis exists.
- **Generators in `P/poly`** (`GenInPPoly G`): each output bit of `G k` has a circuit of size
  `k^c + c`.
- **Hardness** (`HardnessAtLeast G k T`): `H(G_k) ≥ T`, where `H(G_k)` is the least `S` such that
  some circuit of size at most `S` tells `G_k(x)` (uniform `x`) apart from a uniform string of
  `2k` bits with advantage at least `1/S`. The hypothesis of the theorem negates the paper's
  "`H(G_k) ≤ 2^(k^o(1))` for every generator in `P/poly`".

[NaturalProofs/Sanity.lean](NaturalProofs/Sanity.lean) checks that the hypotheses can hold and
can fail. The property of all functions is natural, the empty property is useful against
`P/poly`, and the all-zero generator has hardness below 3.

## Proof

The proof follows the paper's.

1. From `G_k` and a seed `s`, the Goldreich–Goldwasser–Micali function `prf G k n s` of `n`
   variables follows the bits of its input down a binary tree. The root is labelled `s`, and the
   children of a node labelled `v` get the two halves of `G_k(v)`. These functions have circuits
   of polynomial size, so a useful property contains none of them, and the circuit `D` that
   decides the constructive and large `C'` rejects them all, while it accepts a fraction
   `2^(-b n)` of all functions.
2. Hybrid `i` labels the nodes at depth `i` at random. Hybrid `0` is `prf` on a random seed and
   hybrid `n` is a random function. Some step `i → i + 1` keeps advantage `1/n` of the total
   (`telescope`). That step replaces `2^i` outputs of `G` by uniform strings. Some single node,
   with all other labels fixed, keeps advantage `1/2^i` of the step (`multi_sample`).
3. With those labels wired in as constants, `D` applied to the truth table of the hybrid is a
   circuit `distC` of size `2^O(n)` in the one free string. It tells one output of `G_k` apart
   from a uniform string with advantage `2^(-O(n))`.
4. Take `m ≥ 2/ε`, a hard `k`, and the largest `n` with `n^m ≤ k`. The hardness gives
   `2^(k^ε) ≤ 2^(K n)`, while `k^ε ≥ n^2 > K n`.

| File | Contents |
| --- | --- |
| [Defs.lean](NaturalProofs/Defs.lean) | Definitions of the statement |
| [Circuits.lean](NaturalProofs/Circuits.lean) | Multi-output circuits, composition, parallel circuits, sizes |
| [Prob.lean](NaturalProofs/Prob.lean) | Uniform probabilities, averaging, the hybrid over samples (`multi_sample`) |
| [GGM.lean](NaturalProofs/GGM.lean) | GGM functions, hybrids over levels (`level_hybrid`), circuits for the generator, the functions and the distinguisher |
| [Main.lean](NaturalProofs/Main.lean) | `natural_proofs_barrier` |
| [Sanity.lean](NaturalProofs/Sanity.lean) | The hypotheses can hold and can fail |

## Building

Lean `v4.35.0-rc2` with Mathlib (pinned in `lake-manifest.json`).

```bash
lake exe cache get
lake build
```

The library builds in about 30 seconds on 4 cores (after the Mathlib cache), using about 3 GB.

## Palomar registry

[Challenge.lean](Challenge.lean) is a verbatim copy of `NaturalProofs/Defs.lean` followed by the
statement with `sorry`. It imports only Mathlib. [Solution.lean](Solution.lean) imports the
library, and [comparator.json](comparator.json) names the theorem and the permitted axioms.
Metadata is in [formalization.yaml](formalization.yaml).

## Other formalizations

Two other Lean 4 repositories address the barrier.
[crabsatellite/lean4-natural-proofs-barrier](https://github.com/crabsatellite/lean4-natural-proofs-barrier)
takes as its hypothesis that every constructive and large property accepts some output of the
generator, which is the step that the distinguisher argument proves here.
[neardws/p-vs-np-lean](https://github.com/neardws/p-vs-np-lean) states the barrier with PRF
security left undefined and the proof pending.

## Authorship

Claude (Opus 5.5, Anthropic) wrote the Lean proof and the documentation. The listed author posed
the problem and guided the work.

## License

CC0 1.0 Universal (public domain dedication). See [LICENSE](LICENSE).
