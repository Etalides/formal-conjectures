/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Monochromatic quantum graphs (inherited vertex colorings)

This file studies the existence of *monochromatic quantum graphs*: edge-coloured, edge-weighted
complete graphs whose perfect matchings induce vertex colourings, with the property that

- every **non-monochromatic** inherited vertex colouring has total weight `0`, while
- each of the `D` **monochromatic** colourings has total weight `1`.

In the quantum-optics motivation, such a construction corresponds to generating high-dimensional
multipartite GHZ-type states using probabilistic pair sources and linear optics (without additional
resources), where interference patterns can be expressed as weighted sums over perfect matchings.

## Main questions (informal)

- For `N = 4` and `D ≥ 4`, does there exist such a graph/weighting?
- For even `N ≥ 6` and `D ≥ 3`, does there exist such a graph/weighting?

## Formalisation sketch

A quantum graph with `N` vertices and `D` colours can be encoded by a weight function
`W : EdgeN N D α → α` (for a coefficient domain `α`).

For each assignment of vertex indices `ι : V N → Fin D`, we define a perfect-matching sum
`pmSumN N D W ι` (a sum over perfect matchings, where each matching contributes the product of the
corresponding edge weights determined by `ι`). The equation system `EqSystemN N D W` requires

`pmSumN N D W ι = 1` iff `ι` is constant (all entries equal), and `0` otherwise.

The open conjectures in this file ask for non-existence/existence of such `W` over various
coefficient domains (e.g. `ℂ`, `ℝ`, `ℤ`, and restricted integer weights).

## References

* [Krenn2017] M. Krenn, X. Gu, A. Zeilinger,
  "Quantum Experiments and Graphs: Multiparty States as Coherent Superpositions of Perfect Matchings",
  *Physical Review Letters* 119(24), 240403 (2017).

* [MO2018] [Vertex coloring inherited from perfect matchings (motivated by quantum physics)](https://mathoverflow.net/questions/311325),
  MathOverflow question 311325.

* [Gu2019] X. Gu, M. Erhard, A. Zeilinger, M. Krenn,
  "Quantum experiments and graphs II: Quantum interference, computation, and state generation",
  *PNAS* 116(10), 4147–4155 (2019).

* [Krenn2019] [Questions on the Structure of Perfect Matchings inspired by Quantum Physics](https://arxiv.org/abs/1902.06023)
  by *M. Krenn, X. Gu, U. Soltész*,
  Proc. 2nd Croatian Combinatorial Days, 57–70 (2019).

* [Chandran2022] [Edge-coloured graphs with only monochromatic perfect matchings and their connection to quantum physics](https://arxiv.org/abs/2202.05562)
  by *N. Chandran, S. Gajjala* (2022).

* [Chandran2024] [Krenn–Gu conjecture for sparse graphs](https://arxiv.org/abs/2407.00303)
  by *N. Chandran, S. Gajjala, S. Illickan, M. Krenn*, MFCS 2024.
-/

open scoped Matrix
open scoped NNReal

namespace MonochromaticQuantumGraph

/-- Vertices of $K_N$. -/
abbrev V (N : Nat) := Fin N

/-- Edge label for $K_N$ with endpoint indices in `Fin D`.

We *intend* to build edges only with `u < v` (so undirected edges are represented once),
and our enumeration always pairs the first vertex in an ordered list with a later vertex.
-/
structure EdgeN (N D : Nat) where
  u : V N
  v : V N
  i : Fin D
  j : Fin D
deriving DecidableEq

/-- Weights on edges. -/
abbrev WeightsN (N D : Nat) (α : Type) := EdgeN N D → α

/-- Helper: build an `EdgeN` from endpoints and endpoint indices. -/
def mkEdge {N D : Nat} (u v : V N) (i j : Fin D) : EdgeN N D :=
  ⟨u, v, i, j⟩

/-- Ordered vertex list $[0, 1, \ldots, N-1]$. -/
def vertices : (N : Nat) → List (V N)
  | 0 => []
  | N + 1 =>
      (0 : Fin (N + 1)) :: (vertices N).map Fin.succ

/-
## `allEqual`: "all indices are equal"

We package the property "all indices `ι v` are equal" as a chain condition along a vertex list.

Concretely, `allEqualList ι L` means that the relation `ι v = ι w` holds between adjacent elements
of `L`. We implement this with `List.IsChain`, which is convenient for later reasoning and provides
good simp/decidability support.
-/

/-- Chain-equality along a list of vertices. -/
def allEqualList {N D : Nat} (ι : V N → Fin D) (L : List (V N)) : Prop :=
  List.IsChain (fun v w => ι v = ι w) L

/-- All indices equal on `Fin N` (using the canonical ordered vertex list). -/
def allEqual {N D : Nat} (ι : V N → Fin D) : Prop :=
  allEqualList ι (vertices N)

/-- Instance: `allEqualList ι L` is decidable. -/
instance {N D : Nat} (ι : V N → Fin D) (L : List (V N)) :
    Decidable (allEqualList ι L) := by
  letI : DecidableRel (fun v w : V N => ι v = ι w) := fun v w => inferInstance
  unfold allEqualList
  infer_instance

/-- Instance: `allEqual ι` is decidable. -/
instance {N D : Nat} (ι : V N → Fin D) : Decidable (allEqual ι) := by
  unfold allEqual
  infer_instance

/-
## Perfect matching sum, general `N`

Fix a semiring `α`, a weight function `W : WeightsN N D α`, and an index assignment
`ι : V N → Fin D`. The next definitions compute the sum over perfect matchings of the complete graph
on `N` vertices, where each edge is selected with the endpoint indices given by `ι`.

We define an auxiliary function `pmSumListAux W ι n L` with a decreasing fuel parameter `n`
(used only for termination). In the intended use, we call it with `n = L.length`.

Intuition (when `n = L.length`):

* `n = 0` : the empty matching contributes `1` (empty product).
* `n = 1` : odd number of vertices, so no perfect matchings; value `0`.
* `n = n' + 2` and `L = v :: vs`:
  pair `v` with each `u ∈ vs`, multiply the edge weight by the recursive contribution on the
  remaining vertices `vs.erase u`, and sum over `u`.
-/

/-- Auxiliary perfect-matching sum on a vertex list, using a fuel parameter `n` for termination.

When called as `pmSumListAux W ι L.length L`, this computes the weighted sum over all perfect
matchings on the vertices in `L`. The recursion pairs the head vertex with each later vertex and
recurses on the remaining vertices.

For lists of odd length, there are no perfect matchings and the value is `0`. -/
def pmSumListAux {α : Type} [Semiring α] {N D : Nat}
    (W : WeightsN N D α) (ι : V N → Fin D) :
    Nat → List (V N) → α
  | 0, _ => 1
  | 1, _ => 0
  | _ + 2, [] => 1
  | _ + 2, [_] => 0
  | n + 2, v :: vs =>
      (vs.map (fun u =>
          W (mkEdge v u (ι v) (ι u)) *
            pmSumListAux W ι n (vs.erase u)
        )).sum

/-- Perfect-matching sum on a list: run `pmSumListAux` with `fuel = L.length`. -/
def pmSumList {α : Type} [Semiring α] {N D : Nat}
    (W : WeightsN N D α) (ι : V N → Fin D) (L : List (V N)) : α :=
  pmSumListAux W ι L.length L

/-- The perfect-matching sum for $K_N$: use the canonical ordered vertex list `vertices N`. -/
def pmSumN {α : Type} [Semiring α] (N D : Nat)
    (W : WeightsN N D α) (ι : V N → Fin D) : α :=
  pmSumList W ι (vertices N)

/-- The monochromatic quantum graph equation system for $K_N$.

For every index assignment $\iota : V_N \to \mathrm{Fin}\, D$, the perfect-matching sum equals $1$
if $\iota$ is constant (monochromatic inherited vertex colouring), and equals $0$ otherwise. -/
def EqSystemN {α : Type} [Semiring α] (N D : Nat) (W : WeightsN N D α) : Prop :=
  ∀ ι : V N → Fin D,
    pmSumN N D W ι =
      (if allEqual ι then (1 : α) else (0 : α))

/-
# Witnesses & theorems (sanity checks)

These proofs use `native_decide` over `ℕ` to verify the equation system computationally.
For witnesses that use only `0` and `1`, the result transfers to any semiring `α` since the
computation tree is identical. For the `ℂ` case, the proof uses `fin_cases` + `norm_num`.
-/

/-- Instance: `EqSystemN N D W` is decidable when `α` has decidable equality. -/
instance instDecidableEqSystemN {N D : Nat} {α : Type} [Semiring α] [DecidableEq α]
    (W : WeightsN N D α) : Decidable (EqSystemN N D W) :=
  Fintype.decidableForallFintype

/- ## N = 4, D = 2 (works over any semiring α): witness & proof -/
section N4_D2
variable {α : Type} [Semiring α]

def Witness4_d2 : WeightsN 4 2 α :=
  fun e =>
    if e = mkEdge 0 1 0 0 then (1 : α) else
    if e = mkEdge 2 3 0 0 then (1 : α) else
    if e = mkEdge 0 2 1 1 then (1 : α) else
    if e = mkEdge 1 3 1 1 then (1 : α) else
    (0 : α)

/-- Sanity check over `ℕ` using `native_decide`. -/
@[category test, AMS 5 14 81]
private theorem eqSystem4_d2_nat :
    EqSystemN 4 2 (Witness4_d2 (α := ℕ)) := by
  native_decide

@[category test, AMS 5 14 81]
theorem eqSystem4_has_solution_d2 :
    ∃ W : WeightsN 4 2 α, EqSystemN 4 2 W := by
  refine ⟨Witness4_d2 (α := α), ?_⟩
  intro ι
  have h :
      ∀ a b c d : Fin 2,
        pmSumN 4 2 (W := Witness4_d2 (α := α)) ![a, b, c, d] =
          (if allEqual ![a, b, c, d] then (1 : α) else (0 : α)) := by
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [pmSumN, pmSumList, pmSumListAux, vertices,
        allEqual, allEqualList, Witness4_d2, mkEdge]
  have hι : ι = ![ι 0, ι 1, ι 2, ι 3] := by funext k; fin_cases k <;> simp
  rw [hι]; exact h (ι 0) (ι 1) (ι 2) (ι 3)

end N4_D2

/- ## N = 4, D = 3 (works over any semiring α): witness & proof -/
section N4_D3
variable {α : Type} [Semiring α]

def Witness4_d3 : WeightsN 4 3 α :=
  fun e =>
    if e = mkEdge 0 1 0 0 then (1 : α) else
    if e = mkEdge 2 3 0 0 then (1 : α) else
    if e = mkEdge 0 2 1 1 then (1 : α) else
    if e = mkEdge 1 3 1 1 then (1 : α) else
    if e = mkEdge 0 3 2 2 then (1 : α) else
    if e = mkEdge 1 2 2 2 then (1 : α) else
    (0 : α)

/-- Sanity check over `ℕ` using `native_decide`. -/
@[category test, AMS 5 14 81]
private theorem eqSystem4_d3_nat :
    EqSystemN 4 3 (Witness4_d3 (α := ℕ)) := by
  native_decide

set_option maxHeartbeats 400000 in
@[category test, AMS 5 14 81]
theorem eqSystem4_has_solution_d3 :
    ∃ W : WeightsN 4 3 α, EqSystemN 4 3 W := by
  refine ⟨Witness4_d3 (α := α), ?_⟩
  intro ι
  have h :
      ∀ a b c d : Fin 3,
        pmSumN 4 3 (W := Witness4_d3 (α := α)) ![a, b, c, d] =
          (if allEqual ![a, b, c, d] then (1 : α) else (0 : α)) := by
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [pmSumN, pmSumList, pmSumListAux, vertices,
        allEqual, allEqualList, Witness4_d3, mkEdge]
  have hι : ι = ![ι 0, ι 1, ι 2, ι 3] := by funext k; fin_cases k <;> simp
  rw [hι]; exact h (ι 0) (ι 1) (ι 2) (ι 3)

end N4_D3

/- ## N = 6, D = 2 (works over any semiring α): witness & proof -/
section N6_D2
variable {α : Type} [Semiring α]

def Witness6_d2 : WeightsN 6 2 α :=
  fun e =>
    if e = mkEdge 0 1 0 0 then (1 : α) else
    if e = mkEdge 2 3 0 0 then (1 : α) else
    if e = mkEdge 4 5 0 0 then (1 : α) else
    if e = mkEdge 0 5 1 1 then (1 : α) else
    if e = mkEdge 1 2 1 1 then (1 : α) else
    if e = mkEdge 3 4 1 1 then (1 : α) else
    (0 : α)

/-- Sanity check over `ℕ` using `native_decide`. -/
@[category test, AMS 5 14 81]
private theorem eqSystem6_d2_nat :
    EqSystemN 6 2 (Witness6_d2 (α := ℕ)) := by
  native_decide

set_option maxHeartbeats 400000 in
@[category test, AMS 5 14 81]
theorem eqSystem6_has_solution_d2 :
    ∃ W : WeightsN 6 2 α, EqSystemN 6 2 W := by
  refine ⟨Witness6_d2 (α := α), ?_⟩
  intro ι
  have h :
      ∀ a b c d e f : Fin 2,
        pmSumN 6 2 (W := Witness6_d2 (α := α)) ![a, b, c, d, e, f] =
          (if allEqual ![a, b, c, d, e, f] then (1 : α) else (0 : α)) := by
    intro a b c d e f
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
      simp [pmSumN, pmSumList, pmSumListAux, vertices,
        allEqual, allEqualList, Witness6_d2, mkEdge]
  have hι : ι = ![ι 0, ι 1, ι 2, ι 3, ι 4, ι 5] := by funext k; fin_cases k <;> simp
  rw [hι]; exact h (ι 0) (ι 1) (ι 2) (ι 3) (ι 4) (ι 5)

end N6_D2

/-
# Known obstruction for nonnegative real weights (Bogdanov)

Informal proof ("Bogdanov's lemma"): see
[MathOverflow answer](https://mathoverflow.net/a/311021/531914).

We record it as `research solved` statements over `ℝ≥0`, without formalizing the proof here.
-/

/-- Bogdanov: for $N = 4$ and all $D \geq 4$, no solution exists over $\mathbb{R}_{\geq 0}$. -/
@[category research solved, AMS 5 14 81]
theorem eqSystem4_no_solution_nnreal_ge4 :
    ∀ D : Nat, D ≥ 4 →
      ¬ ∃ W : WeightsN 4 D ℝ≥0, EqSystemN 4 D W := by
  sorry

/-- Bogdanov: for all even $N \geq 6$ and $D \geq 3$, no solution exists over $\mathbb{R}_{\geq 0}$. -/
@[category research solved, AMS 5 14 81]
theorem eqSystem_no_solution_nnreal_even_ge6_ge3 :
    ∀ N D : Nat,
      N ≥ 6 → Even N → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℝ≥0, EqSystemN N D W := by
  sorry

/-
# Open conjectures

We state the same family of "no-solution" conjectures for multiple coefficient domains:

* `ℂ` (complex)
* `ℝ` (real)
* `ℤ` (integers)
* `{-1,0,1} ⊆ ℤ` (integer weights restricted pointwise to -1/0/1)

All "general" conjectures are restricted to even `N`.
-/

/- ## Open conjectures over ℂ -/

/-- For $N = 4$ and $D = 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_d4 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 4 4 ℂ, EqSystemN 4 4 W := by
  sorry

/-- For $N = 4$ and all $D \geq 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_ge4 :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 4 →
        ¬ ∃ W : WeightsN 4 D ℂ, EqSystemN 4 D W := by
  sorry

/-- For $N = 6$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 3 ℂ, EqSystemN 6 3 W := by
  sorry


/-- For $N = 6$ and $D = 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d4 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 4 ℂ, EqSystemN 6 4 W := by
  sorry


/-- For $N = 6$ and $D = 5$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d5 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 5 ℂ, EqSystemN 6 5 W := by
  sorry


/-- For $N = 6$ and $D = 6$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d6 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 6 ℂ, EqSystemN 6 6 W := by
  sorry

/-- For $N = 6$ and all $D \geq 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_ge3 :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 3 →
        ¬ ∃ W : WeightsN 6 D ℂ, EqSystemN 6 D W := by
  sorry

/-- For $N = 8$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 3 ℂ, EqSystemN 8 3 W := by
  sorry

/-- For $N = 8$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d10 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 10 ℂ, EqSystemN 8 10 W := by
  sorry

/-- For $N = 10$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 3 ℂ, EqSystemN 10 3 W := by
  sorry

/-- For $N = 10$ and $D = 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d4 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 4 ℂ, EqSystemN 10 4 W := by
  sorry

/-- For $N = 10$ and $D = 5$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d5 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 5 ℂ, EqSystemN 10 5 W := by
  sorry

/-- For $N = 10$ and $D = 6$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d6 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 6 ℂ, EqSystemN 10 6 W := by
  sorry

/-- For $N = 10$ and $D = 7$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d7 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 7 ℂ, EqSystemN 10 7 W := by
  sorry

/-- For $N = 10$ and $D = 8$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d8 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 8 ℂ, EqSystemN 10 8 W := by
  sorry

/-- For $N = 10$ and $D = 9$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d9 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 9 ℂ, EqSystemN 10 9 W := by
  sorry

/-- For $N = 10$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d10 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 10 ℂ, EqSystemN 10 10 W := by
  sorry

/-- For $N = 12$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem12_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 12 3 ℂ, EqSystemN 12 3 W := by
  sorry

/-- For $N = 14$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem14_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 14 3 ℂ, EqSystemN 14 3 W := by
  sorry

/-- For $N = 16$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem16_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 16 3 ℂ, EqSystemN 16 3 W := by
  sorry


lemma det_rank_less {n : Nat} (hn : n > 0) (L : Fin n → Fin (n - 1) → ℂ) (M : Fin (n - 1) → Fin n → ℂ) :
  Matrix.det (fun i j => ∑ k : Fin (n - 1), L i k * M k j) = 0 := by
  let L' : Matrix (Fin n) (Fin n) ℂ := fun i j =>
    if hj : j.val < n - 1 then L i ⟨j.val, hj⟩ else 0
  let M' : Matrix (Fin n) (Fin n) ℂ := fun i j =>
    if hi : i.val < n - 1 then M ⟨i.val, hi⟩ j else 0
  have h_mul : (fun i j => ∑ k : Fin (n - 1), L i k * M k j) = L' * M' := by
    ext i j
    cases n with ·simp_all -contextual[M',Matrix.mul_apply, Fin.sum_univ_castSucc, L']
  have h_det_M : M'.det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero (⟨n - 1, by omega⟩ : Fin n)
    intro j
    dsimp [M']
    rw [dif_neg]
    omega
  rw [h_mul, Matrix.det_mul, h_det_M, mul_zero]

lemma h0_lt_N {N : Nat} (h : N ≥ 4) : 0 < N := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 3) h
lemma h1_lt_N {N : Nat} (h : N ≥ 4) : 1 < N := Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) h
lemma h2_lt_N {N : Nat} (h : N ≥ 4) : 2 < N := Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1))) h

noncomputable def f0 {N : Nat} (h : N ≥ 4) : Fin N := ⟨0, h0_lt_N h⟩
noncomputable def f1 {N : Nat} (h : N ≥ 4) : Fin N := ⟨1, h1_lt_N h⟩
noncomputable def f2 {N : Nat} (h : N ≥ 4) : Fin N := ⟨2, h2_lt_N h⟩

lemma avoid_one_lt {N : Nat} (a : Fin N) (k : Fin (N - 1)) : k.val < N := by omega
lemma avoid_one_plus_lt {N : Nat} (a : Fin N) (k : Fin (N - 1)) : k.val + 1 < N := by omega

def avoid_one {N : Nat} (a : Fin N) (k : Fin (N - 1)) : Fin N :=
  if _h : k.val < a.val then ⟨k.val, avoid_one_lt a k⟩ else ⟨k.val + 1, avoid_one_plus_lt a k⟩

lemma avoid_two_lt {N : Nat} (h : N ≥ 4) (k : Fin (N - 2)) : k.val + 2 < N := by omega

def avoid_two {N : Nat} (h : N ≥ 4) (k : Fin (N - 2)) : Fin N :=
  ⟨k.val + 2, avoid_two_lt h k⟩

lemma sum_avoid_two {N : Nat} (h : N ≥ 4) (F : Fin N → ℂ) :
  (∑ u : Fin N, if u = f0 h ∨ u = f1 h then (0:ℂ) else F u) =
  ∑ k : Fin (N - 2), F (avoid_two h k) := by
  rw [← Finset.sum_subset (Finset.subset_univ ↑( Finset.univ.image (avoid_two (h))))]
  · exact ( Finset.sum_image fun and=>by simp_all[Fin.ext_iff,avoid_two]).trans ( Fintype.sum_congr _ _ fun and=>if_neg (nofun))
  norm_num[avoid_two]
  use fun and x A B=>match and with| ⟨a+2, _⟩=>(x ⟨a,by valid⟩ rfl ).elim

lemma avoid_one_ne {N : Nat} (a : Fin N) (k : Fin (N - 1)) :
  avoid_one a k ≠ a := by
  delta avoid_one
  grind

lemma avoid_two_inj {N : Nat} (h : N ≥ 4) (i j : Fin (N - 2)) :
  avoid_two h i = avoid_two h j ↔ i = j := by
  show(id _)=((id _)) ↔_
  norm_num[i.ext_iff]

lemma rank_N_contradiction {N : Nat} (hn : N - 1 > 0) (h : N ≥ 4) (L : Fin N → Fin N → ℂ) (M : Fin N → Fin N → ℂ)
  (z : Fin N → ℂ) (hz_zero : ∃ a : Fin N, ∀ b, b ≠ a → z b ≠ 0)
  (h_eq : ∀ i j, (∑ u : Fin N, if u = f0 h ∨ u = f1 h then (0:ℂ) else L u i * M u j) = if i = j then z i else 0) : False := by
  rcases hz_zero with ⟨a, ha_nz⟩
  let f := avoid_one a
  let g := avoid_two h
  let L_mat : Fin (N - 1) → Fin (N - 2) → ℂ := fun i k => L (g k) (f i)
  let M_mat : Fin (N - 2) → Fin (N - 1) → ℂ := fun k j => M (g k) (f j)
  have h_det := det_rank_less hn L_mat M_mat
  have h_mat_eq : ∀ i j, (∑ k, L_mat i k * M_mat k j) = if i = j then z (f i) else 0 := by
    intro i j
    have h1 := h_eq (f i) (f j)
    rw [sum_avoid_two h] at h1
    dsimp [L_mat, M_mat]
    simp_all only[avoid_one,g,f, Fin.ext_iff]
    grind
  have h_diag : (fun i j => ∑ k, L_mat i k * M_mat k j) = Matrix.diagonal (fun i => z (f i)) := by
    ext i j
    rw [h_mat_eq, Matrix.diagonal_apply]
  have h_det_2 : Matrix.det (Matrix.diagonal (fun i => z (f i))) = 0 := by
    rw [← h_diag]
    exact h_det
  have h_det_diag : Matrix.det (Matrix.diagonal (fun i => z (f i))) = ∏ i, z (f i) := Matrix.det_diagonal
  rw [h_det_diag] at h_det_2
  have h_prod : (∏ i, z (f i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact ha_nz (f i) (avoid_one_ne a i)
  exact h_prod h_det_2

lemma exists_z_perp_N {N : Nat} (h : N ≥ 4) (C : Fin N → ℂ) :
  ∃ z : Fin N → ℂ, (∑ k, C k * z k) = 0 ∧
  ∃ a : Fin N, ∀ b, b ≠ a → z b ≠ 0 := by
  by_cases hC : ∀ k, C k = 0
  · use fun _ => 1
    match N with |n + 1 =>norm_num [*]
  · push_neg at hC
    rcases hC with ⟨a, ha⟩
    let z : Fin N → ℂ := fun k => if k = a then - (∑ b : Fin N, if b = a then (0:ℂ) else C b) / C a else 1
    use z
    use (by norm_num[z,ha, mul_div_cancel₀ _, Finset.sum_ite, Finset.filter_ne', Finset.filter_eq']),a,fun R M=> (if_neg M).trans_ne one_ne_zero

noncomputable def eval_sum_N {N : Nat} (h : N ≥ 4) (W : WeightsN N N ℂ) (z : Fin N → ℂ) (i j : Fin N) : ℂ :=
  ∑ ι : V N → Fin N, pmSumN N N W ι * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))

lemma allEqual_val {N : Nat} (h : N ≥ 4) (ι : V N → Fin N) (v : V N) :
  allEqual ι → ι v = ι (f0 h) := by
  delta allEqual f0 and V
  delta allEqualList vertices V at *
  obtain ⟨n, rfl⟩:=N.exists_eq_succ_of_ne_zero v.pos.ne'
  simp_all -contextual[Nat.succ_sub_one _,List.isChain_iff_getElem]
  use fun and=>v.induction rfl fun and' =>.trans (? _)
  obtain ⟨M, rfl⟩:=n.exists_eq_succ_of_ne_zero (by omega)
  linear_combination2(norm:=norm_num) (and and' (and'.2.trans_eq (.symm (M.rec rfl (by norm_num))))).symm
  · rcases and' with S | S | S
    · rfl
    · rfl
    norm_num[ Fin.succ]
    congr
    clear ι v and h
    induction M generalizing S with|zero=>omega|_=>cases S with aesop
  · cases and' using Fin.induction with|zero=>_|_=>_
    · rfl
    norm_num at*
    clear*-
    congr
    induction M with|zero=>cases (by valid:).2|_=>cases‹ Fin _› using Fin.induction with aesop

lemma N_rhs_eval_N {N : Nat} (h : N ≥ 4) (W : WeightsN N N ℂ) (hW : EqSystemN N N W) (z : Fin N → ℂ) (i j : Fin N) :
  eval_sum_N h W z i j = if i = j then z i else 0 := by
  unfold eval_sum_N
  have h_eq : ∀ ι : V N → Fin N, pmSumN N N W ι = if allEqual ι then (1:ℂ) else 0 := hW
  simp_rw [h_eq]
  have h_ite : ∀ ι : V N → Fin N, (if allEqual ι then (1:ℂ) else 0) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h)) =
    if allEqual ι ∧ ι (f0 h) = i ∧ ι (f1 h) = j then z i else 0 := by
    intro ι
    by_cases h1 : allEqual ι
    · have h02 : ι (f2 h) = ι (f0 h) := allEqual_val h ι (f2 h) h1
      have h01 : ι (f1 h) = ι (f0 h) := allEqual_val h ι (f1 h) h1
      simp [h1]
      by_cases h2 : ι (f0 h) = i
      · simp [h2]
        by_cases h3 : ι (f1 h) = j
        · simp [h3]
          rw [h02, h2]
        · simp [h3]
      · simp [h2]
    · simp [h1]
  simp_rw [h_ite]
  norm_num[allEqual,Finset.sum_ite,ite_and]at*
  delta allEqualList V vertices at *
  clear*-
  obtain ⟨l, rfl⟩:=N.exists_eq_succ_of_ne_zero i.pos.ne'
  norm_num at*
  norm_num[List.isChain_cons,List.isChain_map]at*
  split
  · rw[Finset.card_eq_one.2 ⟨fun n=>i,Finset.ext fun and=>?_⟩,Nat.cast_one, one_mul]
    norm_num[*,funext_iff, Fin.forall_iff_succ]
    obtain ⟨l, rfl⟩:=l.exists_eq_succ_of_ne_zero (by ·omega)
    norm_num[List.isChain_iff_getElem,and_assoc]
    show _∧_∧and ⟨0, _⟩ = _∧and ⟨1, _⟩ = _ ↔_
    use fun⟨x,e,A, B⟩=>⟨A,fun ⟨a, _⟩=>?_⟩,fun ⟨a, e⟩=>⟨e 0▸a,fun R M=>?_, a, e 0⟩
    · induction a with|zero=>congr|_=>_
      linear_combination2(norm:=norm_num[*, (by valid:).trans', Fin.succ]) (e (by valid) (by use (by valid:).le_pred.trans (l.rec le_rfl (by norm_num)))).symm
      · cases‹ℕ› with|zero=>valid|_=>_
        norm_num[←‹∀y,_› (by valid), Fin.succ]
        congr
        clear*-
        induction l generalizing‹ℕ› with|zero=>omega|_=>cases‹ℕ› with aesop
      · congr
        clear‹i =j› A B‹∀_, _›x‹And _ _›e and‹ Fin _›h
        induction l generalizing‹ℕ› with|zero=>trivial|_=>cases‹ℕ› with aesop
    · simp_rw [e]
  · rw[ Finset.filter_false_of_mem]
    · norm_num
    norm_num
    match l with | S+1=>use fun and A B R L=>‹¬_› (R▸A 0 rfl▸L)

lemma pmSumN_expand {N : Nat} (h : N ≥ 4) (W : WeightsN N N ℂ) (ι : V N → Fin N) :
  pmSumN N N W ι = ∑ u : Fin N, if u = f0 h then (0:ℂ) else
    W (mkEdge (f0 h) u (ι (f0 h)) (ι u)) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase u) := by
  delta pmSumN f0 V vertices at*
  obtain ⟨x, rfl⟩:=Nat.exists_eq_add_of_le' (by valid: N≥2)
  simp_all!-contextual[x.add_sub_cancel, Fin.sum_univ_succ]
  simp_all-contextual[. ==.,pmSumList]
  rw[pmSumListAux]
  · norm_num[Function.comp_def, Fin.succ]
    congr
    · exact (x.rec rfl (by(norm_num)))
    · exact (funext fun and=>congr_arg _ ((congr_arg₂ _) (x.rec rfl (by simp_all)) (rfl)))
    · exact (x.rec rfl ↑(by simp_all [List.finRange_succ]))
  · nofun

noncomputable def C_vec {N : Nat} (h : N ≥ 4) (W : WeightsN N N ℂ) (k : Fin N) : ℂ :=
  ∑ ι : V N → Fin N, pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase (f1 h)) * (if ι (f2 h) = k then (1:ℂ) else 0) * (if ι (f1 h) = f0 h then (1:ℂ) else 0) * (if ι (f0 h) = f0 h then (1:ℂ) else 0)

noncomputable def C_N {N : Nat} (h : N ≥ 4) (W : WeightsN N N ℂ) (z : Fin N → ℂ) : ℂ :=
  ∑ ι : V N → Fin N, pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase (f1 h)) * z (ι (f2 h)) * (if ι (f1 h) = f0 h then (1:ℂ) else 0) * (if ι (f0 h) = f0 h then (1:ℂ) else 0)

lemma C_N_linear {N : Nat} (h : N ≥ 4) (W : WeightsN N N ℂ) (z : Fin N → ℂ) :
  C_N h W z = ∑ k : Fin N, C_vec h W k * z k := by
  simp_rw [C_vec, C_N,mul_comm]
  exact (congr_arg _ (by norm_num[mul_left_comm])).trans ( Finset.sum_comm.trans ( Fintype.sum_congr _ _ fun and=>Finset.mul_sum _ _ _).symm)

noncomputable def L_u {N : Nat} (h : N ≥ 4) (W : WeightsN N N ℂ) (z : Fin N → ℂ) (u : V N) (i : Fin N) : ℂ :=
  if u = f2 h then ∑ c : Fin N, W (mkEdge (f0 h) u i c) * z c
  else ∑ c : Fin N, W (mkEdge (f0 h) u i c)

noncomputable def M_u {N : Nat} (h : N ≥ 4) (W : WeightsN N N ℂ) (z : Fin N → ℂ) (u : V N) (j : Fin N) : ℂ :=
  ∑ ι : V N → Fin N, pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase u) *
    (if ι (f1 h) = j then (1:ℂ) else 0) * (if u = f2 h then (1:ℂ) else z (ι (f2 h))) * (if ι u = f0 h then (1:ℂ) else 0) * (if ι (f0 h) = f0 h then (1:ℂ) else 0)

def swap_val {N : Nat} (x a b : Fin N) : Fin N := if x = a then b else if x = b then a else x

lemma swap_val_inv {N : Nat} (x a b : Fin N) : swap_val (swap_val x a b) a b = x := by
  dsimp [swap_val]
  split_ifs <;> aesop

noncomputable def equiv_u1 {N : Nat} (h : N ≥ 4) (i j : Fin N) : (V N → Fin N) ≃ (V N → Fin N) where
  toFun ι x := if x = f0 h then swap_val (ι x) i (f0 h) else if x = f1 h then swap_val (ι x) j (f0 h) else ι x
  invFun ι x := if x = f0 h then swap_val (ι x) i (f0 h) else if x = f1 h then swap_val (ι x) j (f0 h) else ι x
  left_inv ι := by
    ext x
    dsimp
    by_cases h0 : x = f0 h
    · rw [if_pos h0, if_pos h0]
      have h_swap : swap_val (swap_val (ι x) i (f0 h)) i (f0 h) = ι x := swap_val_inv (ι x) i (f0 h)
      exact congrArg Fin.val h_swap
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : x = f1 h
      · rw [if_pos h1, if_pos h1]
        have h_swap : swap_val (swap_val (ι x) j (f0 h)) j (f0 h) = ι x := swap_val_inv (ι x) j (f0 h)
        exact congrArg Fin.val h_swap
      · rw [if_neg h1, if_neg h1]
  right_inv ι := by
    ext x
    dsimp
    by_cases h0 : x = f0 h
    · rw [if_pos h0, if_pos h0]
      have h_swap : swap_val (swap_val (ι x) i (f0 h)) i (f0 h) = ι x := swap_val_inv (ι x) i (f0 h)
      exact congrArg Fin.val h_swap
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : x = f1 h
      · rw [if_pos h1, if_pos h1]
        have h_swap : swap_val (swap_val (ι x) j (f0 h)) j (f0 h) = ι x := swap_val_inv (ι x) j (f0 h)
        exact congrArg Fin.val h_swap
      · rw [if_neg h1, if_neg h1]

lemma sum_equiv_u1 {N : Nat} (h : N ≥ 4) (i j : Fin N) (F : (V N → Fin N) → ℂ) :
  ∑ ι : V N → Fin N, F ι = ∑ ι : V N → Fin N, F (equiv_u1 h i j ι) := by
  exact (Equiv.sum_comp (equiv_u1 h i j) F).symm

noncomputable def equiv_u2 {N : Nat} (h : N ≥ 4) (u i c : Fin N) : (V N → Fin N) ≃ (V N → Fin N) where
  toFun ι x := if x = f0 h then swap_val (ι x) i (f0 h) else if x = u then swap_val (ι x) c (f0 h) else ι x
  invFun ι x := if x = f0 h then swap_val (ι x) i (f0 h) else if x = u then swap_val (ι x) c (f0 h) else ι x
  left_inv ι := by
    ext x
    dsimp
    by_cases h0 : x = f0 h
    · rw [if_pos h0, if_pos h0]
      have h_swap : swap_val (swap_val (ι x) i (f0 h)) i (f0 h) = ι x := swap_val_inv (ι x) i (f0 h)
      exact congrArg Fin.val h_swap
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : x = u
      · rw [if_pos h1, if_pos h1]
        have h_swap : swap_val (swap_val (ι x) c (f0 h)) c (f0 h) = ι x := swap_val_inv (ι x) c (f0 h)
        exact congrArg Fin.val h_swap
      · rw [if_neg h1, if_neg h1]
  right_inv ι := by
    ext x
    dsimp
    by_cases h0 : x = f0 h
    · rw [if_pos h0, if_pos h0]
      have h_swap : swap_val (swap_val (ι x) i (f0 h)) i (f0 h) = ι x := swap_val_inv (ι x) i (f0 h)
      exact congrArg Fin.val h_swap
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : x = u
      · rw [if_pos h1, if_pos h1]
        have h_swap : swap_val (swap_val (ι x) c (f0 h)) c (f0 h) = ι x := swap_val_inv (ι x) c (f0 h)
        exact congrArg Fin.val h_swap
      · rw [if_neg h1, if_neg h1]

lemma sum_equiv_u2 {N : Nat} (h : N ≥ 4) (u i c : Fin N) (F : (V N → Fin N) → ℂ) :
  ∑ ι : V N → Fin N, F ι = ∑ ι : V N → Fin N, F (equiv_u2 h u i c ι) := by
  exact (Equiv.sum_comp (equiv_u2 h u i c) F).symm

lemma pmSumListAux_indep {N : Nat} (W : WeightsN N N ℂ) (ι κ : V N → Fin N) (n : Nat) (L : List (V N))
  (h_eq : ∀ v ∈ L, ι v = κ v) :
  pmSumListAux W ι n L = pmSumListAux W κ n L := by
  induction n using Nat.strong_induction_on generalizing L with
  | h n ih =>
    cases n with
    | zero => rfl
    | succ n1 =>
      cases n1 with
      | zero => rfl
      | succ n2 =>
        cases L with
        | nil => rfl
        | cons v vs =>
          cases vs with
          | nil => rfl
          | cons v2 vs2 =>
            have h1 : pmSumListAux W ι (n2+2) (v::v2::vs2) = (List.map (fun u => W (mkEdge v u (ι v) (ι u)) * pmSumListAux W ι n2 ((v2::vs2).erase u)) (v2::vs2)).sum := rfl
            have h2 : pmSumListAux W κ (n2+2) (v::v2::vs2) = (List.map (fun u => W (mkEdge v u (κ v) (κ u)) * pmSumListAux W κ n2 ((v2::vs2).erase u)) (v2::vs2)).sum := rfl
            rw [h1, h2]
            apply congrArg List.sum
            apply List.map_congr_left
            intro u hu
            have h_v : ι v = κ v := h_eq v (List.Mem.head _)
            have h_u : ι u = κ u := h_eq u (List.Mem.tail _ hu)
            rw [h_v, h_u]
            apply congrArg
            apply ih n2 (by omega)
            intro w hw
            apply h_eq w
            apply List.mem_cons_of_mem
            exact List.mem_of_mem_erase hw

lemma nodup_vertices (N : Nat) : List.Nodup (vertices N) := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
    unfold vertices
    apply List.nodup_cons.mpr
    constructor
    · intro hc
      rw [List.mem_map] at hc
      rcases hc with ⟨a, _, eq⟩
      have : a.val + 1 = 0 := by
        have h1 : (Fin.succ a).val = a.val + 1 := rfl
        rw [← h1, eq]
        rfl
      omega
    · apply List.Nodup.map _ ih
      intro a b eq
      injection eq with eq2
      apply Fin.eq_of_val_eq
      omega

lemma erase_ne {α : Type} [DecidableEq α] {L : List α} {a b : α} (h : a ∈ L.erase b) :
  List.Nodup L → a ≠ b := by
  intro hn
  intro hab
  rw [hab] at h
  have : b ∉ L.erase b := List.Nodup.not_mem_erase hn
  exact this h

lemma N_lhs_u1 {N : Nat} (h : N ≥ 4) (W : WeightsN N N ℂ) (z : Fin N → ℂ) (i j : Fin N) :
  (∑ ι : V N → Fin N, W (mkEdge (f0 h) (f1 h) (ι (f0 h)) (ι (f1 h))) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase (f1 h)) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))) =
  W (mkEdge (f0 h) (f1 h) i j) * C_N h W z := by
  let F ι := W (mkEdge (f0 h) (f1 h) (ι (f0 h)) (ι (f1 h))) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase (f1 h)) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))
  have h_sum : (∑ ι : V N → Fin N, F ι) = ∑ ι : V N → Fin N, F (equiv_u1 h i j ι) := sum_equiv_u1 h i j F
  have h_eq : ∀ ι, F (equiv_u1 h i j ι) = W (mkEdge (f0 h) (f1 h) i j) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase (f1 h)) * z (ι (f2 h)) * (if ι (f1 h) = f0 h then (1:ℂ) else 0) * (if ι (f0 h) = f0 h then (1:ℂ) else 0) := by
    intro ι
    dsimp [F]
    have h_eval_f0 : equiv_u1 h i j ι (f0 h) = swap_val (ι (f0 h)) i (f0 h) := by rfl
    have h_eval_f1 : equiv_u1 h i j ι (f1 h) = swap_val (ι (f1 h)) j (f0 h) := by
      dsimp [equiv_u1]
      have h_ne : f1 h ≠ f0 h := by
        intro h_eq
        injection h_eq with h_eq_val
        omega
      rw [if_neg h_ne]
    have h_eval_f2 : equiv_u1 h i j ι (f2 h) = ι (f2 h) := by
      dsimp [equiv_u1]
      have h_ne0 : f2 h ≠ f0 h := by
        intro h_eq
        injection h_eq with h_eq_val
        omega
      have h_ne1 : f2 h ≠ f1 h := by
        intro h_eq
        injection h_eq with h_eq_val
        omega
      rw [if_neg h_ne0, if_neg h_ne1]
    rw [h_eval_f0, h_eval_f1, h_eval_f2]
    have h_pm : pmSumListAux W (equiv_u1 h i j ι) (N - 2) ((vertices N).erase (f0 h) |>.erase (f1 h)) = pmSumListAux W ι (N - 2) ((vertices N).erase (f0 h) |>.erase (f1 h)) := by
      apply pmSumListAux_indep
      intro v hv
      have h_v1 : v ≠ f1 h := by
        apply erase_ne hv
        apply List.Nodup.erase
        exact nodup_vertices N
      have h_v0 : v ≠ f0 h := by
        have h_in : v ∈ (vertices N).erase (f0 h) := List.mem_of_mem_erase hv
        apply erase_ne h_in
        exact nodup_vertices N
      dsimp [equiv_u1]
      rw [if_neg h_v0, if_neg h_v1]
    rw [h_pm]
    by_cases h0 : ι (f0 h) = f0 h
    · by_cases h1 : ι (f1 h) = f0 h
      · have h_swap0 : swap_val (ι (f0 h)) i (f0 h) = i := by
          dsimp [swap_val]
          rw [h0]
          by_cases hi : f0 h = i
          · rw [if_pos hi]; exact hi
          · rw [if_neg hi, if_pos rfl]
        have h_swap1 : swap_val (ι (f1 h)) j (f0 h) = j := by
          dsimp [swap_val]
          rw [h1]
          by_cases hj : f0 h = j
          · rw [if_pos hj]; exact hj
          · rw [if_neg hj, if_pos rfl]
        rw [h_swap0, h_swap1, if_pos rfl, if_pos rfl, if_pos h0, if_pos h1]
        ring
      · have h_swap1 : swap_val (ι (f1 h)) j (f0 h) ≠ j := by
          intro hc
          dsimp [swap_val] at hc
          by_cases hc2 : ι (f1 h) = j
          · rw [if_pos hc2] at hc
            have h_f0_j : f0 h = j := hc
            exact h1 (hc2.trans h_f0_j.symm)
          · rw [if_neg hc2] at hc
            by_cases hc3 : ι (f1 h) = f0 h
            · exact h1 hc3
            · rw [if_neg hc3] at hc; exact hc2 hc
        rw [if_neg h_swap1, if_neg h1]
        simp
    · have h_swap0 : swap_val (ι (f0 h)) i (f0 h) ≠ i := by
        intro hc
        dsimp [swap_val] at hc
        by_cases hc2 : ι (f0 h) = i
        · rw [if_pos hc2] at hc
          have h_f0_i : f0 h = i := hc
          exact h0 (hc2.trans h_f0_i.symm)
        · rw [if_neg hc2] at hc
          by_cases hc3 : ι (f0 h) = f0 h
          · exact h0 hc3
          · rw [if_neg hc3] at hc; exact hc2 hc
      rw [if_neg h_swap0, if_neg h0]
      simp
  rw [h_sum]
  unfold C_N
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ι _
  rw [h_eq ι]
  ring

lemma N_lhs_u_other {N : Nat} (h : N ≥ 4) (W : WeightsN N N ℂ) (z : Fin N → ℂ) (i j : Fin N) (u : Fin N) (hu0 : u ≠ f0 h) (hu1 : u ≠ f1 h) :
  (∑ ι : V N → Fin N, W (mkEdge (f0 h) u (ι (f0 h)) (ι u)) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase u) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))) =
  L_u h W z u i * M_u h W z u j := by
  let F ι := W (mkEdge (f0 h) u (ι (f0 h)) (ι u)) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase u) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))
  have h_F : (∑ ι : V N → Fin N, F ι) = ∑ c : Fin N, ∑ ι : V N → Fin N, F ι * (if ι u = c then (1:ℂ) else 0) := by
    have h1 : (∑ ι : V N → Fin N, F ι) = ∑ ι : V N → Fin N, ∑ c : Fin N, F ι * (if ι u = c then (1:ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro ι _
      have hz : (∑ c : Fin N, (if ι u = c then (1:ℂ) else 0)) = 1 := by
        exact Finset.sum_ite_eq (Finset.univ) (ι u) (fun _ => (1:ℂ)) |>.trans (by simp)
      calc F ι = F ι * 1 := by ring
      _ = F ι * ∑ c : Fin N, (if ι u = c then (1:ℂ) else 0) := by rw [hz]
      _ = ∑ c : Fin N, F ι * (if ι u = c then (1:ℂ) else 0) := by rw [Finset.mul_sum]
    rw [h1]
    exact Finset.sum_comm
  have h_inner : ∀ c, (∑ ι : V N → Fin N, F ι * (if ι u = c then (1:ℂ) else 0)) = ∑ ι : V N → Fin N, W (mkEdge (f0 h) u i c) * pmSumListAux W ι (N - 2) (((vertices N).erase (f0 h)).erase u) * (if ι (f1 h) = j then (1:ℂ) else 0) * (if u = f2 h then z c else z (ι (f2 h))) * (if ι u = f0 h then (1:ℂ) else 0) * (if ι (f0 h) = f0 h then (1:ℂ) else 0) := by
    intro c
    let G ι := F ι * (if ι u = c then (1:ℂ) else 0)
    have hG : (∑ ι : V N → Fin N, G ι) = ∑ ι : V N → Fin N, G (equiv_u2 h u i c ι) := sum_equiv_u2 h u i c G
    rw [hG]
    apply Finset.sum_congr rfl
    intro ι _
    dsimp [G, F]
    have h_eval_f0 : equiv_u2 h u i c ι (f0 h) = swap_val (ι (f0 h)) i (f0 h) := by rfl
    have h_eval_u : equiv_u2 h u i c ι u = swap_val (ι u) c (f0 h) := by
      dsimp [equiv_u2]
      rw [if_neg hu0, if_pos rfl]
    have h_eval_f1 : equiv_u2 h u i c ι (f1 h) = ι (f1 h) := by
      dsimp [equiv_u2]
      have h_ne_u : f1 h ≠ u := hu1.symm
      have h_ne_0 : f1 h ≠ f0 h := by
        intro h_eq
        injection h_eq with h_eq_val
        omega
      rw [if_neg h_ne_0, if_neg h_ne_u]
    have h_eval_f2 : equiv_u2 h u i c ι (f2 h) = if f2 h = u then swap_val (ι u) c (f0 h) else ι (f2 h) := by
      dsimp [equiv_u2]
      have h_ne_0 : f2 h ≠ f0 h := by
        intro h_eq
        injection h_eq with h_eq_val
        omega
      rw [if_neg h_ne_0]
      by_cases hu2 : f2 h = u
      · simp [hu2]
      · simp [hu2]
    rw [h_eval_f0, h_eval_u, h_eval_f1, h_eval_f2]
    have h_pm : pmSumListAux W (equiv_u2 h u i c ι) (N - 2) ((vertices N).erase (f0 h) |>.erase u) = pmSumListAux W ι (N - 2) ((vertices N).erase (f0 h) |>.erase u) := by
      apply pmSumListAux_indep
      intro v hv
      have h_v_u : v ≠ u := by
        apply erase_ne hv
        apply List.Nodup.erase
        exact nodup_vertices N
      have h_v_0 : v ≠ f0 h := by
        have h_in : v ∈ (vertices N).erase (f0 h) := List.mem_of_mem_erase hv
        apply erase_ne h_in
        exact nodup_vertices N
      dsimp [equiv_u2]
      rw [if_neg h_v_0, if_neg h_v_u]
    rw [h_pm]
    by_cases h0 : ι (f0 h) = f0 h
    · by_cases hu_f0 : ι u = f0 h
      · have h_swap0 : swap_val (ι (f0 h)) i (f0 h) = i := by
          dsimp [swap_val]; rw [h0]
          by_cases hi : f0 h = i
          · rw [if_pos hi]; exact hi
          · rw [if_neg hi, if_pos rfl]
        have h_swapu : swap_val (ι u) c (f0 h) = c := by
          dsimp [swap_val]; rw [hu_f0]
          by_cases hc : f0 h = c
          · rw [if_pos hc]; exact hc
          · rw [if_neg hc, if_pos rfl]
        rw [h_swap0, h_swapu, if_pos rfl, if_pos rfl, if_pos h0, if_pos hu_f0]
        by_cases hu2 : f2 h = u
        · have hu2' : u = f2 h := hu2.symm
          rw [if_pos hu2, if_pos hu2']
          ring
        · have hu2' : u ≠ f2 h := fun hc => hu2 hc.symm
          rw [if_neg hu2, if_neg hu2']
          ring
      · have h_swapu : swap_val (ι u) c (f0 h) ≠ c := by
          intro hc
          dsimp [swap_val] at hc
          by_cases hc2 : ι u = c
          · rw [if_pos hc2] at hc
            have h_f0_c : f0 h = c := hc
            exact hu_f0 (hc2.trans h_f0_c.symm)
          · rw [if_neg hc2] at hc
            by_cases hc3 : ι u = f0 h
            · exact hu_f0 hc3
            · rw [if_neg hc3] at hc; exact hc2 hc
        rw [if_neg h_swapu, if_neg hu_f0]
        simp
    · have h_swap0 : swap_val (ι (f0 h)) i (f0 h) ≠ i := by
        intro hc
        dsimp [swap_val] at hc
        by_cases hc2 : ι (f0 h) = i
        · rw [if_pos hc2] at hc
          have h_f0_i : f0 h = i := hc
          exact h0 (hc2.trans h_f0_i.symm)
        · rw [if_neg hc2] at hc
          by_cases hc3 : ι (f0 h) = f0 h
          · exact h0 hc3
          · rw [if_neg hc3] at hc; exact hc2 hc
      rw [if_neg h_swap0, if_neg h0]
      simp
  rw [h_F]
  have h_L : L_u h W z u i = ∑ c : Fin N, W (mkEdge (f0 h) u i c) * (if u = f2 h then z c else (1:ℂ)) := by
    unfold L_u; by_cases hu2 : u = f2 h
    · rw [if_pos hu2]; apply Finset.sum_congr rfl; intro c _; rw [if_pos hu2]
    · rw [if_neg hu2]; apply Finset.sum_congr rfl; intro c _; rw [if_neg hu2, mul_one]
  rw [h_L]
  unfold M_u
  rw [Finset.sum_mul]
  have h_swap : (∑ c : Fin N, W (mkEdge (f0 h) u i c) * (if u = f2 h then z c else (1:ℂ)) * ∑ ι : V N → Fin N, pmSumListAux W ι (N - 2) (((vertices N).erase (f0 h)).erase u) * (if ι (f1 h) = j then (1:ℂ) else 0) * (if u = f2 h then (1:ℂ) else z (ι (f2 h))) * (if ι u = f0 h then (1:ℂ) else 0) * (if ι (f0 h) = f0 h then (1:ℂ) else 0)) =
    ∑ c : Fin N, ∑ ι : V N → Fin N, W (mkEdge (f0 h) u i c) * pmSumListAux W ι (N - 2) (((vertices N).erase (f0 h)).erase u) * (if ι (f1 h) = j then (1:ℂ) else 0) * (if u = f2 h then z c else z (ι (f2 h))) * (if ι u = f0 h then (1:ℂ) else 0) * (if ι (f0 h) = f0 h then (1:ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ι _
    by_cases hu2 : u = f2 h
    · simp [hu2]; ring
    · simp [hu2]; ring
  rw [h_swap]
  apply Finset.sum_congr rfl
  intro c _
  rw [h_inner c]

lemma sum_pull_two {N : Nat} (h : N ≥ 4) (F : Fin N → ℂ) :
  (∑ u : Fin N, F u) = F (f0 h) + F (f1 h) + ∑ u : Fin N, if u = f0 h ∨ u = f1 h then (0:ℂ) else F u := by
  have h_f1 : f1 h ≠ f0 h := by rintro@c
  have h1 : (∑ u : Fin N, F u) = ∑ u : Fin N, ((if u = f0 h then F u else 0) + (if u = f1 h then F u else 0) + (if u = f0 h ∨ u = f1 h then 0 else F u)) := by
    apply Finset.sum_congr rfl
    intro u _
    by_cases h0 : u = f0 h
    · rw [if_pos h0, if_neg (by rw [h0]; exact h_f1.symm), if_pos (Or.inl h0)]
      ring
    · rw [if_neg h0]
      by_cases h1_eq : u = f1 h
      · rw [if_pos h1_eq, if_pos (Or.inr h1_eq)]
        ring
      · rw [if_neg h1_eq, if_neg (fun hc => hc.elim h0 h1_eq)]
        ring
  rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hz0 : (∑ u : Fin N, if u = f0 h then F u else (0:ℂ)) = F (f0 h) := by
    have h_eq : (fun u => if u = f0 h then F u else (0:ℂ)) = (fun u => if f0 h = u then F u else (0:ℂ)) := by
      ext u
      by_cases h_u : u = f0 h
      · rw [if_pos h_u, if_pos h_u.symm]
      · rw [if_neg h_u, if_neg (Ne.symm h_u)]
    rw [h_eq]
    exact Finset.sum_ite_eq (Finset.univ) (f0 h) (fun u => F u) |>.trans (by simp)
  have hz1 : (∑ u : Fin N, if u = f1 h then F u else (0:ℂ)) = F (f1 h) := by
    have h_eq : (fun u => if u = f1 h then F u else (0:ℂ)) = (fun u => if f1 h = u then F u else (0:ℂ)) := by
      ext u
      by_cases h_u : u = f1 h
      · rw [if_pos h_u, if_pos h_u.symm]
      · rw [if_neg h_u, if_neg (Ne.symm h_u)]
    rw [h_eq]
    exact Finset.sum_ite_eq (Finset.univ) (f1 h) (fun u => F u) |>.trans (by simp)
  rw [hz0, hz1]

lemma N_lhs_factorize_N {N : Nat} (h : N ≥ 4) (W : WeightsN N N ℂ) (z : Fin N → ℂ) (i j : Fin N) :
  eval_sum_N h W z i j =
  W (mkEdge (f0 h) (f1 h) i j) * C_N h W z +
  ∑ u : Fin N, if u = f0 h ∨ u = f1 h then (0:ℂ) else L_u h W z u i * M_u h W z u j := by
  unfold eval_sum_N
  simp_rw [pmSumN_expand h W]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h_split : (∑ u : Fin N, ∑ ι : V N → Fin N, (if u = f0 h then (0:ℂ) else W (mkEdge (f0 h) u (ι (f0 h)) (ι u)) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase u)) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))) =
    (∑ ι : V N → Fin N, W (mkEdge (f0 h) (f1 h) (ι (f0 h)) (ι (f1 h))) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase (f1 h)) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))) +
    ∑ u : Fin N, if u = f0 h ∨ u = f1 h then (0:ℂ) else (∑ ι : V N → Fin N, W (mkEdge (f0 h) u (ι (f0 h)) (ι u)) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase u) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))) := by
    have h_sum : (∑ u : Fin N, ∑ ι : V N → Fin N, (if u = f0 h then (0:ℂ) else W (mkEdge (f0 h) u (ι (f0 h)) (ι u)) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase u)) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))) =
      (∑ ι : V N → Fin N, (if f0 h = f0 h then (0:ℂ) else W (mkEdge (f0 h) (f0 h) (ι (f0 h)) (ι (f0 h))) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase (f0 h))) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))) +
      (∑ ι : V N → Fin N, (if f1 h = f0 h then (0:ℂ) else W (mkEdge (f0 h) (f1 h) (ι (f0 h)) (ι (f1 h))) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase (f1 h))) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))) +
      ∑ u : Fin N, if u = f0 h ∨ u = f1 h then (0:ℂ) else (∑ ι : V N → Fin N, (if u = f0 h then (0:ℂ) else W (mkEdge (f0 h) u (ι (f0 h)) (ι u)) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase u)) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))) := by
      exact sum_pull_two h (fun u => ∑ ι : V N → Fin N, (if u = f0 h then (0:ℂ) else W (mkEdge (f0 h) u (ι (f0 h)) (ι u)) * pmSumListAux W ι (N-2) ((vertices N).erase (f0 h) |>.erase u)) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h)))
    rw [h_sum]
    have h_f1 : f1 h ≠ f0 h := by nofun
    have h_eq : (∑ u : Fin N, if u = f0 h ∨ u = f1 h then (0:ℂ) else ∑ ι : V N → Fin N, (if u = f0 h then (0:ℂ) else W (mkEdge (f0 h) u (ι (f0 h)) (ι u)) * pmSumListAux W ι (N - 2) ((vertices N).erase (f0 h) |>.erase u)) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h))) =
      ∑ u : Fin N, if u = f0 h ∨ u = f1 h then (0:ℂ) else ∑ ι : V N → Fin N, W (mkEdge (f0 h) u (ι (f0 h)) (ι u)) * pmSumListAux W ι (N - 2) ((vertices N).erase (f0 h) |>.erase u) * (if ι (f0 h) = i then (1:ℂ) else 0) * (if ι (f1 h) = j then (1:ℂ) else 0) * z (ι (f2 h)) := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases h_u : u = f0 h ∨ u = f1 h
      · rw [if_pos h_u, if_pos h_u]
      · rw [if_neg h_u, if_neg h_u]
        have h_u_ne_f0 : u ≠ f0 h := by push_neg at h_u; exact h_u.1
        apply Finset.sum_congr rfl
        intro ι _
        rw [if_neg h_u_ne_f0]
    rw [h_eq]
    simp [h_f1]
  rw [h_split]
  rw [N_lhs_u1 h W z i j]
  apply congrArg
  apply Finset.sum_congr rfl
  intro u _
  by_cases h_u : u = f0 h ∨ u = f1 h
  · rw [if_pos h_u, if_pos h_u]
  · rw [if_neg h_u, if_neg h_u]
    push_neg at h_u
    exact N_lhs_u_other h W z i j u h_u.1 h_u.2

lemma impossible_haf (N : Nat) (h1 : N ≥ 4) (h2 : Even N) (W : WeightsN N N ℂ) : ¬ EqSystemN N N W := by
  intro hW
  have hz := exists_z_perp_N h1 (C_vec h1 W)
  rcases hz with ⟨z, hz_perp, hz_zero⟩
  have h_CN : C_N h1 W z = 0 := by
    rw [C_N_linear h1 W z]
    exact hz_perp
  have h_eq : ∀ i j, (∑ u : Fin N, if u = f0 h1 ∨ u = f1 h1 then (0:ℂ) else L_u h1 W z u i * M_u h1 W z u j) = if i = j then z i else 0 := by
    intro i j
    have h_lhs := N_lhs_factorize_N h1 W z i j
    rw [h_CN, mul_zero, zero_add] at h_lhs
    have h_rhs := N_rhs_eval_N h1 W hW z i j
    rw [← h_rhs, h_lhs]
  exact rank_N_contradiction (by omega) h1 (fun u i => L_u h1 W z u i) (fun u j => M_u h1 W z u j) z hz_zero h_eq


/-- For all even $N \geq 4$ and $D = N$, does there exist no solution to the monochromatic quantum
graph equation system over $\mathbb{C}$?

The DeepMind prover agent has found a formal proof for this statement.
-/
@[category research solved, AMS 5 14 81]
theorem eqSystem_no_solution_even_ge4_d_eq_n_explicit :
    answer(True) ↔
      ∀ N : Nat, N ≥ 4 → Even N →
        ¬ ∃ W : WeightsN N N ℂ, EqSystemN N N W := by
  constructor
  · intro _ N hN hEven hEx
    rcases hEx with ⟨W, hW⟩
    exact impossible_haf N hN hEven W hW
  · intro _
    trivial

/-- For all even $N \geq 6$ and $D \geq 3$, does there exist no solution to the monochromatic
quantum graph equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem_no_solution_ge6_ge3 :
    answer(sorry) ↔
      ∀ N D : Nat, N ≥ 6 → Even N → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℂ, EqSystemN N D W := by
  sorry

/- ## Open conjectures over ℝ -/

/-- For $N = 4$ and $D = 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_d4_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 4 4 ℝ, EqSystemN 4 4 W := by
  sorry

/-- For $N = 4$ and all $D \geq 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_ge4_real :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 4 →
        ¬ ∃ W : WeightsN 4 D ℝ, EqSystemN 4 D W := by
  sorry

/-- For $N = 6$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d3_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 3 ℝ, EqSystemN 6 3 W := by
  sorry

/-- For $N = 6$ and $D = 5$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d5_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 5 ℝ, EqSystemN 6 5 W := by
  sorry

/-- For $N = 6$ and all $D \geq 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_ge3_real :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 3 →
        ¬ ∃ W : WeightsN 6 D ℝ, EqSystemN 6 D W := by
  sorry

/-- For $N = 8$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d3_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 3 ℝ, EqSystemN 8 3 W := by
  sorry

/-- For $N = 8$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d10_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 10 ℝ, EqSystemN 8 10 W := by
  sorry

/-- For $N = 10$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d3_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 3 ℝ, EqSystemN 10 3 W := by
  sorry

/-- For $N = 10$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d10_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 10 ℝ, EqSystemN 10 10 W := by
  sorry

/-- For all even $N \geq 6$ and $D \geq 3$, does there exist no solution to the monochromatic
quantum graph equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem_no_solution_ge6_ge3_real :
    answer(sorry) ↔
      ∀ N D : Nat, N ≥ 6 → Even N → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℝ, EqSystemN N D W := by
  sorry

/- ## Open conjectures over ℤ -/

/-- For $N = 4$ and $D = 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_d4_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 4 4 ℤ, EqSystemN 4 4 W := by
  sorry

/-- For $N = 4$ and all $D \geq 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_ge4_int :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 4 →
        ¬ ∃ W : WeightsN 4 D ℤ, EqSystemN 4 D W := by
  sorry

/-- For $N = 6$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d3_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 3 ℤ, EqSystemN 6 3 W := by
  sorry

/-- For $N = 6$ and $D = 5$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d5_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 5 ℤ, EqSystemN 6 5 W := by
  sorry

/-- For $N = 6$ and all $D \geq 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_ge3_int :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 3 →
        ¬ ∃ W : WeightsN 6 D ℤ, EqSystemN 6 D W := by
  sorry

/-- For $N = 8$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d3_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 3 ℤ, EqSystemN 8 3 W := by
  sorry

/-- For $N = 8$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d10_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 10 ℤ, EqSystemN 8 10 W := by
  sorry

/-- For $N = 10$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d3_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 3 ℤ, EqSystemN 10 3 W := by
  sorry

/-- For $N = 10$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d10_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 10 ℤ, EqSystemN 10 10 W := by
  sorry

/-- For all even $N \geq 6$ and $D \geq 3$, does there exist no solution to the monochromatic
quantum graph equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem_no_solution_ge6_ge3_int :
    answer(sorry) ↔
      ∀ N D : Nat, N ≥ 6 → Even N → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℤ, EqSystemN N D W := by
  sorry

/- ## Open conjectures over {-1,0,1} ⊆ ℤ
   (implemented as ℤ-valued weights with a pointwise restriction) -/

/-- For $N = 4$ and $D = 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_d4_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 4 4 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 4 4 W := by
  sorry

/-- For $N = 4$ and all $D \geq 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_ge4_trinary_int :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 4 →
        ¬ ∃ W : WeightsN 4 D ℤ,
            (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
              EqSystemN 4 D W := by
  sorry

/-- For $N = 6$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d3_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 3 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 6 3 W := by
  sorry

/-- For $N = 6$ and $D = 5$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d5_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 5 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 6 5 W := by
  sorry

/-- For $N = 6$ and all $D \geq 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_ge3_trinary_int :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 3 →
        ¬ ∃ W : WeightsN 6 D ℤ,
            (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
              EqSystemN 6 D W := by
  sorry

/-- For $N = 8$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d3_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 3 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 8 3 W := by
  sorry

/-- For $N = 8$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d10_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 10 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 8 10 W := by
  sorry

/-- For $N = 10$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d3_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 3 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 10 3 W := by
  sorry

/-- For $N = 10$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d10_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 10 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 10 10 W := by
  sorry

/-- For all even $N \geq 6$ and $D \geq 3$, does there exist no solution to the monochromatic
quantum graph equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem_no_solution_ge6_ge3_trinary_int :
    answer(sorry) ↔
      ∀ N D : Nat, N ≥ 6 → Even N → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℤ,
            (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
              EqSystemN N D W := by
  sorry

end MonochromaticQuantumGraph
