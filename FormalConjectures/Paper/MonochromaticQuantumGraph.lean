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

These proofs are computation-heavy (`fin_cases` + `simp`), so we increase the heartbeat limit locally.
-/

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

set_option maxHeartbeats 5000000 in
@[category test, AMS 5 14 81]
theorem eqSystem4_has_solution_d2 :
    ∃ W : WeightsN 4 2 α, EqSystemN 4 2 W := by
  classical
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

  have hι : ι = ![ι 0, ι 1, ι 2, ι 3] := by
    funext k
    fin_cases k <;> simp

  rw [hι]
  exact h (ι 0) (ι 1) (ι 2) (ι 3)

end N4_D2

/- ## N = 4, D = 3 over ℂ: witness & proof -/

def Witness4_d3 : WeightsN 4 3 ℂ :=
  fun e =>
    if e = mkEdge 0 1 0 0 then (1 : ℂ) else
    if e = mkEdge 2 3 0 0 then (1 : ℂ) else
    if e = mkEdge 0 2 1 1 then (1 : ℂ) else
    if e = mkEdge 1 3 1 1 then (1 : ℂ) else
    if e = mkEdge 0 3 2 2 then (1 : ℂ) else
    if e = mkEdge 1 2 2 2 then (1 : ℂ) else
    (0 : ℂ)

set_option maxHeartbeats 5000000 in
@[category test, AMS 5 14 81]
theorem eqSystem4_has_solution_d3 :
    ∃ W : WeightsN 4 3 ℂ, EqSystemN 4 3 W := by
  classical
  refine ⟨Witness4_d3, ?_⟩
  intro ι

  have h :
      ∀ a b c d : Fin 3,
        pmSumN 4 3 (W := Witness4_d3) ![a, b, c, d] =
          (if allEqual ![a, b, c, d] then (1 : ℂ) else (0 : ℂ)) := by
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [pmSumN, pmSumList, pmSumListAux, vertices,
        allEqual, allEqualList, Witness4_d3, mkEdge]

  have hι : ι = ![ι 0, ι 1, ι 2, ι 3] := by
    funext k
    fin_cases k <;> simp

  rw [hι]
  exact h (ι 0) (ι 1) (ι 2) (ι 3)

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

set_option maxHeartbeats 5000000 in
@[category test, AMS 5 14 81]
theorem eqSystem6_has_solution_d2 :
    ∃ W : WeightsN 6 2 α, EqSystemN 6 2 W := by
  classical
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

  have hι : ι = ![ι 0, ι 1, ι 2, ι 3, ι 4, ι 5] := by
    funext k
    fin_cases k <;> simp

  rw [hι]
  exact h (ι 0) (ι 1) (ι 2) (ι 3) (ι 4) (ι 5)

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


lemma vertices_6 : vertices 6 = [0, 1, 2, 3, 4, 5] := rfl

def const_fun_6 {D : Nat} (c : Fin D) : V 6 → Fin D := fun _ => c

lemma const_fun_allEqual_6 {D : Nat} (c : Fin D) : allEqual (const_fun_6 c) := by
  unfold allEqual allEqualList
  rw [vertices_6]
  simp [const_fun_6]

lemma allEqual_implies_const_6 {D : Nat} (ι : V 6 → Fin D) (h : allEqual ι) :
  ι = const_fun_6 (ι 0) := by
  unfold allEqual allEqualList at h
  rw [vertices_6] at h
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at h
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  funext ⟨u, hu⟩
  change ι ⟨u, hu⟩ = ι 0
  match u with
  | 0 => rfl
  | 1 => exact h1.symm
  | 2 => exact (h1.trans h2).symm
  | 3 => exact (h1.trans (h2.trans h3)).symm
  | 4 => exact (h1.trans (h2.trans (h3.trans h4))).symm
  | 5 => exact (h1.trans (h2.trans (h3.trans (h4.trans h5)))).symm

lemma eq_sys_implies_rhs_6_matrix {D : Nat} (W : WeightsN 6 D ℂ) (h : EqSystemN 6 D W) (F : V 6 → Fin D → ℂ) :
  (∑ ι : V 6 → Fin D, (∏ u : Fin 6, F u (ι u)) * pmSumN 6 D W ι) = ∑ c : Fin D, ∏ u : Fin 6, F u c := by
  have h1 : ∑ ι : V 6 → Fin D, (∏ u : Fin 6, F u (ι u)) * pmSumN 6 D W ι =
            ∑ ι : V 6 → Fin D, (∏ u : Fin 6, F u (ι u)) * (if allEqual ι then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro ι _
    rw [h ι]
  rw [h1]
  have h2 : ∑ ι : V 6 → Fin D, (∏ u : Fin 6, F u (ι u)) * (if allEqual ι then (1 : ℂ) else 0) =
            ∑ ι : V 6 → Fin D, if allEqual ι then ∏ u : Fin 6, F u (ι u) else 0 := by
    apply Finset.sum_congr rfl
    intro ι _
    split
    · simp
    · simp
  rw [h2]
  have h3 : ∑ ι : V 6 → Fin D, (if allEqual ι then ∏ u : Fin 6, F u (ι u) else 0) =
            ∑ ι ∈ Finset.univ.filter (fun ι : V 6 → Fin D => allEqual ι), ∏ u : Fin 6, F u (ι u) := by
    exact Finset.sum_filter _ _ |>.symm
  rw [h3]
  have h4 : ∑ ι ∈ Finset.univ.filter (fun ι : V 6 → Fin D => allEqual ι), ∏ u : Fin 6, F u (ι u) =
            ∑ c ∈ Finset.univ, ∏ u : Fin 6, F u ((const_fun_6 c) u) := by
    refine Finset.sum_bij (fun ι _ => ι 0) ?_ ?_ ?_ ?_
    · intro ι hι
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hι ⊢
    · intro ι1 hι1 ι2 hι2 hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hι1 hι2
      have eq1 := allEqual_implies_const_6 ι1 hι1
      have eq2 := allEqual_implies_const_6 ι2 hι2
      rw [eq1, eq2]
      exact congrArg const_fun_6 hc
    · intro c _
      use const_fun_6 c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨const_fun_allEqual_6 c, rfl⟩
    · intro ι hι
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hι
      have eq := allEqual_implies_const_6 ι hι
      exact congrArg (fun g => ∏ u : Fin 6, F u (g u)) eq
  rw [h4]
  have h5 : ∑ c ∈ Finset.univ, ∏ u : Fin 6, F u ((const_fun_6 c) u) = ∑ c : Fin D, ∏ u : Fin 6, F u c := by
    apply Finset.sum_congr rfl
    intro c _
    rfl
  exact h5

lemma pmSumN_6_eval {D : Nat} (W : WeightsN 6 D ℂ) (ι : V 6 → Fin D) :
  pmSumN 6 D W ι = pmSumListAux W ι 6 [0, 1, 2, 3, 4, 5] := rfl

def W_mul_F {N D : Nat} (W : WeightsN N D ℂ) (F : V N → Fin D → ℂ) : WeightsN N D ℂ :=
  fun e => F e.u e.i * F e.v e.j * W e

lemma pmSumN_6_mul_F {D : Nat} (W : WeightsN 6 D ℂ) (F : V 6 → Fin D → ℂ) (ι : V 6 → Fin D) :
  (∏ u : Fin 6, F u (ι u)) * pmSumN 6 D W ι = pmSumN 6 D (W_mul_F W F) ι := by
  rw [pmSumN_6_eval, pmSumN_6_eval]
  dsimp [pmSumListAux, List.erase, List.map, List.sum, mkEdge, W_mul_F]
  have h_prod : ∏ u : Fin 6, F u (ι u) = F 0 (ι 0) * F 1 (ι 1) * F 2 (ι 2) * F 3 (ι 3) * F 4 (ι 4) * F 5 (ι 5) := by
    fapply Fin.prod_univ_six
  rw [h_prod]
  ring

lemma sum_ι_factor_6_specific {D : Nat} (F1 F2 F3 : Fin D → Fin D → ℂ) :
  (∑ ι : V 6 → Fin D, F1 (ι 0) (ι 1) * F2 (ι 2) (ι 3) * F3 (ι 4) (ι 5)) =
  (∑ i : Fin D, ∑ j : Fin D, F1 i j) *
  (∑ i : Fin D, ∑ j : Fin D, F2 i j) *
  (∑ i : Fin D, ∑ j : Fin D, F3 i j) := by
  push_cast[ Finset.sum_mul_sum, false,mul_assoc]
  push_cast [ Finset.sum_mul, ← Finset.sum_product',mul_assoc]
  exact Fintype.sum_equiv ⟨(. 0, _, _, _,_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_6_01_24_35 {D : Nat} (F1 F2 F3 : Fin D → Fin D → ℂ) :
  (∑ ι : V 6 → Fin D, F1 (ι 0) (ι 1) * F2 (ι 2) (ι 4) * F3 (ι 3) (ι 5)) =
  (∑ i : Fin D, ∑ j : Fin D, F1 i j) *
  (∑ i : Fin D, ∑ j : Fin D, F2 i j) *
  (∑ i : Fin D, ∑ j : Fin D, F3 i j) := by
  push_cast [← Finset.sum_product', Finset.sum_mul_sum, mul_assoc]
  exact Fintype.sum_equiv ⟨ fun and=>(((_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_0 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 3 (ι 2) (ι 3)) * W (mkEdge 4 5 (ι 4) (ι 5))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 1 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 4 5 i j)) := by push_cast[ Finset.sum_mul_sum, V,mul_assoc]
                                                                                                                                                         push_cast[ Finset.sum_mul, ← Finset.sum_product',mul_assoc]
                                                                                                                                                         refine Fintype.sum_equiv ⟨ (@. @0, _, _, _,_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_1 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 4 (ι 2) (ι 4)) * W (mkEdge 3 5 (ι 3) (ι 5))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 1 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 5 i j)) := by push_cast[mul_assoc, V, Finset.sum_mul_sum,← Finset.sum_product']
                                                                                                                                                         exact Fintype.sum_equiv ⟨ fun and=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_2 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 5 (ι 2) (ι 5)) * W (mkEdge 3 4 (ι 3) (ι 4))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 1 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 4 i j)) := by push_cast[mul_assoc, V, Finset.sum_mul_sum]
                                                                                                                                                         push_cast[ Finset.sum_mul,← Finset.sum_product',mul_assoc]
                                                                                                                                                         refine Fintype.sum_equiv ⟨ ((. (@0), _, _, _,_, _)), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_3 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 3 (ι 1) (ι 3)) * W (mkEdge 4 5 (ι 4) (ι 5))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 4 5 i j)) := by push_cast[← Finset.sum_product', Finset.sum_mul_sum,mul_assoc]
                                                                                                                                                         exact Fintype.sum_equiv ⟨ fun and=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective rfl, fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_4 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 4 (ι 1) (ι 4)) * W (mkEdge 3 5 (ι 3) (ι 5))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 5 i j)) := by push_cast[ Finset.sum_mul_sum, V, mul_assoc]
                                                                                                                                                         push_cast [ Finset.sum_mul,← Finset.sum_product',mul_assoc]
                                                                                                                                                         refine Fintype.sum_equiv ⟨ (@. (@0), _, _, _,_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_5 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 5 (ι 1) (ι 5)) * W (mkEdge 3 4 (ι 3) (ι 4))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 4 i j)) := by push_cast[ Finset.sum_mul_sum,← Finset.sum_product',mul_assoc]
                                                                                                                                                         exact Fintype.sum_equiv ⟨ fun and=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_6_lem {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 2 (ι 1) (ι 2)) * W (mkEdge 4 5 (ι 4) (ι 5))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 4 5 i j)) := by push_cast[← Finset.sum_product', Finset.sum_mul_sum,mul_assoc]
                                                                                                                                                         exact Fintype.sum_equiv ⟨ fun and=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_7 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 4 (ι 1) (ι 4)) * W (mkEdge 2 5 (ι 2) (ι 5))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 5 i j)) := by push_cast [← Finset.sum_product', Finset.sum_mul_sum, mul_assoc.{0}]
                                                                                                                                                         exact Fintype.sum_equiv ⟨ fun and=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective rfl, fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_8 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 5 (ι 1) (ι 5)) * W (mkEdge 2 4 (ι 2) (ι 4))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 4 i j)) := by push_cast[← Finset.sum_product', Finset.sum_mul_sum,mul_assoc]
                                                                                                                                                         exact Fintype.sum_equiv ⟨ fun and=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective rfl, fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_9 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 4 (ι 0) (ι 4)) * W (mkEdge 1 2 (ι 1) (ι 2)) * W (mkEdge 3 5 (ι 3) (ι 5))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 5 i j)) := by push_cast [← Finset.sum_product', Finset.sum_mul_sum, V, false,mul_assoc]
                                                                                                                                                         exact Fintype.sum_equiv ⟨ fun and=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_10 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 4 (ι 0) (ι 4)) * W (mkEdge 1 3 (ι 1) (ι 3)) * W (mkEdge 2 5 (ι 2) (ι 5))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 5 i j)) := by push_cast[mul_assoc, V, true, Finset.sum_mul_sum, false,← Finset.sum_product']
                                                                                                                                                         exact Fintype.sum_equiv ⟨fun P=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective rfl, fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_11 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 4 (ι 0) (ι 4)) * W (mkEdge 1 5 (ι 1) (ι 5)) * W (mkEdge 2 3 (ι 2) (ι 3))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 3 i j)) := by push_cast[ Finset.sum_mul_sum, V,mul_assoc,← Finset.sum_product']
                                                                                                                                                         exact Fintype.sum_equiv ⟨ fun and=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_12 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 5 (ι 0) (ι 5)) * W (mkEdge 1 2 (ι 1) (ι 2)) * W (mkEdge 3 4 (ι 3) (ι 4))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 4 i j)) := by push_cast[ Finset.sum_mul_sum,← Finset.sum_product',mul_assoc]
                                                                                                                                                         exact Fintype.sum_equiv ⟨ fun and=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_13 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 5 (ι 0) (ι 5)) * W (mkEdge 1 3 (ι 1) (ι 3)) * W (mkEdge 2 4 (ι 2) (ι 4))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 4 i j)) := by push_cast [ ← Finset.sum_product', Finset.sum_mul_sum,mul_assoc]
                                                                                                                                                         exact Fintype.sum_equiv ⟨ fun and=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective rfl, fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_factor_14 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, W (mkEdge 0 5 (ι 0) (ι 5)) * W (mkEdge 1 4 (ι 1) (ι 4)) * W (mkEdge 2 3 (ι 2) (ι 3))) =
  (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 3 i j)) := by push_cast[ ← Finset.sum_product', Finset.sum_mul_sum, V, mul_assoc]
                                                                                                                                                         refine Fintype.sum_equiv ⟨ fun and=>(( (_, _),_, _),_, _), fun and=>![ _, _, _, _,_, _], fun and=>List.ofFn_injective (by constructor), fun and=>rfl⟩ _ _ fun and=>rfl

lemma sum_ι_pmSumN_6 {D : Nat} (W : WeightsN 6 D ℂ) :
  (∑ ι : V 6 → Fin D, pmSumN 6 D W ι) = pmSumN 6 1 (fun e => ∑ i : Fin D, ∑ j : Fin D, W ⟨e.u, e.v, i, j⟩) (fun _ => 0) := by
  have h1 : ∀ ι, pmSumN 6 D W ι =
    W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 3 (ι 2) (ι 3)) * W (mkEdge 4 5 (ι 4) (ι 5)) +
    W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 4 (ι 2) (ι 4)) * W (mkEdge 3 5 (ι 3) (ι 5)) +
    W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 5 (ι 2) (ι 5)) * W (mkEdge 3 4 (ι 3) (ι 4)) +
    W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 3 (ι 1) (ι 3)) * W (mkEdge 4 5 (ι 4) (ι 5)) +
    W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 4 (ι 1) (ι 4)) * W (mkEdge 3 5 (ι 3) (ι 5)) +
    W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 5 (ι 1) (ι 5)) * W (mkEdge 3 4 (ι 3) (ι 4)) +
    W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 2 (ι 1) (ι 2)) * W (mkEdge 4 5 (ι 4) (ι 5)) +
    W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 4 (ι 1) (ι 4)) * W (mkEdge 2 5 (ι 2) (ι 5)) +
    W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 5 (ι 1) (ι 5)) * W (mkEdge 2 4 (ι 2) (ι 4)) +
    W (mkEdge 0 4 (ι 0) (ι 4)) * W (mkEdge 1 2 (ι 1) (ι 2)) * W (mkEdge 3 5 (ι 3) (ι 5)) +
    W (mkEdge 0 4 (ι 0) (ι 4)) * W (mkEdge 1 3 (ι 1) (ι 3)) * W (mkEdge 2 5 (ι 2) (ι 5)) +
    W (mkEdge 0 4 (ι 0) (ι 4)) * W (mkEdge 1 5 (ι 1) (ι 5)) * W (mkEdge 2 3 (ι 2) (ι 3)) +
    W (mkEdge 0 5 (ι 0) (ι 5)) * W (mkEdge 1 2 (ι 1) (ι 2)) * W (mkEdge 3 4 (ι 3) (ι 4)) +
    W (mkEdge 0 5 (ι 0) (ι 5)) * W (mkEdge 1 3 (ι 1) (ι 3)) * W (mkEdge 2 4 (ι 2) (ι 4)) +
    W (mkEdge 0 5 (ι 0) (ι 5)) * W (mkEdge 1 4 (ι 1) (ι 4)) * W (mkEdge 2 3 (ι 2) (ι 3)) := by
    intro ι
    rw [pmSumN_6_eval]
    dsimp [pmSumListAux, List.erase, List.map, List.sum, mkEdge]
    ring
  have h2 : pmSumN 6 1 (fun e => ∑ i : Fin D, ∑ j : Fin D, W ⟨e.u, e.v, i, j⟩) (fun _ => 0) =
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 1 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 4 5 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 1 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 5 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 1 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 4 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 4 5 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 5 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 4 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 4 5 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 5 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 4 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 5 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 5 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 3 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 2 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 3 4 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 3 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 4 i j)) +
    (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 0 5 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 1 4 i j)) * (∑ i : Fin D, ∑ j : Fin D, W (mkEdge 2 3 i j)) := by
    rw [pmSumN_6_eval]
    dsimp [pmSumListAux, List.erase, List.map, List.sum, mkEdge]
    ring
  have h3 : (∑ ι : V 6 → Fin D, pmSumN 6 D W ι) =
            ∑ ι : V 6 → Fin D,
    (W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 3 (ι 2) (ι 3)) * W (mkEdge 4 5 (ι 4) (ι 5)) +
    W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 4 (ι 2) (ι 4)) * W (mkEdge 3 5 (ι 3) (ι 5)) +
    W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 5 (ι 2) (ι 5)) * W (mkEdge 3 4 (ι 3) (ι 4)) +
    W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 3 (ι 1) (ι 3)) * W (mkEdge 4 5 (ι 4) (ι 5)) +
    W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 4 (ι 1) (ι 4)) * W (mkEdge 3 5 (ι 3) (ι 5)) +
    W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 5 (ι 1) (ι 5)) * W (mkEdge 3 4 (ι 3) (ι 4)) +
    W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 2 (ι 1) (ι 2)) * W (mkEdge 4 5 (ι 4) (ι 5)) +
    W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 4 (ι 1) (ι 4)) * W (mkEdge 2 5 (ι 2) (ι 5)) +
    W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 5 (ι 1) (ι 5)) * W (mkEdge 2 4 (ι 2) (ι 4)) +
    W (mkEdge 0 4 (ι 0) (ι 4)) * W (mkEdge 1 2 (ι 1) (ι 2)) * W (mkEdge 3 5 (ι 3) (ι 5)) +
    W (mkEdge 0 4 (ι 0) (ι 4)) * W (mkEdge 1 3 (ι 1) (ι 3)) * W (mkEdge 2 5 (ι 2) (ι 5)) +
    W (mkEdge 0 4 (ι 0) (ι 4)) * W (mkEdge 1 5 (ι 1) (ι 5)) * W (mkEdge 2 3 (ι 2) (ι 3)) +
    W (mkEdge 0 5 (ι 0) (ι 5)) * W (mkEdge 1 2 (ι 1) (ι 2)) * W (mkEdge 3 4 (ι 3) (ι 4)) +
    W (mkEdge 0 5 (ι 0) (ι 5)) * W (mkEdge 1 3 (ι 1) (ι 3)) * W (mkEdge 2 4 (ι 2) (ι 4)) +
    W (mkEdge 0 5 (ι 0) (ι 5)) * W (mkEdge 1 4 (ι 1) (ι 4)) * W (mkEdge 2 3 (ι 2) (ι 3))) := by
    apply Finset.sum_congr rfl
    intro ι _
    exact h1 ι
  rw [h3]
  simp only [Finset.sum_add_distrib]
  rw [sum_ι_factor_0, sum_ι_factor_1, sum_ι_factor_2, sum_ι_factor_3, sum_ι_factor_4,
      sum_ι_factor_5, sum_ι_factor_6_lem, sum_ι_factor_7, sum_ι_factor_8, sum_ι_factor_9,
      sum_ι_factor_10, sum_ι_factor_11, sum_ι_factor_12, sum_ι_factor_13, sum_ι_factor_14]
  exact h2.symm

noncomputable def S_F {N D : Nat} (W : WeightsN N D ℂ) (F : V N → Fin D → ℂ) : WeightsN N 1 ℂ :=
  fun e => ∑ i : Fin D, ∑ j : Fin D, F e.u i * F e.v j * W ⟨e.u, e.v, i, j⟩

lemma matrix_identity_6 (W : WeightsN 6 6 ℂ) (h : EqSystemN 6 6 W) (F : V 6 → Fin 6 → ℂ) :
  pmSumN 6 1 (S_F W F) (fun _ => 0) = ∑ c : Fin 6, ∏ u : Fin 6, F u c := by
  have h1 : (∑ ι : V 6 → Fin 6, (∏ u : Fin 6, F u (ι u)) * pmSumN 6 6 W ι) =
            pmSumN 6 1 (S_F W F) (fun _ => 0) := by
    have h_sum : (∑ ι : V 6 → Fin 6, (∏ u : Fin 6, F u (ι u)) * pmSumN 6 6 W ι) =
                 (∑ ι : V 6 → Fin 6, pmSumN 6 6 (W_mul_F W F) ι) := by
      apply Finset.sum_congr rfl
      intro ι _
      exact pmSumN_6_mul_F W F ι
    rw [h_sum]
    have h2 := sum_ι_pmSumN_6 (W_mul_F W F)
    have h3 : (fun (e : EdgeN 6 1) => ∑ i : Fin 6, ∑ j : Fin 6, W_mul_F W F ⟨e.u, e.v, i, j⟩) = S_F W F := by
      ext e
      unfold W_mul_F S_F
      rfl
    rw [h3] at h2
    exact h2
  have h2 := eq_sys_implies_rhs_6_matrix W h F
  rw [← h1, h2]

noncomputable def fix_zero (v : Fin 6 → ℂ) : Fin 6 → ℂ :=
  if (∀ c, v c = 0) then (fun _ => 1) else v

lemma fix_zero_nonzero (v : Fin 6 → ℂ) :
  ∃ c, fix_zero v c ≠ 0 := by
  delta Ne fix_zero
  exact (em _).elim (by simp_all) (if_neg ·▸not_forall.mp (by valid) )

lemma fix_zero_ortho (v : Fin 6 → ℂ) (x : Fin 6 → ℂ) (h : ∑ c, fix_zero v c * x c = 0) :
  ∑ c, v c * x c = 0 := by
  by_cases h_zero : ∀ c, v c = 0
  · norm_num[ *]
  · simp_all[fix_zero]

noncomputable def alt_vec (v : Fin 6 → ℂ) (i j : Fin 6) : Fin 6 → ℂ :=
  fun c => if c = i then -v j else if c = j then v i else 0

lemma alt_vec_ortho (v : Fin 6 → ℂ) (i j : Fin 6) (h_neq : i ≠ j) :
  ∑ c : Fin 6, v c * alt_vec v i j c = 0 := by
  simp_all[alt_vec,mul_comm]
  norm_num[ Finset.sum_ite, Ne.symm (by assumption), Finset.filter_eq']

lemma prod_alt_vec_eq (V : Fin 5 → Fin 6 → ℂ) (c_star : Fin 6) (j : Fin 5 → Fin 6)
  (hj : ∀ u, j u ≠ c_star) (h_not_all_eq : ∃ u v, j u ≠ j v) :
  (∑ c : Fin 6, alt_vec (V 0) c_star (j 0) c * alt_vec (V 1) c_star (j 1) c * alt_vec (V 2) c_star (j 2) c * alt_vec (V 3) c_star (j 3) c * alt_vec (V 4) c_star (j 4) c) =
  - (V 0 (j 0) * V 1 (j 1) * V 2 (j 2) * V 3 (j 3) * V 4 (j 4)) := by
  show∑x,id _ *(id _)*((id) _)*(id _)*(id _) = _
  norm_num[*,Finset.sum_ite,Finset.filter_eq']
  use fun and _ _ _=>by simp_all[ Fin.exists_iff_succ]

lemma span_2d_case (V : Fin 5 → Fin 6 → ℂ) (c1 c2 : Fin 6)
  (h_span : ∀ u, ∀ j, j ≠ c1 → j ≠ c2 → V u j = 0) :
  ∃ X : Fin 5 → Fin 6 → ℂ, (∀ u : Fin 5, ∑ c : Fin 6, V u c * X u c = 0) ∧ (∑ c : Fin 6, X 0 c * X 1 c * X 2 c * X 3 c * X 4 c ≠ 0) := by
  have h_c3 : ∃ c3 : Fin 6, c3 ≠ c1 ∧ c3 ≠ c2 := by
    exact ( Finset.not_subset.1 (by decide ∘(Finset.card_fin 6▸ Finset.card_mono ·|>.trans Finset.card_le_two):¬_ ⊆{c1,c2})).imp (by norm_num)
  rcases h_c3 with ⟨c3, hc3_1, hc3_2⟩
  use fun _ c => if c = c3 then 1 else 0
  constructor
  · intro u
    norm_num [ *]
  · norm_num

lemma exists_good_c_star (V : Fin 5 → Fin 6 → ℂ) (h_nonzero : ∀ u, ∃ c, V u c ≠ 0) :
  ∃ c_star : Fin 6, ∀ u : Fin 5, ∃ j : Fin 6, j ≠ c_star ∧ V u j ≠ 0 := by
  choose R M using@h_nonzero
  exact (not_forall.1 (by decide ∘ Fin.le_of_surjective R)).imp fun and A B => ⟨ _,A.comp (⟨B,·⟩), M B⟩

lemma choose_j (V : Fin 5 → Fin 6 → ℂ) (c_star : Fin 6)
  (hc_star : ∀ u : Fin 5, ∃ j : Fin 6, j ≠ c_star ∧ V u j ≠ 0)
  (h_not_span : ¬ ∃ d, ∀ u, ∀ j, j ≠ c_star → j ≠ d → V u j = 0) :
  ∃ j : Fin 5 → Fin 6, (∀ u, j u ≠ c_star) ∧ (∀ u, V u (j u) ≠ 0) ∧ (∃ u v, j u ≠ j v) := by
  refine(Classical.axiomOfChoice hc_star).elim fun a s=>by_contra fun and=>h_not_span ⟨a 0,fun R L A B=>by_contra fun and' =>and ⟨ fun and=>ite (and=R) L (a and),.symm ?_⟩⟩
  use⟨ (by cases eq_or_ne · R with norm_num[*]),by_contra fun and' =>and ⟨a, (s ·|>.1), (s ·|>.2),R+1, R,by grind⟩⟩,by norm_num[*,ite_eq_iff]

lemma elementary_axiom_nonzero (V : Fin 5 → Fin 6 → ℂ) (h_nonzero : ∀ u, ∃ c, V u c ≠ 0) :
  ∃ X : Fin 5 → Fin 6 → ℂ, (∀ u : Fin 5, ∑ c : Fin 6, V u c * X u c = 0) ∧ (∑ c : Fin 6, X 0 c * X 1 c * X 2 c * X 3 c * X 4 c ≠ 0) := by
  have h_c_star : ∃ c_star : Fin 6, ∀ u : Fin 5, ∃ j : Fin 6, j ≠ c_star ∧ V u j ≠ 0 := by
    apply exists_good_c_star V h_nonzero
  rcases h_c_star with ⟨c_star, hc_star⟩
  by_cases h_span : ∃ d, ∀ u, ∀ j, j ≠ c_star → j ≠ d → V u j = 0
  · rcases h_span with ⟨d, hd⟩
    exact span_2d_case V c_star d hd
  · have h_j : ∃ j : Fin 5 → Fin 6, (∀ u, j u ≠ c_star) ∧ (∀ u, V u (j u) ≠ 0) ∧ (∃ u v, j u ≠ j v) := by
      apply choose_j V c_star hc_star h_span
    rcases h_j with ⟨j, hj_neq, hj_nonzero, hj_diff⟩
    use fun u => alt_vec (V u) c_star (j u)
    constructor
    · intro u
      exact alt_vec_ortho (V u) c_star (j u) (hj_neq u).symm
    · have h_prod := prod_alt_vec_eq V c_star j hj_neq hj_diff
      rw [h_prod]
      apply neg_ne_zero.mpr
      apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero
            · exact hj_nonzero 0
            · exact hj_nonzero 1
          · exact hj_nonzero 2
        · exact hj_nonzero 3
      · exact hj_nonzero 4

/-- For any 5 vectors V_1..V_5 in C^6, there exist vectors X_1..X_5 such that X_u is orthogonal to V_u,
    and the sum of their component-wise products is non-zero. -/
lemma elementary_axiom (V : Fin 5 → Fin 6 → ℂ) :
  ∃ X : Fin 5 → Fin 6 → ℂ, (∀ u : Fin 5, ∑ c : Fin 6, V u c * X u c = 0) ∧ (∑ c : Fin 6, X 0 c * X 1 c * X 2 c * X 3 c * X 4 c ≠ 0) := by
  have h_X := elementary_axiom_nonzero (fun u => fix_zero (V u)) (fun u => fix_zero_nonzero (V u))
  rcases h_X with ⟨X, hX_ortho, hX_prod⟩
  use X
  constructor
  · intro u
    exact fix_zero_ortho (V u) (X u) (hX_ortho u)
  · exact hX_prod

noncomputable def construct_F (X : Fin 5 → Fin 6 → ℂ) : V 6 → Fin 6 → ℂ
| 0 => fun _ => 1
| 1 => X 0
| 2 => X 1
| 3 => X 2
| 4 => X 3
| 5 => X 4

noncomputable def construct_V (W : WeightsN 6 6 ℂ) : Fin 5 → Fin 6 → ℂ
| 0, c => ∑ i : Fin 6, W ⟨0, 1, i, c⟩
| 1, c => ∑ i : Fin 6, W ⟨0, 2, i, c⟩
| 2, c => ∑ i : Fin 6, W ⟨0, 3, i, c⟩
| 3, c => ∑ i : Fin 6, W ⟨0, 4, i, c⟩
| 4, c => ∑ i : Fin 6, W ⟨0, 5, i, c⟩

lemma S_F_0_1 (W : WeightsN 6 6 ℂ) (X : Fin 5 → Fin 6 → ℂ)
  (hX : ∀ u : Fin 5, ∑ c : Fin 6, construct_V W u c * X u c = 0) :
  S_F W (construct_F X) ⟨0, 1, 0, 0⟩ = 0 := by
  have h_eq : S_F W (construct_F X) ⟨0, 1, 0, 0⟩ = ∑ j : Fin 6, X 0 j * ∑ i : Fin 6, W ⟨0, 1, i, j⟩ := by
    unfold S_F construct_F
    calc (∑ i : Fin 6, ∑ j : Fin 6, 1 * X 0 j * W ⟨0, 1, i, j⟩)
      _ = ∑ j : Fin 6, ∑ i : Fin 6, X 0 j * W ⟨0, 1, i, j⟩ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ j : Fin 6, X 0 j * ∑ i : Fin 6, W ⟨0, 1, i, j⟩ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum]
  rw [h_eq]
  have h_hx := hX 0
  unfold construct_V at h_hx
  have h_ring : (∑ j : Fin 6, X 0 j * ∑ i : Fin 6, W ⟨0, 1, i, j⟩) = ∑ c : Fin 6, (∑ i : Fin 6, W ⟨0, 1, i, c⟩) * X 0 c := by
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [h_ring]
  exact h_hx

lemma S_F_0_2 (W : WeightsN 6 6 ℂ) (X : Fin 5 → Fin 6 → ℂ)
  (hX : ∀ u : Fin 5, ∑ c : Fin 6, construct_V W u c * X u c = 0) :
  S_F W (construct_F X) ⟨0, 2, 0, 0⟩ = 0 := by
  have h_eq : S_F W (construct_F X) ⟨0, 2, 0, 0⟩ = ∑ j : Fin 6, X 1 j * ∑ i : Fin 6, W ⟨0, 2, i, j⟩ := by
    unfold S_F construct_F
    calc (∑ i : Fin 6, ∑ j : Fin 6, 1 * X 1 j * W ⟨0, 2, i, j⟩)
      _ = ∑ j : Fin 6, ∑ i : Fin 6, X 1 j * W ⟨0, 2, i, j⟩ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ j : Fin 6, X 1 j * ∑ i : Fin 6, W ⟨0, 2, i, j⟩ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum]
  rw [h_eq]
  have h_hx := hX 1
  unfold construct_V at h_hx
  have h_ring : (∑ j : Fin 6, X 1 j * ∑ i : Fin 6, W ⟨0, 2, i, j⟩) = ∑ c : Fin 6, (∑ i : Fin 6, W ⟨0, 2, i, c⟩) * X 1 c := by
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [h_ring]
  exact h_hx

lemma S_F_0_3 (W : WeightsN 6 6 ℂ) (X : Fin 5 → Fin 6 → ℂ)
  (hX : ∀ u : Fin 5, ∑ c : Fin 6, construct_V W u c * X u c = 0) :
  S_F W (construct_F X) ⟨0, 3, 0, 0⟩ = 0 := by
  have h_eq : S_F W (construct_F X) ⟨0, 3, 0, 0⟩ = ∑ j : Fin 6, X 2 j * ∑ i : Fin 6, W ⟨0, 3, i, j⟩ := by
    unfold S_F construct_F
    calc (∑ i : Fin 6, ∑ j : Fin 6, 1 * X 2 j * W ⟨0, 3, i, j⟩)
      _ = ∑ j : Fin 6, ∑ i : Fin 6, X 2 j * W ⟨0, 3, i, j⟩ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ j : Fin 6, X 2 j * ∑ i : Fin 6, W ⟨0, 3, i, j⟩ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum]
  rw [h_eq]
  have h_hx := hX 2
  unfold construct_V at h_hx
  have h_ring : (∑ j : Fin 6, X 2 j * ∑ i : Fin 6, W ⟨0, 3, i, j⟩) = ∑ c : Fin 6, (∑ i : Fin 6, W ⟨0, 3, i, c⟩) * X 2 c := by
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [h_ring]
  exact h_hx

lemma S_F_0_4 (W : WeightsN 6 6 ℂ) (X : Fin 5 → Fin 6 → ℂ)
  (hX : ∀ u : Fin 5, ∑ c : Fin 6, construct_V W u c * X u c = 0) :
  S_F W (construct_F X) ⟨0, 4, 0, 0⟩ = 0 := by
  have h_eq : S_F W (construct_F X) ⟨0, 4, 0, 0⟩ = ∑ j : Fin 6, X 3 j * ∑ i : Fin 6, W ⟨0, 4, i, j⟩ := by
    unfold S_F construct_F
    calc (∑ i : Fin 6, ∑ j : Fin 6, 1 * X 3 j * W ⟨0, 4, i, j⟩)
      _ = ∑ j : Fin 6, ∑ i : Fin 6, X 3 j * W ⟨0, 4, i, j⟩ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ j : Fin 6, X 3 j * ∑ i : Fin 6, W ⟨0, 4, i, j⟩ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum]
  rw [h_eq]
  have h_hx := hX 3
  unfold construct_V at h_hx
  have h_ring : (∑ j : Fin 6, X 3 j * ∑ i : Fin 6, W ⟨0, 4, i, j⟩) = ∑ c : Fin 6, (∑ i : Fin 6, W ⟨0, 4, i, c⟩) * X 3 c := by
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [h_ring]
  exact h_hx

lemma S_F_0_5 (W : WeightsN 6 6 ℂ) (X : Fin 5 → Fin 6 → ℂ)
  (hX : ∀ u : Fin 5, ∑ c : Fin 6, construct_V W u c * X u c = 0) :
  S_F W (construct_F X) ⟨0, 5, 0, 0⟩ = 0 := by
  have h_eq : S_F W (construct_F X) ⟨0, 5, 0, 0⟩ = ∑ j : Fin 6, X 4 j * ∑ i : Fin 6, W ⟨0, 5, i, j⟩ := by
    unfold S_F construct_F
    calc (∑ i : Fin 6, ∑ j : Fin 6, 1 * X 4 j * W ⟨0, 5, i, j⟩)
      _ = ∑ j : Fin 6, ∑ i : Fin 6, X 4 j * W ⟨0, 5, i, j⟩ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ j : Fin 6, X 4 j * ∑ i : Fin 6, W ⟨0, 5, i, j⟩ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum]
  rw [h_eq]
  have h_hx := hX 4
  unfold construct_V at h_hx
  have h_ring : (∑ j : Fin 6, X 4 j * ∑ i : Fin 6, W ⟨0, 5, i, j⟩) = ∑ c : Fin 6, (∑ i : Fin 6, W ⟨0, 5, i, c⟩) * X 4 c := by
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [h_ring]
  exact h_hx

lemma pmSum_zero (W : WeightsN 6 6 ℂ) (X : Fin 5 → Fin 6 → ℂ)
  (hX : ∀ u : Fin 5, ∑ c : Fin 6, construct_V W u c * X u c = 0) :
  pmSumN 6 1 (S_F W (construct_F X)) (fun _ => 0) = 0 := by
  have h1 := S_F_0_1 W X hX
  have h2 := S_F_0_2 W X hX
  have h3 := S_F_0_3 W X hX
  have h4 := S_F_0_4 W X hX
  have h5 := S_F_0_5 W X hX
  have h_eval : pmSumN 6 1 (S_F W (construct_F X)) (fun _ => 0) =
    S_F W (construct_F X) ⟨0, 1, 0, 0⟩ * S_F W (construct_F X) ⟨2, 3, 0, 0⟩ * S_F W (construct_F X) ⟨4, 5, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 1, 0, 0⟩ * S_F W (construct_F X) ⟨2, 4, 0, 0⟩ * S_F W (construct_F X) ⟨3, 5, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 1, 0, 0⟩ * S_F W (construct_F X) ⟨2, 5, 0, 0⟩ * S_F W (construct_F X) ⟨3, 4, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 2, 0, 0⟩ * S_F W (construct_F X) ⟨1, 3, 0, 0⟩ * S_F W (construct_F X) ⟨4, 5, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 2, 0, 0⟩ * S_F W (construct_F X) ⟨1, 4, 0, 0⟩ * S_F W (construct_F X) ⟨3, 5, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 2, 0, 0⟩ * S_F W (construct_F X) ⟨1, 5, 0, 0⟩ * S_F W (construct_F X) ⟨3, 4, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 3, 0, 0⟩ * S_F W (construct_F X) ⟨1, 2, 0, 0⟩ * S_F W (construct_F X) ⟨4, 5, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 3, 0, 0⟩ * S_F W (construct_F X) ⟨1, 4, 0, 0⟩ * S_F W (construct_F X) ⟨2, 5, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 3, 0, 0⟩ * S_F W (construct_F X) ⟨1, 5, 0, 0⟩ * S_F W (construct_F X) ⟨2, 4, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 4, 0, 0⟩ * S_F W (construct_F X) ⟨1, 2, 0, 0⟩ * S_F W (construct_F X) ⟨3, 5, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 4, 0, 0⟩ * S_F W (construct_F X) ⟨1, 3, 0, 0⟩ * S_F W (construct_F X) ⟨2, 5, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 4, 0, 0⟩ * S_F W (construct_F X) ⟨1, 5, 0, 0⟩ * S_F W (construct_F X) ⟨2, 3, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 5, 0, 0⟩ * S_F W (construct_F X) ⟨1, 2, 0, 0⟩ * S_F W (construct_F X) ⟨3, 4, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 5, 0, 0⟩ * S_F W (construct_F X) ⟨1, 3, 0, 0⟩ * S_F W (construct_F X) ⟨2, 4, 0, 0⟩ +
    S_F W (construct_F X) ⟨0, 5, 0, 0⟩ * S_F W (construct_F X) ⟨1, 4, 0, 0⟩ * S_F W (construct_F X) ⟨2, 3, 0, 0⟩ := by
    rw [pmSumN_6_eval]
    dsimp [pmSumListAux, List.erase, List.map, List.sum, mkEdge]
    ring
  rw [h_eval, h1, h2, h3, h4, h5]
  ring

lemma RHS_eval (X : Fin 5 → Fin 6 → ℂ) :
  (∑ c : Fin 6, ∏ u : Fin 6, construct_F X u c) = ∑ c : Fin 6, X 0 c * X 1 c * X 2 c * X 3 c * X 4 c := by
  apply Finset.sum_congr rfl
  intro c _
  have h_prod : ∏ u : Fin 6, construct_F X u c = construct_F X 0 c * construct_F X 1 c * construct_F X 2 c * construct_F X 3 c * construct_F X 4 c * construct_F X 5 c := by
    apply Fin.prod_univ_six
  rw [h_prod]
  unfold construct_F
  ring

lemma no_6_6 : ¬∃ W : WeightsN 6 6 ℂ, EqSystemN 6 6 W := by
  intro ⟨W, hW⟩
  have h_id := matrix_identity_6 W hW
  have ⟨X, hX_ortho, hX_nz⟩ := elementary_axiom (construct_V W)
  have h_LHS := pmSum_zero W X hX_ortho
  have h_eval := h_id (construct_F X)
  rw [h_LHS] at h_eval
  have h_RHS := RHS_eval X
  rw [h_RHS] at h_eval
  exact hX_nz h_eval.symm


/-- For $N = 6$ and $D = 6$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$?

The DeepMind Prover Agent has found a formal proof for this statement.
-/
@[category research solved, AMS 5 14 81]
theorem eqSystem6_no_solution_d6 :
    answer(True) ↔
      ¬ ∃ W : WeightsN 6 6 ℂ, EqSystemN 6 6 W := by
  constructor
  · intro _
    exact no_6_6
  · intro _
    trivial

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
