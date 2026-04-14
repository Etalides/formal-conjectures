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
# Hadwiger Conjecture

The Hadwiger conjecture, proposed by Hugo Hadwiger in 1943, states that if a graph has no
$K_t$-minor then it is $(t-1)$-colorable. Equivalently, every graph with chromatic number $t$
contains $K_t$ as a minor.

The cases $t \le 4$ are straightforward. The case $t = 5$ is equivalent to the Four Color Theorem
(proved by Appel and Haken in 1976). The case $t = 6$ was proved by Robertson, Seymour, and Thomas
in 1993. The conjecture remains open for $t \ge 7$.

This file formalises the Four Color Theorem and the Five Color Theorem using the hypermap
framework, closely following Gonthier's formal proof of the Four Color Theorem in Coq.

## Hypermaps

A **hypermap** is a finite type $D$ (of *darts*) equipped with three permutations
$e$ (*edge*), $n$ (*node*), $f$ (*face*) satisfying the triangular identity
$n \circ f \circ e = \mathrm{id}$. This is the central combinatorial abstraction used in
Gonthier's proof.

For a simple graph with a rotation system (cyclic orderings of neighbours at each vertex):
- `edge` is the dart-reversal involution,
- `node` is the rotation at each vertex,
- `face` is determined by the triangular identity: $f = n^{-1} \circ e^{-1} = n^{-1} \circ e$.

The **genus** of a hypermap is defined via the Euler formula. A hypermap is **planar** iff
its genus is 0.

*References:*
- [Wikipedia: Hadwiger conjecture](https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory))
- [Wikipedia: Four color theorem](https://en.wikipedia.org/wiki/Four_color_theorem)
- [Wikipedia: Five color theorem](https://en.wikipedia.org/wiki/Five_color_theorem)
- G. Gonthier, *Formal Proof—The Four-Color Theorem*, Notices of the AMS 55(11), 2008,
  pp. 1382–1393.
- K. Appel and W. Haken, *Every planar map is four colorable*, Bull. Amer. Math. Soc. 82 (1976),
  711–712.
- P. J. Heawood, *Map-colour theorem*, Quart. J. Pure Appl. Math. 24 (1890), 332–338.
- [Four-color theorem formal proof in Coq on GitHub](https://github.com/rocq-community/fourcolor)
-/

namespace HadwigerConjecture

/- ## Hypermaps

Following `hypermap.v` in the Coq fourcolor library. A hypermap is a finite type of darts with
three permutations satisfying the triangular identity `node ∘ face ∘ edge = id`.
-/

/--
A *hypermap* is a finite type of darts equipped with three permutations — `edge`, `node`, and
`face` — satisfying the triangular identity `node (face (edge d)) = d` for all darts `d`.

This is the central combinatorial object in Gonthier's proof of the Four Color Theorem
(`hypermap.v` in the Coq fourcolor library). The three permutations encode the combinatorial
structure of a map on an orientable surface.

Cf. `Record hypermap` in
[hypermap.v](https://github.com/rocq-community/fourcolor/blob/master/theories/proof/hypermap.v).
-/
structure Hypermap where
  /-- The type of darts. -/
  Dart : Type*
  [instFintype : Fintype Dart]
  [instDecidableEq : DecidableEq Dart]
  /-- The edge permutation. In a graph context, this is dart reversal. -/
  edge : Equiv.Perm Dart
  /-- The node permutation. In a graph context, this is the rotation at each vertex. -/
  node : Equiv.Perm Dart
  /-- The face permutation. Determined by the triangular identity. -/
  face : Equiv.Perm Dart
  /-- The triangular identity: `node ∘ face ∘ edge = id`.
  Cf. `cancel3 edge node face` in Gonthier's `hypermap.v`. -/
  edgeK : ∀ d, node (face (edge d)) = d

attribute [instance] Hypermap.instFintype Hypermap.instDecidableEq

namespace Hypermap

variable (G : Hypermap)

/-- The number of orbits of a permutation on a finite type, computed as the number of parts
in its cycle partition (including fixed points as 1-cycles). This corresponds to `fcard`
in MathComp. -/
noncomputable def fcard (σ : Equiv.Perm G.Dart) : ℕ :=
  σ.partition.parts.card

/--
Two darts are *glinked* if one is the image of the other under `edge`, `node`, or `face`.
Cf. `glink` in Gonthier's `hypermap.v`:
`Definition glink : rel G := relU (frel edge) (relU (frel node) (frel face)).`
-/
def glink (x y : G.Dart) : Prop :=
  G.edge x = y ∨ G.node x = y ∨ G.face x = y

/--
Two darts are in the same *connected component* if they are connected by a sequence of glinks.
Cf. `gcomp` (= `connect glink`) in Gonthier's `hypermap.v`.
-/
def gcomp : G.Dart → G.Dart → Prop :=
  Relation.EqvGen G.glink

/-- The setoid of darts up to glink-connectivity. -/
def glinkSetoid : Setoid G.Dart :=
  Relation.EqvGen.setoid G.glink

/-- The number of glink-connected components of a hypermap.
Cf. `n_comp glink G` in Gonthier's `hypermap.v`. -/
noncomputable def numComponents : ℕ := by
  haveI : Fintype (Quotient G.glinkSetoid) := Fintype.ofFinite _
  exact Fintype.card (Quotient G.glinkSetoid)

/--
The left-hand side of the hypermap Euler formula:
$\text{Euler\_lhs} = 2 \cdot C + |D|$
where $C$ is the number of connected components and $|D|$ is the number of darts.

Cf. `Euler_lhs` in Gonthier's `hypermap.v`:
`Definition Euler_lhs := double (n_comp glink G) + #|G|.`
-/
noncomputable def eulerLhs : ℕ :=
  2 * G.numComponents + Fintype.card G.Dart

/--
The right-hand side of the hypermap Euler formula:
$\text{Euler\_rhs} = E + N + F$
where $E$, $N$, $F$ are the number of orbits of the edge, node, and face permutations.

Cf. `Euler_rhs` in Gonthier's `hypermap.v`:
`Definition Euler_rhs := fcard edge G + (fcard node G + fcard face G).`
-/
noncomputable def eulerRhs : ℕ :=
  G.fcard G.edge + (G.fcard G.node + G.fcard G.face)

/--
The *genus* of a hypermap, defined as $(E + N + F - 2C - |D|) / 2$.
A planar hypermap has genus 0.

Cf. `genus` in Gonthier's `hypermap.v`:
`Definition genus := (Euler_lhs - Euler_rhs)./2.`

Note: Gonthier defines `genus = (Euler_lhs - Euler_rhs) / 2` but proves that `Euler_rhs ≥
Euler_lhs` never occurs (the genus is always non-negative). We follow the same convention.
-/
noncomputable def genus : ℕ :=
  (G.eulerRhs - G.eulerLhs) / 2

/--
A hypermap is *planar* if its genus is 0.

Cf. `planar` in Gonthier's `hypermap.v`:
`Definition planar : Prop := genus == 0.`
-/
def planar : Prop := G.genus = 0

end Hypermap

/- ## Bridgelessness and coloring

Following `coloring.v` in the Coq fourcolor library.
-/

/--
A hypermap is *bridgeless* if no dart is a fixed point of the edge permutation.
Equivalently, every edge link connects two distinct darts.

Cf. `bridgeless` in Gonthier's `geometry.v`.
-/
def Hypermap.bridgeless (G : Hypermap) : Prop :=
  ∀ d : G.Dart, G.edge d ≠ d

/--
A *coloring* of a hypermap assigns colors to darts such that:
1. Adjacent darts (connected by an edge link) get **different** colors.
2. Darts in the same face orbit get the **same** color.

This is a *map coloring* in Gonthier's terminology.

Cf. `coloring` in Gonthier's `coloring.v`:
`Definition coloring (k : G -> color) :=`
`  invariant edge k =1 pred0 /\ invariant face k =1 G.`
-/
def Hypermap.IsColoring (G : Hypermap) {n : ℕ} (k : G.Dart → Fin n) : Prop :=
  (∀ d, k (G.edge d) ≠ k d) ∧ (∀ d, k (G.face d) = k d)

/--
A hypermap is *four-colorable* if it admits a coloring with 4 colors.

Cf. `four_colorable` in Gonthier's `coloring.v`:
`Definition four_colorable := exists k, coloring k.`
-/
def Hypermap.fourColorable (G : Hypermap) : Prop :=
  ∃ k : G.Dart → Fin 4, G.IsColoring k

/--
A hypermap is *planar and bridgeless* if it satisfies both conditions.

Cf. `planar_bridgeless` in Gonthier's `geometry.v`.
-/
def Hypermap.planarBridgeless (G : Hypermap) : Prop :=
  G.planar ∧ G.bridgeless

/- ## The combinatorial Four Color Theorem

The core result from Gonthier's proof, stated at the hypermap level.
-/

/--
The **Combinatorial Four Color Theorem** for hypermaps: every planar bridgeless hypermap is
four-colorable.

This is the central result of Gonthier's formalization, from which the topological Four Color
Theorem is derived.

Cf. `four_color_hypermap` in Gonthier's `combinatorial4ct.v`:
`Theorem four_color_hypermap G : planar_bridgeless G -> four_colorable G.`
-/
@[category research solved, AMS 5,
  formal_proof using other_system at "https://github.com/rocq-community/fourcolor"]
theorem four_color_hypermap (G : Hypermap) (hG : G.planarBridgeless) :
    G.fourColorable := by
  sorry

/- ## Hypermaps from simple graphs

To state the Four Color Theorem for `SimpleGraph`, we construct a hypermap from a graph equipped
with a rotation system, matching Gonthier's framework.
-/

open SimpleGraph in
/--
The dart-reversal involution as a permutation on darts.
Each dart `(u, v)` is sent to `(v, u)`.
-/
def dartSymmEquiv {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] :
    Equiv.Perm G.Dart where
  toFun := Dart.symm
  invFun := Dart.symm
  left_inv := Dart.symm_symm
  right_inv := Dart.symm_symm

open SimpleGraph in
/--
A *rotation system* for a graph `G` is a permutation of the darts of `G` that preserves the
source vertex of each dart. This corresponds to the `node` permutation in a hypermap.
-/
structure RotationSystem {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- The rotation permutation on darts, preserving the source vertex. -/
  σ : Equiv.Perm G.Dart
  /-- The rotation preserves the source vertex of each dart. -/
  source_preserved : ∀ d, (σ d).fst = d.fst

open SimpleGraph in
/--
Constructs a `Hypermap` from a `SimpleGraph` equipped with a `RotationSystem`.

- `edge` is the dart-reversal involution (`Dart.symm`).
- `node` is the rotation (`σ`).
- `face` is determined by the triangular identity: `face = node⁻¹ ∘ edge`.
  (Since `edge` is an involution, `edge⁻¹ = edge`.)

This matches Gonthier's convention where `cancel3 edge node face` means
`∀ d, node (face (edge d)) = d`.
-/
def RotationSystem.toHypermap {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (r : RotationSystem G) : Hypermap where
  Dart := G.Dart
  edge := dartSymmEquiv G
  node := r.σ
  face := r.σ⁻¹ * dartSymmEquiv G
  edgeK d := by
    change r.σ (r.σ⁻¹ ((dartSymmEquiv G) ((dartSymmEquiv G) d))) = d
    rw [show (dartSymmEquiv G) ((dartSymmEquiv G) d) = d from
      (dartSymmEquiv G).apply_eq_iff_eq_symm_apply.mpr rfl]
    exact r.σ.apply_symm_apply d

open SimpleGraph in
/--
A graph `G` is *planar* if it admits a rotation system whose associated hypermap is planar
in the sense of Gonthier (genus 0).
-/
def SimpleGraph.IsPlanar {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ r : RotationSystem G, r.toHypermap.planar

/- ## The Four Color Theorem and Five Color Theorem for graphs -/

variable {V : Type*} [Fintype V] [DecidableEq V]

open SimpleGraph in
/--
The **Four Color Theorem**: Every finite planar graph is 4-colorable.

Proved by Kenneth Appel and Wolfgang Haken in 1976, with a computer-assisted proof. A simplified
proof was given by Robertson, Sanders, Seymour, and Thomas in 1997, and a formal proof in Coq
was completed by Gonthier in 2005.
-/
@[category research solved, AMS 5,
  formal_proof using other_system at "https://github.com/rocq-community/fourcolor"]
theorem four_color_theorem
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : SimpleGraph.IsPlanar G) :
    G.Colorable 4 := by
  sorry

open SimpleGraph in
/--
The **Five Color Theorem**: Every finite planar graph is 5-colorable.

Proved independently by Percy John Heawood in 1890 and by Lothar Heffter in 1891.
This is a weaker result than the Four Color Theorem.
-/
@[category research solved, AMS 5]
theorem five_color_theorem
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : SimpleGraph.IsPlanar G) :
    G.Colorable 5 := by
  sorry

end HadwigerConjecture
