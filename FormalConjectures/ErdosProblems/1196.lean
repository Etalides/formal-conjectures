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

namespace Erdos1196

open scoped Asymptotics

-- TODO(Paul-Lez): add this to ForMathlib. I suspect this is the right generalisation from the natural number case?
/-- A set is primitive if no non-associated elements of the set divide each other. -/
def IsPrimitive {M : Type*} [CommMonoid M] (A : Set M) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → Associated x y

open Filter Nat Real
open ArithmeticFunction (vonMangoldt)

noncomputable section
/-! ## Definitions -/
/-- The von Mangoldt function as a real number -/
def Λ' (q : ℕ) : ℝ := vonMangoldt q
/-- Boundary mass at node n. This represents the "source weight" at node n
in the divisor recursion. It consists of two parts:
- contributions from small prime power divisors q < Y
- contributions from large prime power divisors q ≥ Y where a/q < X (entry nodes) -/
def bMass (X Y : ℕ) (n : ℕ) : ℝ :=
  if n < 2 then 0
  else 1 / ((n : ℝ) * (Real.log n) ^ 2) *
    ((n.divisors.filter (fun q => 0 < q ∧ q < Y)).sum (fun q => Λ' q)
   + (n.divisors.filter (fun q => Y ≤ q ∧ n / q < X)).sum (fun q => Λ' q))
def IsPrimitiveNat (A : Set ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ∣ y → x = y

/-- On ℕ, `Associated` is the same as equality (since ℕˣ = {1}) -/
lemma isPrimitive_implies_nat {A : Set ℕ} (h : IsPrimitive A) : IsPrimitiveNat A := by
  intro x hx y hy hxy
  have h' := h x hx y hy hxy
  rwa [associated_eq_eq] at h'

/-! ## Proved analytic sub-lemmas -/
/-
Sum of `1/(n (log n)²)` over `n ∈ [K, N]` is at most `2/log K` for `K ≥ 2`.
    Proved via integral comparison with `∫ dt/(t (log t)²) = -1/log t`.
-/
lemma sum_inv_n_logsq_bound (K : ℕ) (hK : 2 ≤ K) (N : ℕ) :
    (Finset.Icc K N).sum (fun n => 1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤
    2 / Real.log K := by
  by_cases hN : N < K;
  · norm_num [ Finset.Icc_eq_empty_of_lt hN ];
    positivity;
  · -- Applying the integral comparison test, we get:
    have h_integral_comparison : ∑ n ∈ Finset.Icc K N, (1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤ 1 / ((K : ℝ) * (Real.log K) ^ 2) + ∫ x in (K : ℝ)..N, (1 / (x * (Real.log x) ^ 2)) := by
      have h_integral_comparison : ∀ n ∈ Finset.Icc (K + 1) N, (1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤ ∫ x in (n - 1 : ℝ)..n, (1 / (x * (Real.log x) ^ 2)) := by
        intros n hn;
        -- Since $1/(x (\log x)^2)$ is decreasing for $x \geq 2$, we have:
        have h_decreasing : ∀ x ∈ Set.Icc (n - 1 : ℝ) n, (1 / ((x : ℝ) * (Real.log x) ^ 2)) ≥ (1 / ((n : ℝ) * (Real.log n) ^ 2)) := by
          intros x hx;
          gcongr <;> norm_num at *;
          · exact mul_pos ( by linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ( sq_pos_of_pos ( Real.log_pos ( by linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) );
          · linarith;
          · exact Real.log_nonneg ( by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ] );
          · linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ];
          · linarith;
        refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ h_decreasing ) <;> norm_num;
        apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ] ) ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ] ) ) );
      have h_integral_comparison : ∑ n ∈ Finset.Icc (K + 1) N, (1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤ ∫ x in (K : ℝ)..N, (1 / (x * (Real.log x) ^ 2)) := by
        have h_integral_comparison : ∑ n ∈ Finset.Icc (K + 1) N, ∫ x in (n - 1 : ℝ)..n, (1 / (x * (Real.log x) ^ 2)) = ∫ x in (K : ℝ)..N, (1 / (x * (Real.log x) ^ 2)) := by
          erw [ Finset.sum_Ico_eq_sum_range ];
          convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
          · ring;
          · rw [ Nat.cast_sub ] <;> push_cast <;> linarith;
          · intro k hk; apply_rules [ ContinuousOn.intervalIntegrable ];
            exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( K : ℝ ) ≥ 2 by norm_cast ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( K : ℝ ) ≥ 2 by norm_cast ] ) ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( K : ℝ ) ≥ 2 by norm_cast ] ) ) );
        exact h_integral_comparison ▸ Finset.sum_le_sum ‹_›;
      erw [ Finset.sum_Ico_eq_sub _ ] at * <;> norm_num at *;
      · norm_num [ Finset.sum_range_succ ] at * ; linarith;
      · lia;
      · linarith;
    -- Evaluating the integral, we get:
    have h_integral_eval : ∫ x in (K : ℝ)..N, (1 / (x * (Real.log x) ^ 2)) = -1 / Real.log N + 1 / Real.log K := by
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      use fun x => -1 / Real.log x;
      · ring;
      · intro x hx;
        convert HasDerivAt.div ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_log ( show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith [ show ( K : ℝ ) ≥ 2 by norm_cast, show ( N : ℝ ) ≥ K by norm_cast; linarith ] ) ) ( ne_of_gt <| Real.log_pos <| show x > 1 by cases Set.mem_uIcc.mp hx <;> linarith [ show ( K : ℝ ) ≥ 2 by norm_cast, show ( N : ℝ ) ≥ K by norm_cast; linarith ] ) using 1 ; ring;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( K : ℝ ) ≥ 2 by norm_cast, show ( N : ℝ ) ≥ K by norm_cast; linarith ] ) _ ) <| ne_of_gt <| mul_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( K : ℝ ) ≥ 2 by norm_cast, show ( N : ℝ ) ≥ K by norm_cast; linarith ] ) <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( K : ℝ ) ≥ 2 by norm_cast, show ( N : ℝ ) ≥ K by norm_cast; linarith ] ;
    -- Since $K \geq 2$, we have $\frac{1}{K (\log K)^2} \leq \frac{1}{\log K}$.
    have h_bound : 1 / ((K : ℝ) * (Real.log K) ^ 2) ≤ 1 / Real.log K := by
      gcongr;
      · exact Real.log_pos <| Nat.one_lt_cast.mpr hK;
      · have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ show ( K : ℝ ) ≥ 2 by norm_cast, Real.log_le_log ( by positivity ) ( show ( K : ℝ ) ≥ 2 by norm_cast ), mul_le_mul_of_nonneg_right ( show ( K : ℝ ) ≥ 2 by norm_cast ) ( Real.log_nonneg ( show ( K : ℝ ) ≥ 1 by norm_cast; linarith ) ) ];
    ring_nf at *;
    linarith [ inv_nonneg.2 ( Real.log_nonneg ( show ( K : ℝ ) ≥ 1 by norm_cast; linarith ) ), inv_nonneg.2 ( Real.log_nonneg ( show ( N : ℝ ) ≥ 1 by norm_cast; linarith ) ) ]
/-
proved below, placeholder for proof text
`bMass` is bounded by the crude bound `1/(n log n)` using the
    von Mangoldt divisor sum identity `∑_{q | n} Λ(q) = log n`.
-/
lemma bMass_le_crude (X Y n : ℕ) (hn : 2 ≤ n) :
    bMass X Y n ≤ 1 / ((n : ℝ) * Real.log n) := by
  unfold bMass;
  split_ifs <;> norm_num;
  · linarith;
  · -- By definition of von Mangoldt function, we know that $\sum_{q \mid n} \Lambda(q) = \log n$.
    have h_von_mangoldt : ∑ q ∈ n.divisors, Λ' q = Real.log n := by
      convert ArithmeticFunction.vonMangoldt_sum;
    -- Since these are the only terms in the sum, we can simplify the inequality.
    have h_simplify : (∑ q ∈ n.divisors.filter (fun q => 0 < q ∧ q < Y), Λ' q) + (∑ q ∈ n.divisors.filter (fun q => Y ≤ q ∧ n / q < X), Λ' q) ≤ ∑ q ∈ n.divisors, Λ' q := by
      rw [ ← Finset.sum_union ];
      · exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) ) fun _ _ _ => by unfold Λ'; aesop;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
    convert mul_le_mul_of_nonneg_left h_simplify ( show 0 ≤ ( Real.log n ^ 2 ) ⁻¹ * ( n : ℝ ) ⁻¹ by positivity ) using 1 ; ring;
    grind
-- proved below, placeholder for proof text
/-! ## Core lemmas (require deep number-theoretic estimates) -/
/-- **Analytic bound on boundary mass** (requires Mertens' theorem).
For `Y ≥ 2`, there exists `C > 0` such that for all `X ≥ 2` and `N`:
  `∑_{n ∈ [X, N]} bMass(X, Y, n) ≤ 1 + C / log X`.
The proof splits `∑ bMass` into:
- Small prime powers: `∑_{q < Y} (Λ(q)/q) · ∑_{m ≥ X/q} 1/(m · (log(mq))²) = O_Y(1/log X)`
- Entry nodes: `∑_{m < X} (1/m) · ∑_{q ≥ max(Y, X/m)} Λ(q)/(q · (log(mq))²) = 1 + O(1/log X)`
The entry part uses the tail estimate
  `∑_{q ≥ y} Λ(q)/(q · (log(mq))²) = 1/log(my) + O(1/(log(my))²)`
and the harmonic sum `∑_{m < X} 1/m = log X + O(1)`.
Both require Mertens-type estimates that are not yet in Mathlib. -/
lemma bMass_partial_sum_bound (Y : ℕ) (hY : 2 ≤ Y) :
    ∃ C : ℝ, C > 0 ∧ ∀ (X : ℕ), 2 ≤ X → ∀ (N : ℕ),
    (Finset.Icc X N).sum (fun n => bMass X Y n) ≤ 1 + C / Real.log X := by
  sorry
/-- **Finite primitive set bound** (requires divisor recursion argument).
For finite primitive `F ⊆ [X, ∞)` with `X ≥ 2`, `Y ≥ 2`:
  `∑_{a ∈ F} 1/(a · log a) ≤ ∑_{n ∈ [X, sup F]} bMass(X, Y, n)`
The proof defines "hit weights" `hit a n` for divisors `n | a` with `X ≤ n ≤ a`:
- `hit a a = 1`
- `hit a n = ∑_{q | (a/n), q ≥ Y} p(Y, n, q) · hit a (n·q)` for `n < a`
Then shows `W a := ∑_{n | a, X ≤ n} bMass(X,Y,n) · hit(a,n) = 1/(a · log a)`
by strong induction using the von Mangoldt identity `∑_{q | a} Λ(q) = log a`.
Next, defines `hitF n = ∑_{a ∈ F, n | a} hit a n` and proves `hitF ≤ 1`
by reverse induction using the transition mass bound `R_Y(m) ≤ 1`.
The bound then follows from:
  `∑_{a ∈ F} 1/(a log a) = ∑_{a ∈ F} W a = ∑ bMass · hitF ≤ ∑ bMass`.
This requires the transition mass bound, which in turn requires the
tail estimate and Mertens-type results. -/
lemma finite_primitive_sum_le_bMass (X Y : ℕ) (hX : 2 ≤ X) (hY : 2 ≤ Y)
    (F : Finset ℕ) (hF : ∀ a ∈ F, X ≤ a)
    (hprim : IsPrimitiveNat (F : Set ℕ)) :
    F.sum (fun a => 1 / ((a : ℝ) * Real.log a)) ≤
    (Finset.Icc X (F.sup _root_.id)).sum (fun n => bMass X Y n) := by
  sorry

/-
The tsum over a set A is bounded if all finite subsums are bounded.
Uses the fact that for non-negative summable functions, the tsum is
the supremum of finite partial sums.
-/
lemma tsum_le_of_finite_sums_le {A : Set ℕ} (hA : A ⊆ Set.Ici 2) (B : ℝ)
    (hB : ∀ F : Finset ℕ, ↑F ⊆ A →
      F.sum (fun a => 1 / ((a : ℝ) * Real.log a)) ≤ B) :
    ∑' (a : A), (1 / ((a.val : ℝ).log * (a.val : ℝ))) ≤ B := by
  have h_inf_sum_le : Summable (fun a : A => 1 / ((a : ℝ) * Real.log a)) := by
    refine' summable_of_sum_le _ _;
    exact B;
    · exact fun x => one_div_nonneg.2 <| mul_nonneg ( Nat.cast_nonneg _ ) <| Real.log_nonneg <| Nat.one_le_cast.2 <| by linarith [ Set.mem_Ici.1 <| hA x.2 ] ;
    · intro u; specialize hB ( u.image Subtype.val ) ; aesop;
  simp_all +decide [ mul_comm ];
  refine' le_of_tendsto_of_tendsto' ( h_inf_sum_le.hasSum ) tendsto_const_nhds _;
  intro F; convert hB ( F.image Subtype.val ) _ using 1;
  · rw [ Finset.sum_image ] ; aesop;
  · aesop_cat
-- proved below, placeholder for proof text
/-! ## Main quantitative bound -/
/-- The main quantitative bound: for primitive `A ⊆ [X, ∞)` with `X ≥ 2`,
`∑' (a : A), 1/(log a · a) ≤ 1 + C / log X`. -/
theorem primitive_set_quantitative_bound' :
    ∃ C : ℝ, C > 0 ∧ ∀ (X : ℕ), 2 ≤ X →
    ∀ (A : Set ℕ), A ⊆ Set.Ici X → IsPrimitive A →
    ∑' (a : A), (1 / ((a.val : ℝ).log * (a.val : ℝ))) ≤ 1 + C / Real.log X := by
  obtain ⟨C, hCpos, hbnd⟩ := bMass_partial_sum_bound 2 le_rfl
  refine ⟨C, hCpos, fun X hX A hA hprim => ?_⟩
  have hA2 : A ⊆ Set.Ici 2 := fun a ha => le_trans hX (hA ha)
  apply tsum_le_of_finite_sums_le hA2
  intro F hFA
  have hFX : ∀ a ∈ F, X ≤ a := fun a ha => hA (hFA ha)
  have hFprim : IsPrimitiveNat (F : Set ℕ) := by
    intro x hx y hy hxy
    exact isPrimitive_implies_nat hprim x (hFA hx) y (hFA hy) hxy
  calc F.sum (fun a => 1 / ((a : ℝ) * Real.log a))
      ≤ (Finset.Icc X (F.sup _root_.id)).sum (fun n => bMass X 2 n) :=
        finite_primitive_sum_le_bMass X 2 hX le_rfl F hFX hFprim
    _ ≤ 1 + C / Real.log X := hbnd X hX (F.sup _root_.id)
end

lemma primitive_set_quantitative_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ (X : ℕ), 2 ≤ X →
    ∀ (A : Set ℕ), A ⊆ Set.Ici X → IsPrimitive A →
    ∑' (a : A), (1 / ((a.val : ℝ).log * (a.val : ℝ))) < 1 + C / Real.log X := by
  obtain ⟨C, hC, hC'⟩ := primitive_set_quantitative_bound'
  use C + 1
  constructor
  · linarith
  · intro X hX A hA hA'
    specialize hC' X hX A hA hA'
    apply lt_of_le_of_lt hC'
    rw [add_lt_add_iff_left, div_lt_div_iff_of_pos_right]
    · linarith
    · rify at hX
      rw [Real.log_pos_iff]
      all_goals grind



/-! ### Deducing the corrected `1 + o(1)` statement -/
private lemma tendsto_const_div_log_atTop (C : ℝ) :
    Tendsto (fun x : ℕ => C / Real.log (max 2 (x : ℝ))) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp <|
    Filter.tendsto_atTop_atTop.mpr fun x => ⟨⌈x⌉₊ + 1, fun n hn =>
      le_trans (le_of_lt <| Nat.lt_of_ceil_lt hn) <| le_max_right _ _⟩
private lemma isPrimitive_singleton_one
    (A : Set ℕ) (_hA : A ⊆ Set.Ici 1) (hprim : IsPrimitive A) (h1 : (1 : ℕ) ∈ A) :
    A = {1} := by
  ext x
  constructor <;> intro hx <;> contrapose! hprim
  · simp +decide [IsPrimitive]
    refine' ⟨1, h1, x, hx, one_dvd _, _⟩
    rintro ⟨_ | _ | u⟩ <;> aesop
  · aesop

/--
Is it true that, for any $x$, if $A\subset [x,\infty)$ is a primitive set of integers (so that no distinct elements of $A$ divide each other) then\[\sum_{a\in A}\frac{1}{a\log a}&#60; 1+o(1),\]where the $o(1)$ term $\to 0$ as $x\to \infty$?
-/
theorem erdos_1196 :
     ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
     ∀ (x : ℕ), x > 0 → ∀ A ⊆ Set.Ici x, IsPrimitive A →
       ∑' (a : A), (1 / ((a.val : ℝ).log * (a.val : ℝ))) < 1 + o x := by
  obtain ⟨C, hCpos, hbound⟩ := primitive_set_quantitative_bound
  refine ⟨fun x => C / Real.log (max 2 (x : ℝ)), ?_, ?_⟩
  · rw [show (1 : ℕ → ℝ) = fun _ => (1 : ℝ) from rfl]
    rw [Asymptotics.isLittleO_one_iff]
    exact tendsto_const_div_log_atTop C
  · intro x hx A hA hprim
    by_cases hx2 : 2 ≤ x
    · have hlog_eq : Real.log (max 2 (x : ℝ)) = Real.log (x : ℝ) := by
        congr 1; exact max_eq_right (by exact_mod_cast hx2)
      simp only [hlog_eq]
      exact hbound x hx2 A hA hprim
    · have hx1 : x = 1 := by omega
      subst hx1
      by_cases h1 : (1 : ℕ) ∈ A
      · have hA1 := isPrimitive_singleton_one A hA hprim h1
        rw [hA1]; simp [Real.log_one]; positivity
      · have hA2 : A ⊆ Set.Ici 2 := by
          intro a ha
          have h := hA ha; simp [Set.mem_Ici] at h ⊢
          have : a ≠ 1 := fun heq => by subst heq; exact h1 ha
          omega
        have hbound2 := hbound 2 le_rfl A hA2 hprim
        show ∑' (a : ↑A), 1 / (Real.log ↑↑a * ↑↑a) < 1 + C / Real.log (max 2 ((1 : ℕ) : ℝ))
        simp only [Nat.cast_one, max_eq_left (by norm_num : (2 : ℝ) ≥ 1)]
        exact hbound2

end Erdos1196
