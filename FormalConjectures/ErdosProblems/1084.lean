/-
Copyright 2025 The Formal Conjectures Authors.

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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1084

*References:*
- [erdosproblems.com/1084](https://www.erdosproblems.com/1084)
- [Ha74b] Harborth, Heiko, Lösung zu Problem 664A. Elem. Math. (1974), 14--15.

Let `f_2(n)` be the maximum number of pairs of points at distance exactly `1`
among any set of `n` points in `ℝ²`, under the condition that all pairwise
distances are at least `1`.

Estimate the growth of `f_2(n)`.

Status: open.
-/

@[expose] public section

open Finset Filter Metric Real
open scoped EuclideanGeometry

namespace Erdos1084
variable {n : ℕ}

/-- The maximal number of pairs of points which are distance 1 apart that a set of `n` 1-separated
points in `ℝ^d` make. -/
noncomputable def f (d n : ℕ) : ℕ :=
  ⨆ (s : Finset (ℝ^ d)) (_ : s.card = n) (_ : IsSeparated' 1 (s : Set (ℝ^ d))), unitDistNum s

-- TODO: Add erdos_1084.

set_option linter.style.formal_proof_palomar false in
/-- It is easy to check that $f_1(n) = n - 1$. -/
@[category research solved, AMS 52, formal_proof using formal_conjectures at "https://github.com/Sanexxxx777/formal-conjectures/blob/9e4f3845be122a8fa3190d38543ebdd0a6f25605/FormalConjectures/ErdosProblems/1084.lean#L232"]
theorem erdos_1084.variants.upper_d1 : f 1 n = n - 1 := by
  sorry

/-- `x` comes before `y` in the lexicographic order of coordinates. -/
def LexBefore (x y : ℝ^ 2) : Prop := x 0 < y 0 ∨ (x 0 = y 0 ∧ x 1 < y 1)

/-- Two distinct points are comparable in the lexicographic order. -/
@[category API, AMS 52]
lemma lexBefore_or {x y : ℝ^ 2} (h : x ≠ y) : LexBefore x y ∨ LexBefore y x := by
  unfold LexBefore
  rcases lt_trichotomy (x 0) (y 0) with h0 | h0 | h0
  · exact Or.inl (Or.inl h0)
  · rcases lt_trichotomy (x 1) (y 1) with h1 | h1 | h1
    · exact Or.inl (Or.inr ⟨h0, h1⟩)
    · exact absurd (by ext i; fin_cases i <;> assumption) h
    · exact Or.inr (Or.inr ⟨h0.symm, h1⟩)
  · exact Or.inr (Or.inl h0)

/-- Two unit complex numbers whose arguments differ by less than `π / 3` are at distance
less than `1`. -/
@[category API, AMS 52]
lemma norm_sub_lt_one {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (h : |z.arg - w.arg| < π / 3) : ‖z - w‖ < 1 := by
  have ez : z = Complex.exp (z.arg * Complex.I) := by
    simpa [hz] using (Complex.norm_mul_exp_arg_mul_I z).symm
  have ew : w = Complex.exp (w.arg * Complex.I) := by
    simpa [hw] using (Complex.norm_mul_exp_arg_mul_I w).symm
  have key : z - w = Complex.exp (w.arg * Complex.I) *
      (Complex.exp (Complex.I * ↑(z.arg - w.arg)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    conv_lhs => rw [ez, ew]
    congr 2
    push_cast
    ring
  rw [key, norm_mul, Complex.norm_exp_I_mul_ofReal_sub_one, Complex.norm_exp_ofReal_mul_I,
    one_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  have hpi := Real.pi_pos
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  have : |Real.sin ((z.arg - w.arg) / 2)| < 1 / 2 := by
    rw [abs_lt]
    constructor
    · have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (x := -(π / 6)) (y := (z.arg - w.arg) / 2)
        (by linarith) (by linarith) (by linarith)
      rwa [Real.sin_neg, Real.sin_pi_div_six] at this
    · have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (x := (z.arg - w.arg) / 2) (y := π / 6)
        (by linarith) (by linarith) (by linarith)
      rwa [Real.sin_pi_div_six] at this
  linarith

/-- Each point of a `1`-separated set has at most three unit neighbours after it in the
lexicographic order. -/
@[category API, AMS 52]
lemma card_after_le_three {s : Finset (ℝ^ 2)} (hs : IsSeparated' 1 (s : Set (ℝ^ 2)))
    (x : ℝ^ 2) [DecidablePred fun y => dist x y = 1 ∧ LexBefore x y] :
    #{y ∈ s | dist x y = 1 ∧ LexBefore x y} ≤ 3 := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  let θ : ℝ^ 2 → ℝ := fun y => (e (y - x)).arg
  have hpi := Real.pi_pos
  have hmem : ∀ y ∈ ({y ∈ s | dist x y = 1 ∧ LexBefore x y} : Finset _),
      ‖e (y - x)‖ = 1 ∧ -(π / 2) < θ y ∧ θ y ≤ π / 2 := by
    intro y hy
    obtain ⟨-, hd, hlex⟩ := mem_filter.mp hy
    have hre : (e (y - x)).re = y 0 - x 0 := by
      simp [e, Complex.orthonormalBasisOneI_repr_symm_apply]
    have him : (e (y - x)).im = y 1 - x 1 := by
      simp [e, Complex.orthonormalBasisOneI_repr_symm_apply]
    refine ⟨by rw [LinearIsometryEquiv.norm_map, ← dist_eq_norm, dist_comm, hd],
      Complex.neg_pi_div_two_lt_arg_iff.mpr ?_, Complex.arg_le_pi_div_two_iff.mpr ?_⟩
    · rw [hre, him]
      rcases hlex with h | ⟨-, h⟩
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rw [hre]
      rcases hlex with h | ⟨h, -⟩ <;> exact Or.inl (by linarith)
  calc #{y ∈ s | dist x y = 1 ∧ LexBefore x y} ≤ #(Ico (0 : ℤ) 3) := by
        refine card_le_card_of_injOn (fun y => ⌊(π / 2 - θ y) / (π / 3)⌋)
          (fun y hy => ?_) (fun y hy y' hy' hb => ?_)
        · obtain ⟨-, h1, h2⟩ := hmem y hy
          rw [coe_Ico, Set.mem_Ico, Int.floor_nonneg, Int.floor_lt, div_lt_iff₀ (by linarith)]
          push_cast
          exact ⟨div_nonneg (by linarith) (by linarith), by linarith⟩
        · by_contra hne
          have hsep : 1 ≤ edist y y' := hs (mem_filter.mp hy).1 (mem_filter.mp hy').1 hne
          rw [edist_dist, ENNReal.one_le_ofReal] at hsep
          have hlt := Int.abs_sub_lt_one_of_floor_eq_floor hb
          rw [← sub_div, abs_div, abs_of_pos (by linarith : 0 < π / 3), div_lt_one (by linarith),
            sub_sub_sub_cancel_left, abs_sub_comm] at hlt
          have := norm_sub_lt_one (hmem y hy).1 (hmem y' hy').1 hlt
          rw [← map_sub, LinearIsometryEquiv.norm_map, sub_sub_sub_cancel_right,
            ← dist_eq_norm] at this
          linarith
    _ = 3 := by simp

open scoped Classical in
/-- Each unit-distance pair is counted once, by its lexicographically ordered representative. -/
@[category API, AMS 52]
lemma unitDistNum_le_card_after (s : Finset (ℝ^ 2)) :
    unitDistNum s ≤ #{p ∈ s ×ˢ s | dist p.1 p.2 = 1 ∧ LexBefore p.1 p.2} := by
  refine card_le_card_of_surjOn (fun p => s(p.1, p.2)) fun q hq => ?_
  obtain ⟨hqs, hqd⟩ := mem_filter.mp hq
  have hq' : s(q.out.1, q.out.2) = q := Quot.out_eq q
  generalize q.out.1 = a, q.out.2 = b at hq' hqd
  subst hq'
  obtain ⟨ha, hb⟩ := mk_mem_sym2_iff.mp hqs
  have hne : a ≠ b := fun h => by simp [h] at hqd
  rcases lexBefore_or hne with h | h
  · exact ⟨(a, b), by simp [ha, hb, hqd, h], rfl⟩
  · exact ⟨(b, a), by simp [ha, hb, dist_comm, hqd, h], Sym2.eq_swap⟩

open scoped Classical in
/-- A nonempty `1`-separated set of `n` points has at most `3 (n - 1)` ordered unit pairs. -/
@[category API, AMS 52]
lemma card_after_le {s : Finset (ℝ^ 2)} (hs : IsSeparated' 1 (s : Set (ℝ^ 2)))
    (hne : s.Nonempty) :
    #{p ∈ s ×ˢ s | dist p.1 p.2 = 1 ∧ LexBefore p.1 p.2} ≤ 3 * (#s - 1) := by
  obtain ⟨a, ha, hamax⟩ := s.exists_max_image (fun x => x 0) hne
  obtain ⟨m, hm, hmmax⟩ := ({x ∈ s | x 0 = a 0} : Finset _).exists_max_image (fun x => x 1)
    ⟨a, mem_filter.mpr ⟨ha, rfl⟩⟩
  obtain ⟨hms, hm0⟩ := mem_filter.mp hm
  have hlast : #{y ∈ s | dist m y = 1 ∧ LexBefore m y} = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro y hy ⟨-, h | ⟨h0, h1⟩⟩
    · linarith [hamax y hy]
    · linarith [hmmax y (mem_filter.mpr ⟨hy, h0.symm.trans hm0⟩)]
  rw [card_filter, sum_product, ← add_sum_erase s _ hms]
  simp only [← card_filter]
  rw [hlast, zero_add, ← card_erase_of_mem hms, mul_comm, ← smul_eq_mul]
  exact sum_le_card_nsmul _ _ _ fun x _ => card_after_le_three hs x

/-- It is easy to check that $f_2(n) < 3n$. -/
@[category research solved, AMS 52]
theorem erdos_1084.variants.easy_upper_d2 (hn : n ≠ 0) : f 2 n < 3 * n := by
  have : f 2 n ≤ 3 * (n - 1) := by
    refine ciSup_le' fun s => ciSup_le' fun hs => ciSup_le' fun hsep => ?_
    subst hs
    exact (unitDistNum_le_card_after s).trans
      (card_after_le hsep (card_pos.mp (Nat.pos_of_ne_zero hn)))
  omega

/-- Erdős showed that there is some constant $c > 0$ such that $f_2(n) < 3n - c n^{1/2}$. -/
@[category research solved, AMS 52]
theorem erdos_1084.variants.upper_d2 : ∃ c > (0 : ℝ), ∀ n > 0, f 2 n < 3 * n - c * sqrt n := by
  sorry

/-- Erdős conjectured that the triangular lattice is best possible in 2D, in particular that
$f_2(3n^2 + 3n + 1) = 9n^2 + 3n$. Harborth [Ha74b] proved this, and more generally
$f_2(n) = \lfloor 3n - \sqrt{12n - 3} \rfloor$ for all $n \geq 2$.

Note: in [Er75f] is read $9n^2 + 6n$, but this seems to be a typo.
-/
@[category research solved, AMS 52]
theorem erdos_1084.variants.triangular_optimal_d2 : f 2 (3 * n ^ 2 + 3 * n + 1) = 9 * n ^ 2 + 3 * n := by
  sorry

/-- Erdős claims the existence of two constants $c_1, c_2 > 0$
such that $6n - c_1 n^{2/3} ≤ f_3(n) \le 6n - c_2 n^{2/3}$. -/
@[category research solved, AMS 52]
theorem erdos_1084.variants.upper_lower_d3 :
    ∃ c₁ : ℝ, ∃ c₂ > (0 : ℝ), ∀ᶠ n in atTop,
      6 * n - c₁ * n ^ (2 / 3 : ℝ) ≤ f 3 n ∧ f 3 n ≤ 6 * n - c₂ * n ^ (2 / 3 : ℝ) := by
  sorry

end Erdos1084
