/- GID: D5/S3/Combinatorics/AdditiveCodes/AdditiveCodesBinarySeed
   generality: G
   mirror-B: D5/B/S3/Combinatorics/AdditiveCodes/AdditiveCodesBinarySeed
   mirror-E: none(waiver:binary-seed-obstruction)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.FiniteDimensional.Lemmas]
   utility: none
   digest: Parity and support obstruct three-dimensional binary seed subspaces. -/

import D5.S3.Combinatorics.AdditiveCodes.AdditiveExtensionDefs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000
set_option maxSynthPendingDepth 1000

namespace D5.S3.Combinatorics.AdditiveCodes

/-- The eight points used for the binary seed. -/
def binarySeedPoints : Finset (Fin 6 → ZMod 2) :=
  insert 0 (insert (fun _ => 1) (Finset.univ.image (fun i => Pi.single i 1)))

/-- The difference set of the seed, using subtraction in the ambient vector space. -/
def binarySeedDifferences : Finset (Fin 6 → ZMod 2) :=
  (binarySeedPoints ×ˢ binarySeedPoints).image (fun p => p.1 - p.2)

/-- The linear three-dimensional shift space for the binary seed tiling. -/
def binarySeedShift : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun a := ![a 0, a 0 + a 1, a 1 + a 2, a 0 + a 2, a 1, a 2]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp <;> ring

/-- Every subspace contained in the seed difference set has dimension at most two.
The even part is supported on the edges of a triangle. The odd part is a coset of
that even part; mixed unit and complementary-unit supports cannot occur in a
four-element coset whose sum is zero. -/
theorem binarySeedObstruction (W : Submodule (ZMod 2) (Fin 6 → ZMod 2))
    (hW : ∀ x ∈ W, x ∈ binarySeedDifferences) : Module.finrank (ZMod 2) W ≤ 2 := by
  let unit : Fin 6 → (Fin 6 → ZMod 2) := fun i => Pi.single i 1
  let ones : Fin 6 → ZMod 2 := fun _ => 1
  let parity : (Fin 6 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => ∑ i, x i
      map_add' := fun x y => Finset.sum_add_distrib
      map_smul' := fun c x => by simp [Finset.mul_sum] }
  -- These local checks classify supports, rather than enumerating subspaces.
  have even_shape : ∀ x : Fin 6 → ZMod 2,
      x ∈ binarySeedDifferences → parity x = 0 → x ≠ 0 →
      x = ones ∨ ∃ i j : Fin 6, i ≠ j ∧ x = unit i + unit j := by
    decide
  have odd_shape : ∀ x : Fin 6 → ZMod 2,
      x ∈ binarySeedDifferences → parity x ≠ 0 →
      ∃ i : Fin 6, x = unit i ∨ x = ones + unit i := by
    decide
  have complement_edge : ∀ i j : Fin 6, i ≠ j →
      ones + (unit i + unit j) ∉ binarySeedDifferences := by decide
  have triangle : ∀ i j a b : Fin 6, i ≠ j → a ≠ b →
      unit i + unit j ≠ unit a + unit b →
      (unit i + unit j) + (unit a + unit b) ∈ binarySeedDifferences →
      ∃ s t u : Fin 6, s ≠ t ∧ s ≠ u ∧ t ≠ u ∧
        unit i + unit j = unit s + unit t ∧
        unit a + unit b = unit s + unit u := by decide
  have triangle_edges : ∀ s t u i j : Fin 6,
      s ≠ t → s ≠ u → t ≠ u → i ≠ j →
      (unit s + unit t) + (unit i + unit j) ∈ binarySeedDifferences →
      (unit s + unit u) + (unit i + unit j) ∈ binarySeedDifferences →
      (unit t + unit u) + (unit i + unit j) ∈ binarySeedDifferences →
      unit i + unit j = unit s + unit t ∨
      unit i + unit j = unit s + unit u ∨
      unit i + unit j = unit t + unit u := by decide
  have odd_coset : ∀ i j l n : Fin 6, ∀ a b c d : Bool,
      let pick := fun (z : Fin 6) (t : Bool) => if t then ones + unit z else unit z
      let A := pick i a; let B := pick j b; let C := pick l c; let D := pick n d
      A ≠ B → A ≠ C → A ≠ D → B ≠ C → B ≠ D → C ≠ D →
      A + B ∈ binarySeedDifferences → A + C ∈ binarySeedDifferences →
      A + D ∈ binarySeedDifferences → B + C ∈ binarySeedDifferences →
      B + D ∈ binarySeedDifferences → C + D ∈ binarySeedDifferences →
      A + B + C + D ≠ 0 := by
    intro i j l n a b c d
    cases a <;> cases b <;> cases c <;> cases d
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte]
      revert i j l n
      decide
  classical
  by_contra hdim
  have hd : 3 ≤ Module.finrank (ZMod 2) W := by omega
  obtain ⟨g, hg⟩ := exists_linearIndependent_of_le_finrank hd
  let f := Fintype.linearCombination (ZMod 2) g
  have hf := hg.fintypeLinearCombination_injective
  have coeffs : Function.Injective (fun a : Fin 3 → ZMod 2 => (f a : Fin 6 → ZMod 2)) :=
    Subtype.coe_injective.comp hf
  have char : ∀ x : Fin 6 → ZMod 2, x + x = 0 := by
    intro x; ext i; exact CharTwo.add_self_eq_zero (x i)
  by_cases he : ∀ x ∈ W, parity x = 0
  · have not_ones : ones ∉ W := by
      intro ho
      have gn0 : (g 0 : Fin 6 → ZMod 2) ≠ 0 := by
        intro h; exact hg.ne_zero 0 (Subtype.ext h)
      have gn1 : (g 1 : Fin 6 → ZMod 2) ≠ 0 := by
        intro h; exact hg.ne_zero 1 (Subtype.ext h)
      have gne : (g 0 : Fin 6 → ZMod 2) ≠ g 1 := by
        intro h; have := hg.injective (Subtype.ext h); norm_num at this
      obtain ⟨x, hx, hx0, hxo⟩ : ∃ x ∈ W, x ≠ 0 ∧ x ≠ ones := by
        by_cases ho0 : (g 0 : Fin 6 → ZMod 2) = ones
        · exact ⟨g 1, (g 1).property, gn1, fun h => gne (ho0.trans h.symm)⟩
        · exact ⟨g 0, (g 0).property, gn0, ho0⟩
      obtain hxone | ⟨i, j, hij, hxij⟩ := even_shape x (hW x hx) (he x hx) hx0
      · exact hxo hxone
      · exact complement_edge i j hij (hxij ▸ hW (ones + x) (W.add_mem ho hx))
    have shape : ∀ x ∈ W, x ≠ 0 →
        ∃ i j : Fin 6, i ≠ j ∧ x = unit i + unit j := by
      intro x hx hx0
      rcases even_shape x (hW x hx) (he x hx) hx0 with h | h
      · exact False.elim (not_ones (h ▸ hx))
      · exact h
    let a : Fin 3 → ZMod 2 := ![1, 0, 0]
    let b : Fin 3 → ZMod 2 := ![0, 1, 0]
    let c : Fin 3 → ZMod 2 := ![0, 0, 1]
    have fa0 : (f a : Fin 6 → ZMod 2) ≠ 0 := by
      intro h; have h' := coeffs (a₁ := a) (a₂ := 0) (by simpa using h)
      have := congrFun h' 0; norm_num [a] at this
    have fb0 : (f b : Fin 6 → ZMod 2) ≠ 0 := by
      intro h; have h' := coeffs (a₁ := b) (a₂ := 0) (by simpa using h)
      have := congrFun h' 1; norm_num [b] at this
    have fc0 : (f c : Fin 6 → ZMod 2) ≠ 0 := by
      intro h; have h' := coeffs (a₁ := c) (a₂ := 0) (by simpa using h)
      have := congrFun h' 2
      change (1 : ZMod 2) = 0 at this
      exact one_ne_zero this
    have fab : (f a : Fin 6 → ZMod 2) ≠ f b := by
      intro h; have := congrFun (coeffs h) 0; norm_num [a, b] at this
    obtain ⟨i, j, hij, ha⟩ := shape (f a) (f a).property fa0
    obtain ⟨l, n, hln, hb⟩ := shape (f b) (f b).property fb0
    obtain ⟨s, t, u, hst, hsu, htu, hab, hbb⟩ :=
      triangle i j l n hij hln (ha ▸ hb ▸ fab)
        (ha ▸ hb ▸ hW (f a + f b) (W.add_mem (f a).property (f b).property))
    have has : (f a : Fin 6 → ZMod 2) = unit s + unit t := ha.trans hab
    have hbs : (f b : Fin 6 → ZMod 2) = unit s + unit u := hb.trans hbb
    have habs : (f a + f b : Fin 6 → ZMod 2) = unit t + unit u := by
      rw [has, hbs]; have := char (unit s); abel_nf at this ⊢; simp only [this, zero_add]
    obtain ⟨v, w, hvw, hc⟩ := shape (f c) (f c).property fc0
    have hwac := hW (f a + f c) (W.add_mem (f a).property (f c).property)
    have hwbc := hW (f b + f c) (W.add_mem (f b).property (f c).property)
    have hwabc := hW (f a + f b + f c)
      (W.add_mem (W.add_mem (f a).property (f b).property) (f c).property)
    rcases triangle_edges s t u v w hst hsu htu hvw
      (has ▸ hc ▸ hwac) (hbs ▸ hc ▸ hwbc) (habs ▸ hc ▸ hwabc) with h | h | h
    · have := congrFun (coeffs (hc.trans h |>.trans has.symm)) 2
      change (1 : ZMod 2) = 0 at this; exact one_ne_zero this
    · have := congrFun (coeffs (hc.trans h |>.trans hbs.symm)) 2
      change (1 : ZMod 2) = 0 at this; exact one_ne_zero this
    · have hh : (f c : Fin 6 → ZMod 2) = f (a + b) := by
        rw [map_add]; exact (hc.trans h).trans habs.symm
      have := congrFun (coeffs hh) 2; change (1 : ZMod 2) = 0 at this; exact one_ne_zero this
  · push_neg at he
    obtain ⟨x, hx, hp⟩ := he
    let E := LinearMap.ker (parity.comp W.subtype)
    have hEd : 2 ≤ Module.finrank (ZMod 2) E := by
      have hnull := (parity.comp W.subtype).finrank_range_add_finrank_ker
      have hbound := (parity.comp W.subtype).range.finrank_le
      have hfield : Module.finrank (ZMod 2) (ZMod 2) = 1 := Module.finrank_self _
      dsimp [E]; omega
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hEd
    let q := Fintype.linearCombination (ZMod 2) v
    have hq := hv.fintypeLinearCombination_injective
    let a : Fin 2 → ZMod 2 := ![1, 0]
    let b : Fin 2 → ZMod 2 := ![0, 1]
    let u : Fin 6 → ZMod 2 := ((q a : E) : W)
    let w : Fin 6 → ZMod 2 := ((q b : E) : W)
    have huW : u ∈ W := (((q a : E) : W)).property
    have hwW : w ∈ W := (((q b : E) : W)).property
    have hu : parity u = 0 := (q a).property
    have hw : parity w = 0 := (q b).property
    have hinj : Function.Injective (fun z : Fin 2 → ZMod 2 =>
        ((((q z : E) : W) : Fin 6 → ZMod 2))) :=
      Subtype.coe_injective.comp (Subtype.coe_injective.comp hq)
    have hu0 : u ≠ 0 := by
      intro h; have hh := hinj (a₁ := a) (a₂ := 0) (by simpa [u] using h)
      have := congrFun hh 0; norm_num [a] at this
    have hw0 : w ≠ 0 := by
      intro h; have hh := hinj (a₁ := b) (a₂ := 0) (by simpa [w] using h)
      have := congrFun hh 1; norm_num [b] at this
    have huw : u ≠ w := by
      intro h; have := congrFun (hinj h) 0; norm_num [a, b] at this
    have odd : ∀ z ∈ W, parity z ≠ 0 →
        ∃ i : Fin 6, z = unit i ∨ z = ones + unit i := by
      intro z hz hzp; exact odd_shape z (hW z hz) hzp
    obtain ⟨i, hi⟩ := odd x hx hp
    obtain ⟨j, hj⟩ := odd (x + u) (W.add_mem hx huW) (by simpa [hu] using hp)
    obtain ⟨l, hl⟩ := odd (x + w) (W.add_mem hx hwW) (by simpa [hw] using hp)
    obtain ⟨n, hn⟩ := odd (x + u + w)
      (W.add_mem (W.add_mem hx huW) hwW) (by simpa [hu, hw] using hp)
    -- Four odd elements of a two-dimensional even-kernel coset have sum zero.
    -- Mixed supports force a forbidden weight-four pair; equal-type distinct
    -- supports have a nonzero sum. Only six-coordinate support checks are used.
    have hz : x + (x + u) + (x + w) + (x + u + w) = 0 := by
      ext i
      change x i + (x i + u i) + (x i + w i) + (x i + u i + w i) = 0
      calc
        _ = (2 : ZMod 2) * (x i + x i + u i + w i) := by ring
        _ = 0 := by
          have h2 : (2 : ZMod 2) = 0 := by decide
          rw [h2, zero_mul]
    obtain ⟨ti, hti⟩ : ∃ ti : Bool, x = if ti then ones + unit i else unit i := by
      rcases hi with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨tj, htj⟩ : ∃ tj : Bool, x + u = if tj then ones + unit j else unit j := by
      rcases hj with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨tl, htl⟩ : ∃ tl : Bool, x + w = if tl then ones + unit l else unit l := by
      rcases hl with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨tn, htn⟩ : ∃ tn : Bool,
        x + u + w = if tn then ones + unit n else unit n := by
      rcases hn with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    have contra := odd_coset i j l n ti tj tl tn
    dsimp only at contra
    rw [← hti, ← htj, ← htl, ← htn] at contra
    have hne1 : x ≠ x + u := by simpa using hu0
    have hne2 : x ≠ x + w := by simpa using hw0
    have hne3 : x ≠ x + u + w := by
      intro h
      have huv : u = w := by
        have hh : u + w = 0 := by simpa [add_assoc] using h.symm
        have hh' := congrArg (fun z => z + w) hh
        simpa [add_assoc, char w] using hh'
      exact huw huv
    have hne4 : x + u ≠ x + w := by simpa using huw
    have hne5 : x + u ≠ x + u + w := by simpa using hw0
    have hne6 : x + w ≠ x + u + w := by
      simpa [add_right_comm x u w] using hu0
    have hmem : ∀ a ∈ W, ∀ b ∈ W, a + b ∈ binarySeedDifferences :=
      fun a ha b hb => hW (a + b) (W.add_mem ha hb)
    exact contra hne1 hne2 hne3 hne4 hne5 hne6
      (hmem x hx (x + u) (W.add_mem hx huW))
      (hmem x hx (x + w) (W.add_mem hx hwW))
      (hmem x hx (x + u + w) (W.add_mem (W.add_mem hx huW) hwW))
      (hmem (x + u) (W.add_mem hx huW) (x + w) (W.add_mem hx hwW))
      (hmem (x + u) (W.add_mem hx huW) (x + u + w)
        (W.add_mem (W.add_mem hx huW) hwW))
      (hmem (x + w) (W.add_mem hx hwW) (x + u + w)
        (W.add_mem (W.add_mem hx huW) hwW)) hz

end D5.S3.Combinatorics.AdditiveCodes
