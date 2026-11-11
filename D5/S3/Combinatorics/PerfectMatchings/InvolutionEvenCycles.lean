/- GID: D5/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Basic]
   utility: none
   digest: Rooted interlacing of ordered perfect matchings and even permutation cycles. -/

import D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
import D5.S3.Zeros.Convolution.PerfectMatchingCount

/-! Ordered matching edges interlace from the least vertex of each full component. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles

open Equiv
open D5.S3.Zeros.Convolution.PerfectMatchingCount
open InvolutionOrbitSplit

variable {X : Type*} [Fintype X] [LinearOrder X]

omit [Fintype X] [LinearOrder X] in
private theorem connected_comm (s t : Perm X) (x y : X) :
    Connected s t x y ↔ Connected t s x y := by
  constructor <;> intro h <;> induction h with
  | refl => exact .refl
  | tail _ hab ih => exact ih.tail hab.symm

omit [Fintype X] [LinearOrder X] in
private theorem connected_symm (s t : FixedPointFreeInvolution X) {x y : X}
    (h : Connected s.val t.val x y) : Connected s.val t.val y x := by
  induction h with
  | refl => exact .refl
  | @tail a b h hab ih =>
    apply Relation.ReflTransGen.trans _ ih
    apply Relation.ReflTransGen.single
    rcases hab with h | h
    · left; rw [← h]; exact s.property.1 a
    · right; rw [← h]; exact t.property.1 a

private def component (s t : FixedPointFreeInvolution X) (x : X) : Finset X :=
  Finset.univ.filter fun y => (t.val * s.val).SameCycle x y ∨
    (t.val * s.val).SameCycle (t.val x) y

private theorem mem_component (s t : FixedPointFreeInvolution X) (x y : X) :
    y ∈ component s t x ↔ Connected s.val t.val x y := by
  simp only [component, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (connected_iff_rotation_orbits t.val s.val t.property.1 s.property.1 x y).symm.trans
    (connected_comm t.val s.val x y)

private theorem component_nonempty (s t : FixedPointFreeInvolution X) (x : X) :
    (component s t x).Nonempty := ⟨x, (mem_component s t x x).mpr .refl⟩

/-- The least vertex of the actual two-colored matching component through x. -/
def componentRoot (s t : FixedPointFreeInvolution X) (x : X) : X :=
  (component s t x).min' (component_nonempty s t x)

private theorem root_mem (s t : FixedPointFreeInvolution X) (x : X) :
    Connected s.val t.val x (componentRoot s t x) :=
  (mem_component s t x _).mp (Finset.min'_mem _ _)

private theorem root_eq (s t : FixedPointFreeInvolution X) {x y : X}
    (h : Connected s.val t.val x y) : componentRoot s t x = componentRoot s t y := by
  have he : component s t x = component s t y := by
    ext z
    rw [mem_component, mem_component]
    exact ⟨fun hz => (connected_symm s t h).trans hz, fun hz => h.trans hz⟩
  apply le_antisymm
  · exact Finset.min'_le _ _ (he.symm ▸ Finset.min'_mem _ _)
  · exact Finset.min'_le _ _ (he ▸ Finset.min'_mem _ _)

private theorem root_left (s t : FixedPointFreeInvolution X) (x : X) :
    componentRoot s t (s.val x) = componentRoot s t x :=
  (root_eq s t (Relation.ReflTransGen.single (Or.inl rfl))).symm

private theorem root_right (s t : FixedPointFreeInvolution X) (x : X) :
    componentRoot s t (t.val x) = componentRoot s t x :=
  (root_eq s t (Relation.ReflTransGen.single (Or.inr rfl))).symm

/-- The product orbit containing the least vertex is the s-first phase. -/
def firstPhase (s t : FixedPointFreeInvolution X) (x : X) : Prop :=
  (t.val * s.val).SameCycle (componentRoot s t x) x

instance (s t : FixedPointFreeInvolution X) (x : X) : Decidable (firstPhase s t x) :=
  inferInstanceAs (Decidable ((t.val * s.val).SameCycle (componentRoot s t x) x))

omit [Fintype X] [LinearOrder X] in
private theorem exchange (A B : Set X) (f : Perm X) (hf : Function.Involutive f)
    (hd : Disjoint A B) (hi : f '' A = B) {x : X} (hx : x ∈ A ∪ B) :
    f x ∈ A ↔ x ∉ A := by
  have him {z : X} (hz : z ∈ A) : f z ∈ B := hi ▸ Set.mem_image_of_mem f hz
  constructor
  · intro h hxa
    exact Set.disjoint_left.mp hd h (him hxa)
  · intro hn
    obtain ⟨z, hz, hzx⟩ := (hi ▸ (hx.resolve_left hn) : x ∈ f '' A)
    simpa only [← hzx, hf z] using hz

private theorem phase_left (s t : FixedPointFreeInvolution X) (x : X) :
    firstPhase s t (s.val x) ↔ ¬ firstPhase s t x := by
  rw [firstPhase, root_left]
  let m := componentRoot s t x
  have hc := component_split t.val s.val t.property.1 s.property.1
    t.property.2 s.property.2 m
  apply exchange _ _ s.val s.property.1 hc.1 hc.2.2.2.2.2
  rw [← hc.2.2.2.1]
  exact (connected_comm s.val t.val m x).mp (connected_symm s t (root_mem s t x))

private theorem phase_right (s t : FixedPointFreeInvolution X) (x : X) :
    firstPhase s t (t.val x) ↔ ¬ firstPhase s t x := by
  rw [firstPhase, root_right]
  let m := componentRoot s t x
  have hc := component_split t.val s.val t.property.1 s.property.1
    t.property.2 s.property.2 m
  apply exchange _ _ t.val t.property.1 hc.1 hc.2.2.2.2.1
  rw [← hc.2.2.2.1]
  exact (connected_comm s.val t.val m x).mp (connected_symm s t (root_mem s t x))

/-- Interlace the two product orbits, following s first at each component minimum. -/
def interlace (s t : FixedPointFreeInvolution X) : Perm X where
  toFun x := if firstPhase s t x then s.val x else t.val x
  invFun x := if firstPhase s t x then t.val x else s.val x
  left_inv x := by
    by_cases h : firstPhase s t x
    · simp only [ite_eq_left h, ite_eq_right ((phase_left s t x).not.mpr (not_not.mpr h)),
        s.property.1 x]
    · simp only [ite_eq_right h, ite_eq_left ((phase_right s t x).mpr h), t.property.1 x]
  right_inv x := by
    by_cases h : firstPhase s t x
    · simp only [ite_eq_left h, ite_eq_right ((phase_right s t x).not.mpr (not_not.mpr h)),
        t.property.1 x]
    · simp only [ite_eq_right h, ite_eq_left ((phase_left s t x).mpr h), s.property.1 x]

private theorem interlace_apply (s t : FixedPointFreeInvolution X) (x : X) :
    interlace s t x = if firstPhase s t x then s.val x else t.val x := rfl

private theorem interlace_flip (s t : FixedPointFreeInvolution X) (x : X) :
    firstPhase s t (interlace s t x) ↔ ¬ firstPhase s t x := by
  rw [interlace_apply]
  split_ifs <;> first | exact phase_left s t x | exact phase_right s t x

private theorem interlace_free (s t : FixedPointFreeInvolution X) (x : X) :
    interlace s t x ≠ x := by
  rw [interlace_apply]
  split_ifs <;> first | exact s.property.2 x | exact t.property.2 x

private theorem phase_of_rotation (s t : FixedPointFreeInvolution X) {x y : X}
    (h : (t.val * s.val).SameCycle x y) : firstPhase s t x ↔ firstPhase s t y := by
  have hc : Connected s.val t.val x y := (connected_comm t.val s.val x y).mp
    ((connected_iff_rotation_orbits t.val s.val t.property.1 s.property.1 x y).mpr
      (Or.inl h))
  unfold firstPhase
  rw [← root_eq s t hc]
  exact ⟨fun hx => hx.trans h, fun hy => hy.trans h.symm⟩

private theorem phase_root (s t : FixedPointFreeInvolution X) (x : X) :
    firstPhase s t (componentRoot s t x) := by
  unfold firstPhase
  rw [← root_eq s t (root_mem s t x)]

private theorem interlace_powers (s t : FixedPointFreeInvolution X) (x : X)
    (hx : firstPhase s t x) (k : ℕ) :
    (interlace s t ^ (2*k)) x = ((t.val * s.val)^k) x ∧
    (interlace s t ^ (2*k+1)) x = s.val (((t.val * s.val)^k) x) := by
  have hp (n : ℕ) : firstPhase s t (((t.val * s.val)^n) x) :=
    (phase_of_rotation s t (Perm.SameCycle.refl _ x).pow_right).mp hx
  have he : ∀ n : ℕ, (interlace s t ^ (2*n)) x = ((t.val * s.val)^n) x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hn : 2*(n+1) = 1+(1+2*n) := by omega
      rw [hn, pow_add, pow_add, pow_one, Perm.mul_apply, Perm.mul_apply, ih]
      simp only [interlace_apply, hp n, phase_left, not_true_eq_false, ite_true,
        ite_false, pow_succ', Perm.mul_apply]
  refine ⟨he k, ?_⟩
  rw [pow_succ', Perm.mul_apply, he k, interlace_apply, ite_eq_left (hp k)]

private theorem interlace_connected (s t : FixedPointFreeInvolution X) (x y : X) :
    (interlace s t).SameCycle x y ↔ Connected s.val t.val x y := by
  have hedge (z : X) : Connected s.val t.val z (interlace s t z) := by
    rw [interlace_apply]
    split_ifs
    · exact .single (Or.inl rfl)
    · exact .single (Or.inr rfl)
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact .refl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      exact ih.trans (hedge _)
  · intro h
    let m := componentRoot s t x
    have hp := interlace_powers s t m (phase_root s t x)
    have hc := component_split t.val s.val t.property.1 s.property.1
      t.property.2 s.property.2 m
    have hreach (z : X) (hz : Connected s.val t.val m z) :
        (interlace s t).SameCycle m z := by
      have hz' : z ∈ RotationOrbit (t.val * s.val) m ∪
          RotationOrbit (t.val * s.val) (t.val m) := by
        rw [← hc.2.2.2.1]
        exact (connected_comm s.val t.val m z).mp hz
      rcases hz' with hz' | hz'
      · obtain ⟨k, hk⟩ := hz'.exists_nat_pow_eq
        exact ⟨(2*k : ℕ), by simpa only [zpow_natCast] using (hp k).1.trans hk⟩
      · rw [← hc.2.2.2.2.2] at hz'
        obtain ⟨w, hw, rfl⟩ := hz'
        obtain ⟨k, hk⟩ := hw.exists_nat_pow_eq
        exact ⟨(2*k+1 : ℕ), by
          simpa only [zpow_natCast, hk] using (hp k).2⟩
    have hm := connected_symm s t (root_mem s t x)
    exact (hreach x hm).symm.trans (hreach y (hm.trans h))

omit [Fintype X] [LinearOrder X] in
private theorem parity_along (q : Perm X) (P : X → Prop)
    (hf : ∀ x, P (q x) ↔ ¬ P x) (x : X) (n : ℕ) :
    P ((q^n) x) ↔ (Even n ↔ P x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, hf, ih, Nat.even_add_one]
    tauto

private theorem interlace_even_cycles (s t : FixedPointFreeInvolution X)
    (c : Perm X) (hc : c ∈ (interlace s t).cycleFactorsFinset) :
    Even c.support.card := by
  obtain ⟨x, hx⟩ := (Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
  have he := (Perm.isCycleOn_support_of_mem_cycleFactorsFinset hc).pow_card_apply hx
  have hp := parity_along (interlace s t) (firstPhase s t) (interlace_flip s t)
    x c.support.card
  rw [he] at hp
  tauto

/-- The forward map retains the actual permutation, including common transpositions. -/
def forward (p : FixedPointFreeInvolution X × FixedPointFreeInvolution X) :
    {q : Perm X // (∀ x, q x ≠ x) ∧
      ∀ c ∈ q.cycleFactorsFinset, Even c.support.card} :=
  ⟨interlace p.1 p.2, interlace_free p.1 p.2, interlace_even_cycles p.1 p.2⟩

/-- The least vertex of the full q-cycle, retaining fixed points for this definition. -/
def cycleRoot (q : Perm X) (x : X) : X :=
  (Finset.univ.filter (q.SameCycle x)).min'
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, Perm.SameCycle.refl q x⟩⟩

private theorem cycle_root_mem (q : Perm X) (x : X) : q.SameCycle x (cycleRoot q x) :=
  (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

private theorem cycle_root_eq (q : Perm X) {x y : X} (h : q.SameCycle x y) :
    cycleRoot q x = cycleRoot q y := by
  have he : Finset.univ.filter (q.SameCycle x) = Finset.univ.filter (q.SameCycle y) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩
  apply le_antisymm
  · exact Finset.min'_le _ _ (he.symm ▸ Finset.min'_mem _ _)
  · exact Finset.min'_le _ _ (he ▸ Finset.min'_mem _ _)

/-- Even distance from the least vertex along the actual cycle. -/
def cyclePhase (q : Perm X) (x : X) : Prop := (q^2).SameCycle (cycleRoot q x) x

instance (q : Perm X) (x : X) : Decidable (cyclePhase q x) :=
  inferInstanceAs (Decidable ((q^2).SameCycle (cycleRoot q x) x))

section Inverse

variable (q : {q : Perm X // (∀ x, q x ≠ x) ∧
  ∀ c ∈ q.cycleFactorsFinset, Even c.support.card})

private theorem square_separation (x : X) : ¬ (q.val^2).SameCycle x (q.val x) := by
  intro h
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have hc := Perm.isCycleOn_support_cycleOf q.val x
  have hx : x ∈ (q.val.cycleOf x).support :=
    (Perm.mem_support_cycleOf_iff' (q.property.1 x)).mpr (Perm.SameCycle.refl _ _)
  have he := q.property.2 _ (Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
    (Perm.mem_support.mpr (q.property.1 x)))
  have hm : 2*k ≡ 1 [MOD (q.val.cycleOf x).support.card] :=
    (hc.pow_apply_eq_pow_apply hx).mp (by simpa only [pow_mul, pow_one] using hk)
  have h2 := hm.of_dvd (even_iff_two_dvd.mp he)
  simp [Nat.ModEq] at h2

private theorem square_cases {a b : X} (h : q.val.SameCycle a b) :
    (q.val^2).SameCycle a b ∨ (q.val^2).SameCycle a (q.val b) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    refine ⟨(k : ℕ), ?_⟩
    rw [zpow_natCast, ← pow_mul]
    have hn' : 2*k = n := by omega
    rwa [hn']
  · right
    refine ⟨(k+1 : ℕ), ?_⟩
    rw [zpow_natCast, ← pow_mul]
    have hn' : 2*(k+1) = n+1 := by omega
    rw [hn', pow_succ', Perm.mul_apply, hn]

private theorem cycle_phase_flip (x : X) :
    cyclePhase q.val (q.val x) ↔ ¬ cyclePhase q.val x := by
  unfold cyclePhase
  rw [← cycle_root_eq q.val (Perm.SameCycle.refl _ x).apply_right]
  constructor
  · intro h h'
    exact square_separation q x (h'.symm.trans h)
  · intro h
    exact (square_cases q (cycle_root_mem q.val x).symm).resolve_left h

private theorem cycle_phase_prev (x : X) :
    cyclePhase q.val (q.val⁻¹ x) ↔ ¬ cyclePhase q.val x := by
  have h := cycle_phase_flip q (q.val⁻¹ x)
  simp only [Perm.inv_def, Equiv.apply_symm_apply] at h
  tauto

private def alternating (b : Bool) : Perm X where
  toFun x := if (cyclePhase q.val x ↔ b = true) then q.val x else q.val⁻¹ x
  invFun x := if (cyclePhase q.val x ↔ b = true) then q.val x else q.val⁻¹ x
  left_inv x := by
    cases b <;> by_cases h : cyclePhase q.val x <;>
      simp_all only [Bool.false_eq_true,
        iff_false, iff_true, cycle_phase_flip, cycle_phase_prev, ite_true, ite_false,
        not_true_eq_false, not_false_eq_true] <;>
      first | exact q.val.apply_symm_apply x | exact q.val.symm_apply_apply x
  right_inv x := by
    cases b <;> by_cases h : cyclePhase q.val x <;>
      simp_all only [Bool.false_eq_true,
        iff_false, iff_true, cycle_phase_flip, cycle_phase_prev, ite_true, ite_false,
        not_true_eq_false, not_false_eq_true] <;>
      first | exact q.val.apply_symm_apply x | exact q.val.symm_apply_apply x

private theorem alternating_free (b : Bool) (x : X) : alternating q b x ≠ x := by
  change (if (cyclePhase q.val x ↔ b = true) then q.val x else q.val⁻¹ x) ≠ x
  split_ifs
  · exact q.property.1 x
  · intro h
    apply q.property.1 x
    simpa only [Perm.inv_def, Equiv.apply_symm_apply] using (congrArg q.val h).symm

/-- Recover both ordered mates by alternating successor and predecessor from each minimum. -/
def recover : FixedPointFreeInvolution X × FixedPointFreeInvolution X :=
  (⟨alternating q true, (alternating q true).left_inv, alternating_free q true⟩,
   ⟨alternating q false, (alternating q false).left_inv, alternating_free q false⟩)

private theorem recover_left_apply (x : X) :
    (recover q).1.val x = if cyclePhase q.val x then q.val x else q.val⁻¹ x := by
  change (if (cyclePhase q.val x ↔ true = true) then q.val x else q.val⁻¹ x) = _
  simp

private theorem recover_right_apply (x : X) :
    (recover q).2.val x = if cyclePhase q.val x then q.val⁻¹ x else q.val x := by
  change (if (cyclePhase q.val x ↔ false = true) then q.val x else q.val⁻¹ x) = _
  simp only [Bool.false_eq_true, iff_false, ite_not]

private theorem recover_connected (x y : X) :
    Connected (recover q).1.val (recover q).2.val x y ↔ q.val.SameCycle x y := by
  have hstep (z : X) : Connected (recover q).1.val (recover q).2.val z (q.val z) := by
    by_cases h : cyclePhase q.val z
    · exact .single (Or.inl (by rw [recover_left_apply, ite_eq_left h]))
    · exact .single (Or.inr (by rw [recover_right_apply, ite_eq_right h]))
  constructor
  · intro h
    induction h with
    | refl => exact Perm.SameCycle.refl _ _
    | @tail a b h hab ih =>
      apply ih.trans
      rcases hab with hab | hab
      · rw [← hab, recover_left_apply]
        split_ifs
        · exact (Perm.SameCycle.refl _ _).apply_right
        · exact (Perm.SameCycle.refl _ _).symm_apply_right
      · rw [← hab, recover_right_apply]
        split_ifs
        · exact (Perm.SameCycle.refl _ _).symm_apply_right
        · exact (Perm.SameCycle.refl _ _).apply_right
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact .refl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      exact ih.trans (hstep _)

private theorem recover_root (x : X) :
    componentRoot (recover q).1 (recover q).2 x = cycleRoot q.val x := by
  have he : component (recover q).1 (recover q).2 x =
      Finset.univ.filter (q.val.SameCycle x) := by
    ext y
    rw [mem_component, recover_connected]
    simp
  apply le_antisymm
  · exact Finset.min'_le _ _ (he.symm ▸ Finset.min'_mem _ _)
  · exact Finset.min'_le _ _ (he ▸ Finset.min'_mem _ _)

private theorem cycle_phase_root (x : X) : cyclePhase q.val (cycleRoot q.val x) := by
  unfold cyclePhase
  rw [← cycle_root_eq q.val (cycle_root_mem q.val x)]

private theorem recover_rotation_powers (a : X) (ha : cyclePhase q.val a) (n : ℕ) :
    (((recover q).2.val * (recover q).1.val)^n) a = ((q.val^2)^n) a := by
  have hp (k : ℕ) : cyclePhase q.val (((q.val^2)^k) a) := by
    rw [← pow_mul]
    exact (parity_along q.val (cyclePhase q.val) (cycle_phase_flip q) a (2*k)).mpr
      (by simpa using ha)
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      (((recover q).2.val * (recover q).1.val)^(n+1)) a =
          ((recover q).2.val * (recover q).1.val)
            ((((recover q).2.val * (recover q).1.val)^n) a) := by
              rw [pow_succ', Perm.mul_apply]
      _ = ((recover q).2.val * (recover q).1.val) (((q.val^2)^n) a) :=
        congrArg _ ih
      _ = q.val (q.val (((q.val^2)^n) a)) := by
        rw [Perm.mul_apply, recover_left_apply, ite_eq_left (hp n),
          recover_right_apply, ite_eq_right
            ((cycle_phase_flip q _).not.mpr (not_not.mpr (hp n)))]
      _ = ((q.val^2)^(n+1)) a := by
        rw [pow_succ' (q.val^2) n, Perm.mul_apply]
        rfl

private theorem recover_phase (x : X) :
    firstPhase (recover q).1 (recover q).2 x ↔ cyclePhase q.val x := by
  unfold firstPhase cyclePhase
  rw [recover_root]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℕ), ?_⟩
    rw [zpow_natCast, ← recover_rotation_powers q _ (cycle_phase_root q x) n]
    exact hn
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℕ), ?_⟩
    rw [zpow_natCast, recover_rotation_powers q _ (cycle_phase_root q x) n]
    exact hn

private theorem forward_recover : forward (recover q) = q := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change interlace (recover q).1 (recover q).2 x = q.val x
  rw [interlace_apply]
  by_cases h : cyclePhase q.val x
  · rw [ite_eq_left ((recover_phase q x).mpr h), recover_left_apply, ite_eq_left h]
  · rw [ite_eq_right (fun hp => h ((recover_phase q x).mp hp)),
      recover_right_apply, ite_eq_right h]

end Inverse

private theorem interlace_root (s t : FixedPointFreeInvolution X) (x : X) :
    cycleRoot (interlace s t) x = componentRoot s t x := by
  have he : component s t x = Finset.univ.filter ((interlace s t).SameCycle x) := by
    ext y
    rw [mem_component, ← interlace_connected]
    simp
  apply le_antisymm
  · exact Finset.min'_le _ _ (he ▸ Finset.min'_mem _ _)
  · exact Finset.min'_le _ _ (he.symm ▸ Finset.min'_mem _ _)

private theorem interlace_phase (s t : FixedPointFreeInvolution X) (x : X) :
    cyclePhase (interlace s t) x ↔ firstPhase s t x := by
  unfold cyclePhase firstPhase
  rw [interlace_root]
  have hp := interlace_powers s t (componentRoot s t x) (phase_root s t x)
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℕ), ?_⟩
    rw [zpow_natCast]
    rw [← (hp n).1, pow_mul]
    exact hn
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℕ), ?_⟩
    rw [zpow_natCast, ← pow_mul, (hp n).1]
    exact hn

private theorem recover_forward (s t : FixedPointFreeInvolution X) :
    recover (forward (s,t)) = (s,t) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [recover_left_apply]
    change (if cyclePhase (interlace s t) x then interlace s t x
      else (interlace s t)⁻¹ x) = s.val x
    simp only [interlace_phase]
    by_cases h : firstPhase s t x
    · rw [ite_eq_left h, interlace_apply, ite_eq_left h]
    · rw [ite_eq_right h]
      change (if firstPhase s t x then t.val x else s.val x) = s.val x
      rw [ite_eq_right h]
  · apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [recover_right_apply]
    change (if cyclePhase (interlace s t) x then (interlace s t)⁻¹ x
      else interlace s t x) = t.val x
    simp only [interlace_phase]
    by_cases h : firstPhase s t x
    · rw [ite_eq_left h]
      change (if firstPhase s t x then t.val x else s.val x) = t.val x
      rw [ite_eq_left h]
    · rw [ite_eq_right h, interlace_apply, ite_eq_right h]

/-- Rooted interlacing covers the whole colored component and recovers both ordered mates.
The forward and predecessor colors use the same least-vertex phase. -/
theorem rooted_interlacing (s t : FixedPointFreeInvolution X) :
    recover (forward (s,t)) = (s,t) ∧
    (∀ x y, (interlace s t).SameCycle x y ↔ Connected s.val t.val x y) ∧
    (∀ x, Connected s.val t.val x (componentRoot s t x) ∧
      ∀ y, Connected s.val t.val x y → componentRoot s t x ≤ y) ∧
    (∀ m, (∀ y, Connected s.val t.val m y → m ≤ y) → ∀ k : ℕ,
      (interlace s t ^ (2*k)) m = ((t.val*s.val)^k) m ∧
      (interlace s t ^ (2*k+1)) m = s.val (((t.val*s.val)^k) m)) ∧
    (∀ x, interlace s t x = (if firstPhase s t x then s.val x else t.val x) ∧
      (interlace s t)⁻¹ x = (if firstPhase s t x then t.val x else s.val x) ∧
      (cyclePhase (interlace s t) x ↔ firstPhase s t x)) := by
  refine ⟨recover_forward s t, interlace_connected s t, ?_, ?_, ?_⟩
  · intro x
    exact ⟨root_mem s t x, fun y hy => Finset.min'_le _ _ ((mem_component s t x y).mpr hy)⟩
  · intro m hm k
    have he : componentRoot s t m = m := le_antisymm
      (Finset.min'_le _ _ ((mem_component s t m m).mpr .refl))
      (hm _ (root_mem s t m))
    have hp := phase_root s t m
    rw [he] at hp
    exact interlace_powers s t m hp k
  · intro x
    exact ⟨rfl, rfl, interlace_phase s t x⟩

/-- Alternating the actual successor and predecessor reconstructs the original permutation. -/
theorem rooted_reconstruction
    (q : {q : Perm X // (∀ x, q x ≠ x) ∧
      ∀ c ∈ q.cycleFactorsFinset, Even c.support.card}) :
    forward (recover q) = q ∧ ∀ x,
      (recover q).1.val x = (if cyclePhase q.val x then q.val x else q.val⁻¹ x) ∧
      (recover q).2.val x = (if cyclePhase q.val x then q.val⁻¹ x else q.val x) := by
  exact ⟨forward_recover q, fun x => ⟨recover_left_apply q x, recover_right_apply q x⟩⟩

/-- The actual s-first rooted equivalence, with no extra component orientation bit. -/
def equivalence : (FixedPointFreeInvolution X × FixedPointFreeInvolution X) ≃
    {q : Perm X // (∀ x, q x ≠ x) ∧
      ∀ c ∈ q.cycleFactorsFinset, Even c.support.card} where
  toFun := forward
  invFun := recover
  left_inv p := (rooted_interlacing p.1 p.2).1
  right_inv q := (rooted_reconstruction q).1

#print axioms rooted_interlacing
#print axioms rooted_reconstruction
#print axioms equivalence

end D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles
