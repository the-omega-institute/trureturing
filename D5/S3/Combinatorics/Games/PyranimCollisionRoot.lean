/- GID: D5/S3/Combinatorics/Games/PyranimCollisionRoot
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Games/PyranimCollisionRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Block multiplicity bounds and the all-width root limits for Pyranim collisions. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/33619
-/

import D5.S3.Combinatorics.Games.PyranimPosition
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Block multiplicity bounds and the all-width root limits for Pyranim collisions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

open Filter Topology

namespace D5.S3.Combinatorics.Games.Pyranim

section

variable {n m : ℕ} {A : Stable n} {B : Stable m}

/-- Every stable subposition of an initial position, including the initial position. -/
private abbrev Desc (A : Stable n) := {I : Stable n // I.val ⊆ A.val}

private def transport (e : A.val ≃o B.val) (I : Desc A) : Desc B :=
  ⟨⟨{b | ∃ hb : b ∈ B.val, (e.symm ⟨b, hb⟩).val ∈ I.val.val}, by
      intro c b hbc hc
      obtain ⟨hcB, hcI⟩ := hc
      refine ⟨B.property hbc hcB, I.val.property ?_ hcI⟩
      exact e.symm.monotone (show (⟨b, B.property hbc hcB⟩ : B.val) ≤ ⟨c, hcB⟩ from hbc)⟩,
    fun _ hb => hb.choose⟩

private theorem mem_transport_iff (e : A.val ≃o B.val) (I : Desc A) (a : A.val) :
    (e a).val ∈ (transport e I).val.val ↔ a.val ∈ I.val.val := by
  change (∃ h : (e a).val ∈ B.val, (e.symm ⟨(e a).val, h⟩).val ∈ I.val.val) ↔ _
  constructor
  · rintro ⟨_, h⟩
    simpa only [Subtype.coe_eta, OrderIso.symm_apply_apply] using h
  · intro h
    exact ⟨(e a).property, by simpa only [Subtype.coe_eta, OrderIso.symm_apply_apply]⟩

private theorem transport_symm (e : A.val ≃o B.val) (I : Desc A) :
    transport e.symm (transport e I) = I := by
  apply Subtype.ext
  apply Subtype.ext
  ext a
  change a ∈ (transport e.symm (transport e I)).val.val ↔ a ∈ I.val.val
  constructor
  · intro h
    have ha : a ∈ A.val := h.choose
    rw [← show (e.symm (e ⟨a, ha⟩)).val = a by simp] at h
    exact (mem_transport_iff e I ⟨a, ha⟩).mp
      ((mem_transport_iff e.symm (transport e I) (e ⟨a, ha⟩)).mp h)
  · intro h
    have ha := I.property h
    have ht := (mem_transport_iff e.symm (transport e I) (e ⟨a, ha⟩)).mpr
      ((mem_transport_iff e I ⟨a, ha⟩).mpr h)
    simpa only [OrderIso.symm_apply_apply] using ht

private def descEquiv (e : A.val ≃o B.val) : Desc A ≃ Desc B where
  toFun := transport e
  invFun := transport e.symm
  left_inv := transport_symm e
  right_inv := transport_symm e.symm

private theorem upperCover_transport (e : A.val ≃o B.val) (I : Desc A) (c u : A.val) :
    UpperCover (transport e I).val (e c).val (e u).val ↔ UpperCover I.val c.val u.val := by
  have hlt (a b : A.val) : (e a).val < (e b).val ↔ a.val < b.val := e.lt_iff_lt
  constructor
  · rintro ⟨hu, hcu, hcover⟩
    refine ⟨(mem_transport_iff e I u).mp hu, (hlt c u).mp hcu, ?_⟩
    intro v hv hcv hvu
    let vA : A.val := ⟨v, I.property hv⟩
    exact hcover _ ((mem_transport_iff e I vA).mpr hv) ((hlt c vA).mpr hcv)
      ((hlt vA u).mpr hvu)
  · rintro ⟨hu, hcu, hcover⟩
    refine ⟨(mem_transport_iff e I u).mpr hu, (hlt c u).mpr hcu, ?_⟩
    intro v hv hcv hvu
    let vB : B.val := ⟨v, (transport e I).property hv⟩
    let vA := e.symm vB
    have he : e vA = vB := e.apply_symm_apply vB
    have hcv' : (e c).val < (e vA).val := by rw [he]; exact hcv
    have hvu' : (e vA).val < (e u).val := by rw [he]; exact hvu
    exact hcover _ ((mem_transport_iff e I vA).mp (he ▸ hv)) ((hlt c vA).mp hcv')
      ((hlt vA u).mp hvu')

private theorem visible_transport (e : A.val ≃o B.val) (I : Desc A) (c : A.val) :
    Visible (transport e I).val (e c).val ↔ Visible I.val c.val := by
  rw [visible_iff_covers, visible_iff_covers, mem_transport_iff]
  refine and_congr_right (fun _ => not_congr ?_)
  constructor
  · rintro ⟨u, v, hu, hv, hne⟩
    let uB : B.val := ⟨u, (transport e I).property hu.1⟩
    let vB : B.val := ⟨v, (transport e I).property hv.1⟩
    refine ⟨(e.symm uB).val, (e.symm vB).val, ?_, ?_, ?_⟩
    · apply (upperCover_transport e I c (e.symm uB)).mp
      simpa only [OrderIso.apply_symm_apply] using hu
    · apply (upperCover_transport e I c (e.symm vB)).mp
      simpa only [OrderIso.apply_symm_apply] using hv
    · intro h
      exact hne (congrArg Subtype.val (e.symm.injective (Subtype.ext h)))
  · rintro ⟨u, v, hu, hv, hne⟩
    let uA : A.val := ⟨u, I.property hu.1⟩
    let vA : A.val := ⟨v, I.property hv.1⟩
    exact ⟨(e uA).val, (e vA).val, (upperCover_transport e I c uA).mpr hu,
      (upperCover_transport e I c vA).mpr hv,
      fun h => hne (congrArg Subtype.val (e.injective (Subtype.ext h)))⟩

private def removeDesc (I : Desc A) (c : A.val) : Desc A :=
  ⟨removeChip I.val c.val, fun _ hb => I.property hb.1⟩

private theorem transport_remove (e : A.val ≃o B.val) (I : Desc A) (c : A.val) :
    transport e (removeDesc I c) = removeDesc (transport e I) (e c) := by
  apply Subtype.ext
  apply Subtype.ext
  ext b
  change b ∈ (transport e (removeDesc I c)).val.val ↔
    b ∈ (removeDesc (transport e I) (e c)).val.val
  by_cases hb : b ∈ B.val
  · let a := e.symm ⟨b, hb⟩
    rw [← show (e a).val = b by simp [a], mem_transport_iff]
    change (a.val ∈ I.val.val ∧ ¬ c.val ≤ a.val) ↔
      (e a).val ∈ (transport e I).val.val ∧ ¬ (e c).val ≤ (e a).val
    rw [mem_transport_iff, show (e c).val ≤ (e a).val ↔ c.val ≤ a.val from e.le_iff_le]
  · exact iff_of_false (fun h => hb ((transport e (removeDesc I c)).property h))
      (fun h => hb ((removeDesc (transport e I) (e c)).property h))

private theorem option_transport (e : A.val ≃o B.val) (I J : Desc A) :
    LegalOption (transport e I).val (transport e J).val ↔ LegalOption I.val J.val := by
  suffices forward : ∀ {i j : ℕ} {P : Stable i} {Q : Stable j} (f : P.val ≃o Q.val)
      (X Y : Desc P), LegalOption X.val Y.val →
        LegalOption (transport f X).val (transport f Y).val by
    constructor
    · intro h
      simpa only [transport_symm] using forward e.symm (transport e I) (transport e J) h
    · exact forward e I J
  intro i j P Q f X Y h
  obtain ⟨c, hc, heq⟩ := h
  let a : P.val := ⟨c, X.property hc.1⟩
  have hy : Y = removeDesc X a := Subtype.ext heq
  exact ⟨(f a).val, (visible_transport f X a).mpr hc, by
    rw [hy, transport_remove]; rfl⟩

/-- Options as actual successor positions inside the original carrier. -/
private def descOptions (I : Desc A) :
    Options I.val ≃ {J : Desc A // LegalOption I.val J.val} where
  toFun J := ⟨⟨J.val, (legalOption_ssubset J.property).1.trans I.property⟩, J.property⟩
  invFun J := ⟨J.val.val, J.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def transportOptions (e : A.val ≃o B.val) (I : Desc A) :
    Options I.val ≃ Options (transport e I).val :=
  (descOptions I).trans
    (((descEquiv e).subtypeEquiv (fun J => (option_transport e I J).symm)).trans
      (descOptions (transport e I)).symm)

private theorem transport_gameIso (e : A.val ≃o B.val) (I : Desc A) :
    GameIso I.val (transport e I).val := by
  induction I using (measure (fun J : Desc A => chipCount J.val)).wf.induction with
  | h I ih =>
    rw [gameIso_iff]
    refine ⟨transportOptions e I, ?_⟩
    intro J
    exact ih ((descOptions I J).val) (chipCount_lt_of_option J.property)

private theorem transport_self (e : A.val ≃o B.val) :
    transport e (⟨A, fun _ h => h⟩ : Desc A) = ⟨B, fun _ h => h⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  ext b
  exact ⟨fun h => (transport e (⟨A, fun _ h => h⟩ : Desc A)).property h,
    fun hb => ⟨hb, (e.symm ⟨b, hb⟩).property⟩⟩

private theorem gameIso_of_chipOrderIso (e : A.val ≃o B.val) : GameIso A B := by
  have h := transport_gameIso e (⟨A, fun _ h => h⟩ : Desc A)
  rw [transport_self] at h
  exact h

end

section

variable {n : ℕ}

private structure Window (n : ℕ) where
  start : ℕ
  width : ℕ
  fits : start + width ≤ n

namespace Window

private def place (W : Window n) (c : Interval W.width) : Interval n :=
  ⟨W.start + c.left, W.start + c.right, by have := c.left_pos; omega,
    Nat.add_le_add_left c.left_le_right _, (Nat.add_le_add_left c.right_le_width _).trans W.fits⟩

private theorem place_le_place (W : Window n) (c u : Interval W.width) :
    W.place c ≤ W.place u ↔ c ≤ u := by
  change (W.start + u.left ≤ W.start + c.left ∧ W.start + c.right ≤ W.start + u.right) ↔
    (u.left ≤ c.left ∧ c.right ≤ u.right)
  omega

private theorem place_injective (W : Window n) : Function.Injective W.place := by
  intro c u h
  exact le_antisymm ((W.place_le_place c u).mp h.le) ((W.place_le_place u c).mp h.ge)

private theorem below_place (W : Window n) {x : Interval n} {c : Interval W.width}
    (h : x ≤ W.place c) : ∃ a, a ≤ c ∧ W.place a = x := by
  obtain ⟨hl, hr⟩ := h
  change W.start + c.left ≤ x.left at hl
  change x.right ≤ W.start + c.right at hr
  have := c.left_pos
  have := c.right_le_width
  have := x.left_le_right
  let a : Interval W.width := ⟨x.left - W.start, x.right - W.start, by omega,
    by omega, by omega⟩
  refine ⟨a, ?_, ?_⟩
  · change c.left ≤ x.left - W.start ∧ x.right - W.start ≤ c.right
    omega
  · apply Interval.ext <;> dsimp [place, a] <;> omega

end Window

section Layout

variable {ι : Type} (W : ι → Window n)

private def Separated : Prop :=
  ∀ i j, i ≠ j → (W i).start + (W i).width ≤ (W j).start ∨
    (W j).start + (W j).width ≤ (W i).start

private theorem index_eq_of_placed_le (hW : Separated W) {i j : ι}
    {c : Interval (W i).width} {u : Interval (W j).width}
    (h : (W i).place c ≤ (W j).place u) : i = j := by
  by_contra hne
  obtain ⟨hl, hr⟩ := h
  change (W j).start + u.left ≤ (W i).start + c.left at hl
  change (W i).start + c.right ≤ (W j).start + u.right at hr
  have := c.left_pos
  have := c.left_le_right
  have := c.right_le_width
  have := u.left_pos
  have := u.right_le_width
  rcases hW i j hne with hsep | hsep <;> omega

/-- Assemble block positions by including only chips internal to one window. -/
private def assemble (I : ∀ i, Stable (W i).width) : Stable n :=
  ⟨{x | ∃ i c, c ∈ (I i).val ∧ (W i).place c = x}, by
    intro x y hyx hx
    obtain ⟨i, c, hc, rfl⟩ := hx
    obtain ⟨a, hac, rfl⟩ := (W i).below_place hyx
    exact ⟨i, a, (I i).property hac hc, rfl⟩⟩

private theorem mem_assemble_place_iff (hW : Separated W) (I : ∀ i, Stable (W i).width)
    (i : ι) (c : Interval (W i).width) :
    (W i).place c ∈ (assemble W I).val ↔ c ∈ (I i).val := by
  constructor
  · rintro ⟨j, u, hu, heq⟩
    have hij := index_eq_of_placed_le W hW heq.ge
    subst j
    exact (W i).place_injective heq ▸ hu
  · intro hc
    exact ⟨i, c, hc, rfl⟩

private def assembleChip (I : ∀ i, Stable (W i).width)
    (a : Σ i, (I i).val) : (assemble W I).val :=
  ⟨(W a.1).place a.2.val, a.1, a.2.val, a.2.property, rfl⟩

private noncomputable def assembleChipsEquiv (hW : Separated W) (I : ∀ i, Stable (W i).width) :
    (Σ i, (I i).val) ≃ (assemble W I).val :=
  Equiv.ofBijective (assembleChip W I) (by
    constructor
    · rintro ⟨i, c⟩ ⟨j, u⟩ h
      have heq : (W i).place c.val = (W j).place u.val := congrArg Subtype.val h
      have hij := index_eq_of_placed_le W hW heq.le
      subst j
      have hcu : c = u := Subtype.ext ((W i).place_injective heq)
      cases hcu
      rfl
    · rintro ⟨x, i, c, hc, rfl⟩
      exact ⟨⟨i, ⟨c, hc⟩⟩, rfl⟩)

private noncomputable def assembleChipOrderIso (hW : Separated W)
    {I J : ∀ i, Stable (W i).width} (p : Equiv.Perm ι)
    (localIso : ∀ i, (I i).val ≃o (J (p i)).val) :
    (assemble W I).val ≃o (assemble W J).val where
  toEquiv := (assembleChipsEquiv W hW I).symm.trans
    ((Equiv.sigmaCongr p (fun i => (localIso i).toEquiv)).trans (assembleChipsEquiv W hW J))
  map_rel_iff' := by
    intro x y
    obtain ⟨⟨i, c⟩, rfl⟩ := (assembleChipsEquiv W hW I).surjective x
    obtain ⟨⟨j, u⟩, rfl⟩ := (assembleChipsEquiv W hW I).surjective y
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    change (W (p i)).place (localIso i c).val ≤ (W (p j)).place (localIso j u).val ↔
      (W i).place c.val ≤ (W j).place u.val
    by_cases hij : i = j
    · subst j
      rw [Window.place_le_place, Window.place_le_place]
      exact (localIso i).le_iff_le
    · exact iff_of_false (fun h => hij (p.injective (index_eq_of_placed_le W hW h)))
        (fun h => hij (index_eq_of_placed_le W hW h))

private theorem assemble_gameIso (hW : Separated W)
    {I J : ∀ i, Stable (W i).width} (p : Equiv.Perm ι)
    (localIso : ∀ i, (I i).val ≃o (J (p i)).val) : GameIso (assemble W I) (assemble W J) :=
  gameIso_of_chipOrderIso (assembleChipOrderIso W hW p localIso)

end Layout

/-- Full blocks occupy consecutive windows, followed by one remainder window. -/
private def blockWindows (m k r : ℕ) : Fin k ⊕ Unit → Window (k * m + r)
  | .inl i => ⟨i.val * m, m,
      (calc
        i.val * m + m = (i.val + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ k * m := Nat.mul_le_mul_right m i.isLt
        _ ≤ k * m + r := Nat.le_add_right _ _)⟩
  | .inr _ => ⟨k * m, r, le_rfl⟩

private theorem blockWindows_separated (m k r : ℕ) : Separated (blockWindows m k r) := by
  intro i j hne
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hij : i.val ≠ j.val := fun h => hne (congrArg Sum.inl (Fin.ext h))
      change i.val * m + m ≤ j.val * m ∨ j.val * m + m ≤ i.val * m
      rcases lt_or_gt_of_ne hij with h | h
      · exact Or.inl (by simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right m h)
      · exact Or.inr (by simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right m h)
    | inr j =>
      exact Or.inl (by
        change i.val * m + m ≤ k * m
        simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right m i.isLt)
  | inr i =>
    cases j with
    | inl j =>
      exact Or.inr (by
        change j.val * m + m ≤ k * m
        simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right m j.isLt)
    | inr j => exact (hne (congrArg Sum.inr (Subsingleton.elim i j))).elim

private def blockPatterns {m k r : ℕ} (f : Fin k → Stable m) (R : Stable r) :
    ∀ i, Stable ((blockWindows m k r) i).width
  | .inl i => f i
  | .inr _ => R

private def blockBoard {m k r : ℕ} (f : Fin k → Stable m) (R : Stable r) : Stable (k * m + r) :=
  assemble (blockWindows m k r) (blockPatterns f R)

private theorem blockBoard_injective {m k r : ℕ} (R : Stable r) :
    Function.Injective (fun f : Fin k → Stable m => blockBoard f R) := by
  intro f g h
  funext i
  apply Subtype.ext
  ext c
  have hf := mem_assemble_place_iff _ (blockWindows_separated m k r) (blockPatterns f R)
    (.inl i) c
  have hg := mem_assemble_place_iff _ (blockWindows_separated m k r) (blockPatterns g R)
    (.inl i) c
  change blockBoard f R = blockBoard g R at h
  have hmem : (blockWindows m k r (.inl i)).place c ∈ (blockBoard f R).val ↔
      (blockWindows m k r (.inl i)).place c ∈ (blockBoard g R).val := by rw [h]
  exact hf.symm.trans (hmem.trans hg)

private theorem blockBoard_gameIso_of_perm {m k r : ℕ} {f g : Fin k → Stable m} (R : Stable r)
    (p : Equiv.Perm (Fin k)) (hp : ∀ i, g (p i) = f i) :
    GameIso (blockBoard f R) (blockBoard g R) := by
  apply assemble_gameIso _ (blockWindows_separated m k r) (Equiv.sumCongr p (Equiv.refl Unit))
  rintro (i | i)
  · change (f i).val ≃o (g (p i)).val
    rw [hp]
  · exact OrderIso.refl _

private noncomputable def finiteEquivOfCardEq {S T : Type} [Finite S] [Finite T]
    (h : Nat.card S = Nat.card T) : S ≃ T := by
  letI := Fintype.ofFinite S
  letI := Fintype.ofFinite T
  exact Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using h)

/-- Equal multiplicities match by a bijection of the fibers over each block type. -/
private noncomputable def permOfBlockCounts {k : ℕ} {T : Type} {f g : Fin k → T}
    (h : ∀ t, Nat.card {i // f i = t} = Nat.card {i // g i = t}) : Equiv.Perm (Fin k) := by
  classical
  exact Equiv.ofFiberEquiv (fun t => finiteEquivOfCardEq (h t))

private theorem permOfBlockCounts_spec {k : ℕ} {T : Type} {f g : Fin k → T}
    (h : ∀ t, Nat.card {i // f i = t} = Nat.card {i // g i = t}) (i : Fin k) :
    g (permOfBlockCounts h i) = f i := by
  classical
  exact Equiv.ofFiberEquiv_map (fun t => finiteEquivOfCardEq (h t)) i

end

section

/-- The mandatory chips of a full block have lengths one and two. -/
private def ShortRowFull {m : ℕ} (I : Stable m) : Prop :=
  ∀ c : Interval m, c.right ≤ c.left + 1 → c ∈ I.val

private abbrev FullBlock (m : ℕ) := {I : Stable m // ShortRowFull I}

private theorem shortRowFull_iff (b : ℕ) (I : FullBottom (b + 2)) :
    ShortRowFull I.val ↔ ∀ c : Interval (b + 1), c.left = c.right → c ∈ (removeBottom I).val := by
  constructor
  · intro h c hc
    change raiseRight c ∈ I.val.val
    apply h
    change c.right + 1 ≤ c.left + 1
    omega
  · intro h c hc
    by_cases hsingle : c.left = c.right
    · exact I.property c hsingle
    · have hlt : c.left < c.right := lt_of_le_of_ne c.left_le_right hsingle
      have hshort : (lowerRight c hlt).left = (lowerRight c hlt).right := by
        change c.left = c.right - 1
        omega
      have hmem := h (lowerRight c hlt) hshort
      change raiseRight (lowerRight c hlt) ∈ I.val.val at hmem
      simpa only [raiseRight_lowerRight] using hmem

/-- Strip the bottom row twice and relabel [i,j] as [i,j-2]. -/
private def fullBlockEquiv (b : ℕ) : FullBlock (b + 2) ≃ Stable b :=
  let refineBottom : FullBlock (b + 2) ≃ {I : FullBottom (b + 2) // ShortRowFull I.val} :=
    { toFun := fun I => ⟨⟨I.val, fun c hc => I.property c (by omega)⟩, I.property⟩
      invFun := fun I => ⟨I.val.val, I.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refineBottom.trans
    (((fullBottomSuccEquiv (b + 1)).subtypeEquiv (shortRowFull_iff b)).trans (fullBottomSuccEquiv b))

private theorem fullBlockCard (b : ℕ) : Nat.card (FullBlock (b + 2)) = catalan (b + 1) :=
  (Nat.card_congr (fullBlockEquiv b)).trans (stableCard b)

private theorem width_decomp (n b : ℕ) : n / (b + 2) * (b + 2) + n % (b + 2) = n := by
  simpa only [Nat.mul_comm] using Nat.div_add_mod n (b + 2)

/-- The registered boards leave the final n % (b+2) bottom sites empty. -/
private def registeredBoard (n b : ℕ) (f : Fin (n / (b + 2)) → FullBlock (b + 2)) : Stable n :=
  Equiv.cast (congrArg Stable (width_decomp n b))
    (blockBoard (fun i => (f i).val) (emptyStable (n % (b + 2))))

private theorem registeredBoard_injective (n b : ℕ) : Function.Injective (registeredBoard n b) := by
  intro f g h
  have hboards : blockBoard (fun i => (f i).val) (emptyStable (n % (b + 2))) =
      blockBoard (fun i => (g i).val) (emptyStable (n % (b + 2))) :=
    (Equiv.cast (congrArg Stable (width_decomp n b))).injective h
  have htypes := blockBoard_injective (emptyStable (n % (b + 2))) hboards
  exact funext (fun i => Subtype.ext (congrFun htypes i))

private theorem gameIso_cast {m n : ℕ} (h : m = n) {I J : Stable m} (hIJ : GameIso I J) :
    GameIso (Equiv.cast (congrArg Stable h) I) (Equiv.cast (congrArg Stable h) J) := by
  subst n
  exact hIJ

private theorem registeredBoard_gameIso_of_counts (n b : ℕ) {f g : Fin (n / (b + 2)) → FullBlock (b + 2)}
    (h : ∀ t, Nat.card {i // f i = t} = Nat.card {i // g i = t}) :
    GameIso (registeredBoard n b f) (registeredBoard n b g) :=
  gameIso_cast (width_decomp n b)
    (blockBoard_gameIso_of_perm (emptyStable (n % (b + 2))) (permOfBlockCounts h)
      (fun i => congrArg Subtype.val (permOfBlockCounts_spec h i)))

private theorem registeredBoard_card (n b : ℕ) :
    Nat.card (Set.range (registeredBoard n b)) = (catalan (b + 1)) ^ (n / (b + 2)) := by
  classical
  rw [← Nat.card_congr (Equiv.ofInjective _ (registeredBoard_injective n b))]
  let := Fintype.ofFinite (Interval (b + 2))
  let _ : Fintype (FullBlock (b + 2)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    ← Nat.card_eq_fintype_card, fullBlockCard]

end

section

/-- Each coordinate counts the occurrences of one literal full-block type. -/
private noncomputable def blockMultiplicity {q m : ℕ} (f : Fin q → FullBlock m) (t : FullBlock m) : Fin (q + 1) :=
  ⟨Nat.card {i // f i = t},
    Nat.lt_succ_of_le (by
      simpa only [Nat.card_fin] using
        (Nat.card_le_card_of_injective
          (Subtype.val : {i // f i = t} → Fin q) Subtype.val_injective))⟩

private theorem blockMultiplicity_range_card (q b : ℕ) :
    Nat.card (Set.range (blockMultiplicity (q := q) (m := b + 2))) ≤
      (q + 1) ^ catalan (b + 1) := by
  have h := Nat.card_le_card_of_injective
    (Subtype.val : Set.range (blockMultiplicity (q := q) (m := b + 2)) → _) Subtype.val_injective
  rwa [Nat.card_fun, Nat.card_fin, fullBlockCard] at h

private theorem exists_large_iso_class (n b : ℕ) :
    ∃ I : Stable n, catalan (b + 1) ^ (n / (b + 2)) ≤
      (n / (b + 2) + 1) ^ catalan (b + 1) * Nat.card {J : Stable n // GameIso I J} := by
  classical
  let q := n / (b + 2)
  let Family := Set.range (registeredBoard n b)
  let Vector := FullBlock (b + 2) → Fin (q + 1)
  let tuple : Family ≃ (Fin q → FullBlock (b + 2)) :=
    (Equiv.ofInjective _ (registeredBoard_injective n b)).symm
  let code : Family → Vector := fun J => blockMultiplicity (tuple J)
  let _ : Fintype Family := Fintype.ofFinite _
  let vectors := Finset.univ.image code
  have hcard : Nat.card Family = catalan (b + 1) ^ q := registeredBoard_card n b
  have hvectors : vectors.Nonempty := by
    let t : FullBlock (b + 2) := (fullBlockEquiv b).symm (emptyStable b)
    let J : Family := ⟨registeredBoard n b (fun _ => t), ⟨fun _ => t, rfl⟩⟩
    exact ⟨code J, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let fiber (v : Vector) := Finset.univ.filter (fun J : Family => code J = v)
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image vectors (fun v => (fiber v).card) hvectors
  obtain ⟨I, _, hI⟩ := Finset.mem_image.mp hv
  have hvbound : vectors.card ≤ (q + 1) ^ catalan (b + 1) := by
    have hs : ∀ v ∈ vectors, v ∈ Set.range (blockMultiplicity (q := q) (m := b + 2)) := by
      intro w hw
      obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨tuple J, rfl⟩
    rw [← Nat.card_eq_finsetCard]
    exact (Nat.card_le_card_of_injective
      (fun w : vectors => ⟨w.val, hs w.val w.property⟩)
      (fun _ _ h => Subtype.ext (congrArg
        (fun v : Set.range (blockMultiplicity (q := q) (m := b + 2)) => v.val) h))).trans
        (blockMultiplicity_range_card q b)
  have hfiberIso (J : fiber v) : GameIso I.val J.val.val := by
    have hJ : code J.val = v := (Finset.mem_filter.mp J.property).2
    have hcounts : ∀ t, Nat.card {i // tuple I i = t} = Nat.card {i // tuple J.val i = t} :=
      fun t => congrArg (fun w : Vector => (w t).val) (hI.trans hJ.symm)
    have hIso := registeredBoard_gameIso_of_counts n b hcounts
    change GameIso (((Equiv.ofInjective _ (registeredBoard_injective n b)) (tuple I)).val)
      (((Equiv.ofInjective _ (registeredBoard_injective n b)) (tuple J.val)).val) at hIso
    simpa [tuple] using hIso
  have hfiber : (fiber v).card ≤ Nat.card {J : Stable n // GameIso I.val J} := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_le_card_of_injective (fun J : fiber v => ⟨J.val.val, hfiberIso J⟩)
      (fun _ _ h => Subtype.ext (Subtype.ext
        (congrArg (fun J : {J : Stable n // GameIso I.val J} => J.val) h)))
  refine ⟨I.val, ?_⟩
  calc
    catalan (b + 1) ^ q = Nat.card Family := hcard.symm
    _ = ∑ w ∈ vectors, (fiber w).card := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      exact Finset.card_eq_sum_card_fiberwise (fun J hJ => Finset.mem_image_of_mem code hJ)
    _ ≤ ∑ _w ∈ vectors, (fiber v).card := Finset.sum_le_sum hmax
    _ = vectors.card * (fiber v).card := by simp
    _ ≤ _ := Nat.mul_le_mul hvbound hfiber

/-- The collision event on all ordered pairs of stable positions of width n. -/
abbrev CollisionPairs (n : ℕ) := {p : Stable n × Stable n // GameIso p.1 p.2}

/-- Independent uniform sampling with replacement, expressed as an exact real ratio. -/
noncomputable def collisionProbability (n : ℕ) : ℝ :=
  (Nat.card (CollisionPairs n) : ℝ) / (Nat.card (Stable n) : ℝ) ^ 2

theorem stable_card_pos (n : ℕ) : 0 < Nat.card (Stable n) := by
  let _ : Nonempty (Stable n) := ⟨emptyStable n⟩
  exact Nat.card_pos

private theorem collisionProbability_le_one (n : ℕ) : collisionProbability n ≤ 1 := by
  have h := Nat.card_le_card_of_injective
    (Subtype.val : CollisionPairs n → Stable n × Stable n) Subtype.val_injective
  rw [Nat.card_prod, ← pow_two] at h
  have hpos : 0 < (Nat.card (Stable n) : ℝ) := by exact_mod_cast stable_card_pos n
  exact (div_le_one (by positivity)).2 (by exact_mod_cast h)

private theorem collisionProbability_lower (n b : ℕ) :
    ((catalan (b + 1) : ℝ) ^ (n / (b + 2)) /
      (((n / (b + 2) : ℕ) : ℝ) + 1) ^ catalan (b + 1) / (catalan (n + 1) : ℝ)) ^ 2 ≤
      collisionProbability n := by
  obtain ⟨I, hI⟩ := exists_large_iso_class n b
  let Class := {J : Stable n // GameIso I J}
  have hpairs : Nat.card Class ^ 2 ≤ Nat.card (CollisionPairs n) := by
    rw [pow_two, ← Nat.card_prod]
    exact Nat.card_le_card_of_injective
      (fun p : Class × Class => ⟨(p.1.val, p.2.val),
        gameIso_trans _ _ _ (gameIso_symm _ _ p.1.property) p.2.property⟩)
      (fun _ _ h => Prod.ext
        (Subtype.ext (congrArg (fun p : CollisionPairs n => p.val.1) h))
        (Subtype.ext (congrArg (fun p : CollisionPairs n => p.val.2) h)))
  have hcast : (catalan (b + 1) : ℝ) ^ (n / (b + 2)) ≤
      (((n / (b + 2) : ℕ) : ℝ) + 1) ^ catalan (b + 1) * (Nat.card Class : ℝ) := by
    exact_mod_cast hI
  have hclass : (catalan (b + 1) : ℝ) ^ (n / (b + 2)) /
      (((n / (b + 2) : ℕ) : ℝ) + 1) ^ catalan (b + 1) ≤ (Nat.card Class : ℝ) :=
    (div_le_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hcast)
  have hpos : 0 < (catalan (n + 1) : ℝ) := by
    rw [← stableCard]
    exact_mod_cast stable_card_pos n
  rw [collisionProbability, stableCard]
  calc
    _ ≤ ((Nat.card Class : ℝ) / (catalan (n + 1) : ℝ)) ^ 2 := by
      gcongr
    _ ≤ _ := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hpairs) (by positivity)

end

section

open Filter Topology

private theorem catalan_le_four_pow (k : ℕ) : catalan k ≤ 4 ^ k :=
  (Nat.le_mul_of_pos_left _ (Nat.succ_pos k)).trans
    ((succ_mul_catalan_eq_centralBinom k).le.trans (Nat.centralBinom_le_four_pow k))

private theorem four_pow_le_catalan_mul (k : ℕ) : 4 ^ k ≤ (k + 1) ^ 3 * catalan k := by
  calc
    4 ^ k = 2 ^ (2 * k) := by rw [pow_mul]; rfl
    _ = ∑ j ∈ Finset.range (2 * k + 1), (2 * k).choose j := (Nat.sum_range_choose _).symm
    _ ≤ ∑ _j ∈ Finset.range (2 * k + 1), k.centralBinom :=
      Finset.sum_le_sum fun j _ => Nat.choose_le_centralBinom j k
    _ = (2 * k + 1) * (k + 1) * catalan k := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id,
        ← succ_mul_catalan_eq_centralBinom, mul_assoc]
    _ ≤ _ := by
      apply Nat.mul_le_mul_right
      have h : 2 * k + 1 ≤ (k + 1) ^ 2 := by nlinarith
      calc
        (2 * k + 1) * (k + 1) ≤ (k + 1) ^ 2 * (k + 1) := Nat.mul_le_mul_right _ h
        _ = (k + 1) ^ 3 := (pow_succ (k + 1) 2).symm

private theorem catalan_one_le (b : ℕ) : (1 : ℝ) ≤ (catalan (b + 1) : ℝ) := by
  exact_mod_cast (show 0 < catalan (b + 1) by rw [← stableCard]; exact stable_card_pos b)

private theorem tendsto_linear_root (a c : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + c) ^ (a / (n : ℝ))) atTop (𝓝 1) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + c) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using (tendsto_rpow_div_mul_add a 1 (-c) zero_ne_one).comp hcast

private theorem tendsto_nat_inv :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/-- A lower bound on the nth root at fixed block width b+2, using q ≤ n and q > n/(b+2)-1. -/
private noncomputable def fixedBlockRootLower (b n : ℕ) : ℝ :=
  (((catalan (b + 1) : ℝ) ^ ((1 : ℝ) / ((b : ℝ) + 2) - (n : ℝ)⁻¹)) /
    (((n : ℝ) + 1) ^ ((catalan (b + 1) : ℝ) / (n : ℝ)) *
      (4 : ℝ) ^ (1 + (n : ℝ)⁻¹))) ^ 2

private theorem fixedBlockRootLower_le (n b : ℕ) (hn : 0 < n) :
    fixedBlockRootLower b n ≤ (collisionProbability n) ^ ((n : ℝ)⁻¹) := by
  let q := n / (b + 2)
  let D := catalan (b + 1)
  let e := (n : ℝ)⁻¹
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 < e := inv_pos.mpr hnR
  have hD : (1 : ℝ) ≤ (D : ℝ) := catalan_one_le b
  have hm : (0 : ℝ) < (b : ℝ) + 2 := by positivity
  have hq : n < (q + 1) * (b + 2) := by
    have hr := Nat.mod_lt n (show 0 < b + 2 by omega)
    rw [Nat.add_mul, Nat.one_mul]
    have hd := width_decomp n b
    change q * (b + 2) + n % (b + 2) = n at hd
    omega
  have hqR : (n : ℝ) < ((q : ℝ) + 1) * ((b : ℝ) + 2) := by exact_mod_cast hq
  have hfloor : 1 / ((b : ℝ) + 2) - e ≤ (q : ℝ) * e := by
    have h := (div_lt_iff₀ hm).2 hqR
    rw [sub_le_iff_le_add, ← add_one_mul]
    change 1 / ((b : ℝ) + 2) ≤ ((q : ℝ) + 1) * (n : ℝ)⁻¹
    rw [← div_eq_mul_inv, le_div_iff₀ hnR]
    calc
      1 / ((b : ℝ) + 2) * (n : ℝ) = (n : ℝ) / ((b : ℝ) + 2) := by ring
      _ ≤ (q : ℝ) + 1 := h.le
  have hqle : (q : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n (b + 2)
  have hC : (0 : ℝ) < (catalan (n + 1) : ℝ) := by
    rw [← stableCard]
    exact_mod_cast stable_card_pos n
  have hCmax : (catalan (n + 1) : ℝ) ≤ (4 : ℝ) ^ (n + 1) := by
    exact_mod_cast catalan_le_four_pow (n + 1)
  have hbase :
      (D : ℝ) ^ (1 / ((b : ℝ) + 2) - e) / (((n : ℝ) + 1) ^ ((D : ℝ) / n) *
        (4 : ℝ) ^ (1 + e)) ≤
      ((D : ℝ) ^ q / (((q : ℝ) + 1) ^ D) / (catalan (n + 1) : ℝ)) ^ e := by
    rw [div_div, Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
      (by positivity), ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ (D : ℝ)),
      ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1)]
    have hden : (((q : ℝ) + 1) ^ ((D : ℝ) * e)) * (catalan (n + 1) : ℝ) ^ e ≤
        (((n : ℝ) + 1) ^ ((D : ℝ) / n)) * (4 : ℝ) ^ (1 + e) := by
      apply mul_le_mul
      · rw [div_eq_mul_inv]
        exact Real.rpow_le_rpow (by positivity) (by linarith) (mul_nonneg (by positivity) he.le)
      · calc
          (catalan (n + 1) : ℝ) ^ e ≤ ((4 : ℝ) ^ (n + 1)) ^ e :=
            Real.rpow_le_rpow hC.le hCmax he.le
          _ = (4 : ℝ) ^ (1 + e) := by
            rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 4)]
            congr 1
            simp only [Nat.cast_add, Nat.cast_one]
            dsimp only [e]
            field_simp
      · positivity
      · positivity
    exact (div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hD hfloor)
      (by positivity)).trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
  calc
    fixedBlockRootLower b n ≤
        (((D : ℝ) ^ q / (((q : ℝ) + 1) ^ D) / (catalan (n + 1) : ℝ)) ^ e) ^ 2 := by
      unfold fixedBlockRootLower
      exact pow_le_pow_left₀ (by positivity) hbase _
    _ = (((D : ℝ) ^ q / (((q : ℝ) + 1) ^ D) / (catalan (n + 1) : ℝ)) ^ 2) ^ e := by
      rw [← Real.rpow_mul_natCast (by positivity), ← Real.rpow_natCast_mul (by positivity), mul_comm]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) (collisionProbability_lower n b) he.le

private theorem tendsto_fixedBlockRootLower (b : ℕ) :
    Tendsto (fixedBlockRootLower b) atTop
      (𝓝 (((catalan (b + 1) : ℝ) ^ (1 / ((b : ℝ) + 2)) / 4) ^ 2)) := by
  have hD := catalan_one_le b
  unfold fixedBlockRootLower
  have hnum : Tendsto (fun n : ℕ => (catalan (b + 1) : ℝ) ^
      (1 / ((b : ℝ) + 2) - (n : ℝ)⁻¹)) atTop
      (𝓝 ((catalan (b + 1) : ℝ) ^ (1 / ((b : ℝ) + 2)))) := by
    exact (Real.continuousAt_const_rpow (by positivity)).tendsto.comp
      (by simpa only [sub_zero] using tendsto_const_nhds.sub tendsto_nat_inv)
  have h4 : Tendsto (fun n : ℕ => (4 : ℝ) ^ (1 + (n : ℝ)⁻¹)) atTop (𝓝 4) := by
    simpa only [Function.comp_def, Real.rpow_one] using
      (Real.continuousAt_const_rpow (a := 4) (b := 1) (by norm_num)).tendsto.comp
      (by simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_nat_inv)
  have hden := (tendsto_linear_root (catalan (b + 1) : ℝ) 1).mul h4
  simpa only [Pi.div_apply, one_mul] using
    (hnum.div hden (by norm_num)).pow 2

private theorem tendsto_four_block_root :
    Tendsto (fun b : ℕ => (4 : ℝ) ^ (((b : ℝ) + 1) / ((b : ℝ) + 2))) atTop (𝓝 4) := by
  have hcast : Tendsto (fun b : ℕ => (b : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun b : ℕ => ((b : ℝ) + 1) / ((b : ℝ) + 2)) atTop (𝓝 1) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.comp hcast) using 1
    · ext b
      simp only [Function.comp_def]
      have hb : (0 : ℝ) < (b : ℝ) + 2 := by positivity
      field_simp
      ring
    · simp
  simpa only [Function.comp_def, Real.rpow_one] using
    (Real.continuousAt_const_rpow (a := 4) (b := 1) (by norm_num)).tendsto.comp hexp

private theorem tendsto_catalan_block_root :
    Tendsto (fun b : ℕ => (catalan (b + 1) : ℝ) ^ (1 / ((b : ℝ) + 2))) atTop (𝓝 4) := by
  let upper (b : ℕ) := (4 : ℝ) ^ (((b : ℝ) + 1) / ((b : ℝ) + 2))
  let poly (b : ℕ) := ((b : ℝ) + 2) ^ ((3 : ℝ) / ((b : ℝ) + 2))
  have hcast : Tendsto (fun b : ℕ => (b : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hpoly : Tendsto poly atTop (𝓝 1) := by
    simpa [poly, Function.comp_def] using
      (tendsto_rpow_div_mul_add 3 1 0 zero_ne_one).comp hcast
  have hu : Tendsto upper atTop (𝓝 4) := tendsto_four_block_root
  have hl : Tendsto (fun b => upper b / poly b) atTop (𝓝 4) := by
    simpa only [Pi.div_def, div_one] using hu.div hpoly one_ne_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro b
    have h : (4 : ℝ) ^ (b + 1) ≤ ((b : ℝ) + 2) ^ 3 * (catalan (b + 1) : ℝ) := by
      exact_mod_cast (by simpa only [Nat.add_assoc] using four_pow_le_catalan_mul (b + 1) :
        (4 : ℕ) ^ (b + 1) ≤ (b + 2) ^ 3 * catalan (b + 1))
    have hh := Real.rpow_le_rpow (by positivity) h (by positivity : 0 ≤ 1 / ((b : ℝ) + 2))
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by norm_num),
      ← Real.rpow_natCast_mul (by positivity)] at hh
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, mul_one_div] at hh
    exact (div_le_iff₀ (by positivity : 0 < poly b)).2 (by simpa [upper, poly, mul_comm] using hh)
  · intro b
    have h : (catalan (b + 1) : ℝ) ≤ (4 : ℝ) ^ (b + 1) := by
      exact_mod_cast catalan_le_four_pow (b + 1)
    have hh := Real.rpow_le_rpow (by positivity) h (by positivity : 0 ≤ 1 / ((b : ℝ) + 2))
    rw [← Real.rpow_natCast_mul (by norm_num)] at hh
    simpa [upper, div_eq_mul_inv, mul_one_div] using hh

/-- The nth root of the collision probability tends to one along all positive widths. -/
theorem tendsto_collisionProbability_root :
    Tendsto (fun n : ℕ => (collisionProbability n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hrate : Tendsto (fun b : ℕ => ((catalan (b + 1) : ℝ) ^
      (1 / ((b : ℝ) + 2)) / 4) ^ 2) atTop (𝓝 1) := by
    convert (tendsto_catalan_block_root.div_const 4).pow 2 using 1
    norm_num
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨b, hb⟩ := (hrate.eventually (lt_mem_nhds ha)).exists
    have hfixed := (tendsto_fixedBlockRootLower b).eventually (lt_mem_nhds hb)
    filter_upwards [hfixed, eventually_ge_atTop (1 : ℕ)] with n hn hpos
    exact hn.trans_le (fixedBlockRootLower_le n b hpos)
  · intro a ha
    apply Filter.Eventually.of_forall
    intro n
    apply lt_of_le_of_lt _ ha
    exact Real.rpow_le_one (by unfold collisionProbability; positivity)
      (collisionProbability_le_one n) (by positivity)

end

section

open Filter Topology

abbrev DistinctPairs (n : ℕ) := {p : Stable n × Stable n // p.1 ≠ p.2}

abbrev DistinctCollisionPairs (n : ℕ) := {p : CollisionPairs n // p.val.1 ≠ p.val.2}

/-- Uniform sampling from ordered pairs of distinct stable positions. -/
noncomputable def distinctCollisionProbability (n : ℕ) : ℝ :=
  (Nat.card (DistinctCollisionPairs n) : ℝ) / (Nat.card (DistinctPairs n) : ℝ)

private def diagonalEquiv (n : ℕ) :
    Stable n ≃ {p : Stable n × Stable n // p.1 = p.2} where
  toFun I := ⟨(I, I), rfl⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl p.property)

private def collisionDiagonalEquiv (n : ℕ) :
    Stable n ≃ {p : CollisionPairs n // p.val.1 = p.val.2} where
  toFun I := ⟨⟨(I, I), gameIso_refl I⟩, rfl⟩
  invFun p := p.val.val.1
  left_inv _ := rfl
  right_inv p := Subtype.ext (Subtype.ext (Prod.ext rfl p.property))

private theorem distinctPairs_card_add (n : ℕ) :
    Nat.card (Stable n) + Nat.card (DistinctPairs n) = Nat.card (Stable n) ^ 2 := by
  classical
  rw [pow_two, ← Nat.card_prod, Nat.card_congr (diagonalEquiv n), ← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl (fun p : Stable n × Stable n => p.1 = p.2))

private theorem distinctCollisionPairs_card_add (n : ℕ) :
    Nat.card (Stable n) + Nat.card (DistinctCollisionPairs n) = Nat.card (CollisionPairs n) := by
  classical
  rw [Nat.card_congr (collisionDiagonalEquiv n), ← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl (fun p : CollisionPairs n => p.val.1 = p.val.2))

theorem distinctCollisionProbability_eq (n : ℕ) (hn : 1 < Nat.card (Stable n)) :
    distinctCollisionProbability n =
      ((Nat.card (Stable n) : ℝ) * collisionProbability n - 1) /
        ((Nat.card (Stable n) : ℝ) - 1) := by
  let N := (Nat.card (Stable n) : ℝ)
  have hN : 1 < N := by
    dsimp only [N]
    exact_mod_cast hn
  have hpairs : N + (Nat.card (DistinctPairs n) : ℝ) = N ^ 2 := by
    dsimp only [N]
    exact_mod_cast distinctPairs_card_add n
  have hcoll : N + (Nat.card (DistinctCollisionPairs n) : ℝ) =
      (Nat.card (CollisionPairs n) : ℝ) := by
    dsimp only [N]
    exact_mod_cast distinctCollisionPairs_card_add n
  have hd : (Nat.card (DistinctPairs n) : ℝ) = N * (N - 1) := by linarith
  have hc : (Nat.card (DistinctCollisionPairs n) : ℝ) = (Nat.card (CollisionPairs n) : ℝ) - N := by
    linarith
  have hNpos : 0 < N := by linarith
  have hsub : 0 < N - 1 := by linarith
  unfold distinctCollisionProbability collisionProbability
  change _ = (N * (_ / N ^ 2) - 1) / (N - 1)
  rw [hd, hc]
  field_simp

private theorem distinctCollisionProbability_nonneg (n : ℕ) :
    0 ≤ distinctCollisionProbability n := by
  unfold distinctCollisionProbability
  positivity

private theorem distinctCollisionProbability_le (n : ℕ) (hn : 1 < Nat.card (Stable n)) :
    distinctCollisionProbability n ≤ collisionProbability n := by
  have hN : (1 : ℝ) < Nat.card (Stable n) := by exact_mod_cast hn
  rw [distinctCollisionProbability_eq n hn, div_le_iff₀ (sub_pos.2 hN)]
  have h := collisionProbability_le_one n
  linarith

private theorem two_pow_le_stable_card (n : ℕ) : 2 ^ n ≤ Nat.card (Stable n) := by
  rw [stableCard]
  induction n with
  | zero => simp [catalan_one]
  | succ n ih =>
    let a : Fin (n + 2) := 0
    let z : Fin (n + 2) := Fin.last (n + 1)
    have hne : a ≠ z := by
      intro h
      have hv := congrArg Fin.val h
      change 0 = n + 1 at hv
      omega
    have hsum : catalan (n + 1) + catalan (n + 1) ≤ catalan (n + 1 + 1) := by
      rw [catalan_succ (n + 1)]
      let weight (i : Fin (n + 2)) := catalan (i : ℕ) * catalan (n + 1 - (i : ℕ))
      have h : ∑ i ∈ ({a, z} : Finset (Fin (n + 2))), weight i ≤ ∑ i, weight i :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      simpa only [Finset.sum_pair hne, weight, a, z, Fin.val_zero, Fin.val_last,
        Nat.sub_zero, Nat.sub_self, catalan_zero, one_mul, mul_one] using h
    rw [pow_succ, Nat.mul_two]
    exact (Nat.add_le_add ih ih).trans hsum

private theorem stable_card_gt_one (n : ℕ) (hn : 0 < n) : 1 < Nat.card (Stable n) :=
  (one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (Nat.ne_of_gt hn)).trans_le (two_pow_le_stable_card n)

/-- With high enough width, the diagonal contributes at most half of the collision mass. -/
private theorem eventually_half_collision_le_distinct :
    ∀ᶠ n : ℕ in atTop, collisionProbability n / 2 ≤ distinctCollisionProbability n := by
  have hroot := tendsto_collisionProbability_root.eventually
    (lt_mem_nhds (by norm_num : (3 : ℝ) / 4 < 1))
  filter_upwards [hroot, eventually_ge_atTop (2 : ℕ)] with n hroot hn
  have hn' : 0 < n := by omega
  let N := (Nat.card (Stable n) : ℝ)
  have hsize : (2 : ℝ) ^ n ≤ N := by
    dsimp only [N]
    exact_mod_cast two_pow_le_stable_card n
  have hN₀ : 0 < N := lt_of_lt_of_le (by positivity) hsize
  have hN : 1 < N := by
    dsimp only [N]
    exact_mod_cast stable_card_gt_one n hn'
  have hp : 0 ≤ collisionProbability n := by unfold collisionProbability; positivity
  have hp₀ : ((3 : ℝ) / 4) ^ n ≤ collisionProbability n := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hroot.le n
    rwa [Real.rpow_inv_natCast_pow hp (by exact_mod_cast Nat.ne_of_gt hn')] at hpow
  have hbase : (2 : ℝ) ≤ ((3 : ℝ) / 2) ^ n := by
    calc
      (2 : ℝ) ≤ ((3 : ℝ) / 2) ^ (2 : ℕ) := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hn
  have hmass : 2 ≤ N * collisionProbability n := by
    calc
      (2 : ℝ) ≤ ((3 : ℝ) / 2) ^ n := hbase
      _ = (2 : ℝ) ^ n * ((3 : ℝ) / 4) ^ n := by
        rw [← mul_pow]
        norm_num
      _ ≤ _ := mul_le_mul hsize hp₀ (by positivity) hN₀.le
  rw [distinctCollisionProbability_eq n (stable_card_gt_one n hn'), le_div_iff₀ (sub_pos.2 hN)]
  change collisionProbability n / 2 * (N - 1) ≤ N * collisionProbability n - 1
  nlinarith only [hmass, hp]

/-- The nth-root limit also holds for uniform distinct ordered pairs. -/
theorem tendsto_distinctCollisionProbability_root :
    Tendsto (fun n : ℕ => (distinctCollisionProbability n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
  have htwoExp : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have htwo : Tendsto (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.rpow_zero] using
      (Real.continuousAt_const_rpow (a := 2) (b := 0) (by norm_num)).tendsto.comp htwoExp
  have hl : Tendsto (fun n : ℕ => (collisionProbability n / 2) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hquot := tendsto_collisionProbability_root.div htwo one_ne_zero
    rw [div_one] at hquot
    apply hquot.congr
    intro n
    change (collisionProbability n) ^ ((n : ℝ)⁻¹) / (2 : ℝ) ^ ((n : ℝ)⁻¹) =
      (collisionProbability n / 2) ^ ((n : ℝ)⁻¹)
    rw [Real.div_rpow (by unfold collisionProbability; positivity) (by norm_num : (0 : ℝ) ≤ 2)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_collisionProbability_root
  · filter_upwards [eventually_half_collision_le_distinct] with n hn
    exact Real.rpow_le_rpow (by unfold collisionProbability; positivity) hn (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact Real.rpow_le_rpow (distinctCollisionProbability_nonneg n)
      (distinctCollisionProbability_le n (stable_card_gt_one n hn)) (by positivity)

/-- Decay to zero transfers to distinct pairs if established for independent sampling. -/
theorem tendsto_distinctCollisionProbability_zero_of
    (h : Tendsto collisionProbability atTop (𝓝 0)) :
    Tendsto distinctCollisionProbability atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · exact Filter.Eventually.of_forall distinctCollisionProbability_nonneg
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact distinctCollisionProbability_le n (stable_card_gt_one n hn)

end

end D5.S3.Combinatorics.Games.Pyranim
