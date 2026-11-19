/- GID: D5/S3/Combinatorics/Graph/LinearForests/UndirectedCycleCompletionLaw
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/UndirectedCycleCompletionLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform lifts give uniform undirected cycle completions. -/

import D5.S3.Combinatorics.Graph.Brooks.General
import D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch
import D5.S0.Diagonal.Probability.EquivariantEscape
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.GroupTheory.Perm.Fin

/-! Uniform transport through the two actual orientations of each undirected cycle. -/

namespace D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw

open SimpleGraph Equiv Equiv.Perm
open D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch (same_cycle_perm_congr)

variable {V : Type*} [Fintype V]

open Classical in
private theorem raw_cycle_permutation (C : SimpleGraph V) [DecidableRel C.Adj]
    (hconn : C.Connected) (hdegree : ∀ v, C.degree v = 2) :
    ∃ σ : Perm V, σ.IsCycleOn Set.univ ∧
      ∀ u v, C.Adj u v ↔ σ u = v ∨ σ v = u := by
  classical
  have hcyc : C.IsCycles := by
    intro v _
    rw [ncard_neighborSet, hdegree]
  let v := hconn.nonempty.some
  have hv : (C.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [ncard_neighborSet, hdegree]
    decide
  obtain ⟨p, hp, _⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := C.connectedComponentMk v) (by simp) hv
  have hmax : C.maxDegree ≤ 2 :=
    C.maxDegree_le_of_forall_degree_le 2 (fun w => le_of_eq (hdegree w))
  have hn : 2 ≤ p.length := by have := hp.three_le_length; omega
  obtain ⟨m, hm⟩ : ∃ m, p.length = m + 2 := ⟨p.length - 2, (Nat.sub_add_cancel hn).symm⟩
  have hiso := C.cycle_iso_of_connected_degree_le_two hconn hmax p hp
  rw [hm] at hiso
  obtain ⟨e⟩ := hiso
  let ρ : Perm (Fin (m + 2)) := finRotate (m + 2)
  let σ := e.toEquiv.permCongr ρ
  have hρ : ρ.IsCycleOn Set.univ := by
    have hf := (@isCycle_finRotate m).isCycleOn
    change ρ.IsCycleOn {x | ρ x ≠ x} at hf
    convert hf using 1
    ext x
    simp [ρ]
  have hσ : σ.IsCycleOn Set.univ := by
    refine ⟨by simp, ?_⟩
    intro a _ b _
    obtain ⟨a, rfl⟩ := e.toEquiv.surjective a
    obtain ⟨b, rfl⟩ := e.toEquiv.surjective b
    exact (same_cycle_perm_congr e.toEquiv ρ a b).mpr (hρ.2 (Set.mem_univ a) (Set.mem_univ b))
  refine ⟨σ, hσ, ?_⟩
  intro a b
  obtain ⟨i, rfl⟩ := e.toEquiv.surjective a
  obtain ⟨j, rfl⟩ := e.toEquiv.surjective b
  change C.Adj (e i) (e j) ↔ σ (e.toEquiv i) = e.toEquiv j ∨ σ (e.toEquiv j) = e.toEquiv i
  rw [e.map_rel_iff]
  simp only [σ, Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq]
  dsimp only [ρ]
  rw [cycleGraph_adj, finRotate_apply i, finRotate_apply j]
  constructor
  · rintro (h | h)
    · exact Or.inr (by simpa [add_comm] using (sub_eq_iff_eq_add.mp h).symm)
    · exact Or.inl (by simpa [add_comm] using (sub_eq_iff_eq_add.mp h).symm)
  · rintro (h | h)
    · exact Or.inr (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h.symm))
    · exact Or.inl (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h.symm))

private theorem no_short_cycle (hn : 3 ≤ Fintype.card V) (σ : Perm V)
    (hσ : σ.IsCycleOn Set.univ) (v : V) : σ v ≠ v ∧ σ (σ v) ≠ v := by
  have hf : σ.IsCycleOn (↑(Finset.univ : Finset V)) := by simpa using hσ
  constructor
  · intro h
    have hh := (hf.pow_apply_eq (Finset.mem_univ v) (n := 1)).mp (by simpa using h)
    simp only [Finset.card_univ] at hh
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) hh
  · intro h
    have hh := (hf.pow_apply_eq (Finset.mem_univ v) (n := 2)).mp (by simpa [pow_two] using h)
    simp only [Finset.card_univ] at hh
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) hh

omit [Fintype V] in
private theorem equal_from_one_edge [Finite V] (σ τ : Perm V)
    (hτ : τ.IsCycleOn Set.univ) (hσ₂ : ∀ x, σ (σ x) ≠ x)
    (hstep : ∀ x, σ x = τ x ∨ τ (σ x) = x)
    {x₀ : V} (h₀ : σ x₀ = τ x₀) : σ = τ := by
  have hpropagate (x : V) (hx : σ x = τ x) : σ (τ x) = τ (τ x) := by
    rcases hstep (τ x) with hy | hy
    · exact hy
    · exact (hσ₂ x (hx ▸ τ.injective hy)).elim
  have hpow (n : ℕ) : σ ((τ ^ n) x₀) = τ ((τ ^ n) x₀) := by
    induction n with
    | zero => simpa using h₀
    | succ n ih => simpa only [pow_succ', Perm.mul_apply] using hpropagate _ ih
  ext x
  obtain ⟨n, rfl⟩ := hτ.exists_pow_eq' (Set.toFinite _) (Set.mem_univ x₀) (Set.mem_univ x)
  exact hpow n

def shadow (σ : Perm V) : SimpleGraph V := SimpleGraph.fromRel (fun x y => σ x = y)

theorem shadow_adj (hn : 3 ≤ Fintype.card V) (σ : Perm V)
    (hσ : σ.IsCycleOn Set.univ) (x y : V) :
    (shadow σ).Adj x y ↔ σ x = y ∨ σ y = x := by
  rw [shadow, SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    rintro rfl
    exact (no_short_cycle hn σ hσ x).1 (h.elim id id)

private theorem shadow_cycle (hn : 3 ≤ Fintype.card V) (σ : Perm V)
    (hσ : σ.IsCycleOn Set.univ) :
    (shadow σ).Connected ∧ ∀ v, ((shadow σ).neighborSet v).ncard = 2 := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hstep (v : V) : (shadow σ).Adj v (σ v) :=
    (shadow_adj hn σ hσ _ _).mpr (Or.inl rfl)
  have hconn : (shadow σ).Connected := by
    let : Nonempty V := hne
    apply Connected.mk
    intro a b
    obtain ⟨n,hnat⟩ := (hσ.2 (Set.mem_univ a) (Set.mem_univ b)).exists_nat_pow_eq
    have hi : Function.Semiconj (shadow σ).connectedComponentMk σ id := by
      intro v
      exact ConnectedComponent.sound (hstep v).reachable.symm
    have he := hi.iterate_right n a
    simp only [Perm.iterate_eq_pow, Function.iterate_id,id_eq,hnat] at he
    exact (ConnectedComponent.eq.mp he).symm
  refine ⟨hconn, fun v => ?_⟩
  have hdiff : σ v ≠ σ⁻¹ v := by
    intro h
    apply (no_short_cycle hn σ hσ v).2
    simpa using congrArg σ h
  have hset : (shadow σ).neighborSet v = {σ v,σ⁻¹ v} := by
    ext w
    rw [mem_neighborSet, shadow_adj hn σ hσ]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · right
        simpa using congrArg (fun v => σ⁻¹ v) h
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (by simp)
  have hcard : ((shadow σ).neighborSet v).ncard = 2 := by
    change σ v ≠ σ.symm v at hdiff
    rw [hset]
    simp [hdiff]
  exact hcard

structure Lift (F : SimpleGraph V) where
  E : V → V → Prop
  σ : Perm V
  edge : ∀ x y, E x y → F.Adj x y
  orient : ∀ x y, F.Adj x y → E x y ∨ E y x
  antisymm : ∀ x y, E x y → ¬ E y x
  outgoing : Relator.RightUnique E
  incoming : Relator.LeftUnique E
  full : σ.IsCycleOn Set.univ
  extension : ∀ x y, E x y → σ x = y

def reverseLift {F : SimpleGraph V} (l : Lift F) : Lift F where
  E x y := l.E y x
  σ := l.σ⁻¹
  edge x y h := (l.edge y x h).symm
  orient x y h := (l.orient y x h.symm)
  antisymm x y h := l.antisymm y x h
  outgoing _ _ _ h h' := l.incoming h h'
  incoming _ _ _ h h' := l.outgoing h h'
  full := l.full.inv
  extension x y h := by
    have he := l.extension y x h
    simpa using (congrArg (fun v => l.σ⁻¹ v) he).symm

private theorem forced_orientation {F : SimpleGraph V} (hn : 3 ≤ Fintype.card V)
    (l : Lift F) (x y : V) : l.E x y ↔ F.Adj x y ∧ l.σ x = y := by
  constructor
  · exact fun h => ⟨l.edge _ _ h,l.extension _ _ h⟩
  · rintro ⟨hf,hs⟩
    rcases l.orient x y hf with h | h
    · exact h
    · have hr := l.extension _ _ h
      exact ((no_short_cycle hn l.σ l.full x).2 (by rw [hs,hr])).elim

theorem lift_ext {F : SimpleGraph V} (hn : 3 ≤ Fintype.card V)
    {a b : Lift F} (h : a.σ = b.σ) : a = b := by
  have he : a.E = b.E := by
    funext x y
    apply propext
    rw [forced_orientation hn a, forced_orientation hn b,h]
  cases a
  cases b
  cases h
  cases he
  rfl

private def canonicalLift (hn : 3 ≤ Fintype.card V) (F : SimpleGraph V)
    (σ : Perm V) (hf : σ.IsCycleOn Set.univ)
    (he : ∀ x y, F.Adj x y → σ x = y ∨ σ y = x) : Lift F where
  E x y := F.Adj x y ∧ σ x = y
  σ := σ
  edge _ _ h := h.1
  orient x y h := by
    rcases he x y h with hσ | hσ
    · exact Or.inl ⟨h,hσ⟩
    · exact Or.inr ⟨h.symm,hσ⟩
  antisymm x y h h' := (no_short_cycle hn σ hf x).2 (by rw [h.2,h'.2])
  outgoing _ _ _ h h' := h.2.symm.trans h'.2
  incoming _ _ _ h h' := σ.injective (h.2.trans h'.2.symm)
  full := hf
  extension _ _ h := h.2

theorem reverse_distinct {F : SimpleGraph V} (hn : 3 ≤ Fintype.card V)
    (l : Lift F) : l ≠ reverseLift l := by
  intro h
  have he := congrArg Lift.σ h
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hne
  apply (no_short_cycle hn l.σ l.full v).2
  have he' := congrArg (fun σ : Perm V => σ v) he
  change l.σ v = l.σ⁻¹ v at he'
  simpa using congrArg l.σ he'

abbrev CompletedGraph (F : SimpleGraph V) :=
  {C : SimpleGraph V // C.Connected ∧ (∀ v, (C.neighborSet v).ncard = 2) ∧ F ≤ C}

def forget (hn : 3 ≤ Fintype.card V) {F : SimpleGraph V}
    (l : Lift F) : CompletedGraph F :=
  ⟨shadow l.σ, (shadow_cycle hn l.σ l.full).1,
    (shadow_cycle hn l.σ l.full).2,
    fun x y h => (shadow_adj hn l.σ l.full x y).mpr
      ((l.orient x y h).elim (fun he => Or.inl (l.extension _ _ he))
        (fun he => Or.inr (l.extension _ _ he)))⟩

theorem forget_reverse (hn : 3 ≤ Fintype.card V) {F : SimpleGraph V}
    (l : Lift F) : forget hn (reverseLift l) = forget hn l := by
  apply Subtype.ext
  ext x y
  rw [show (forget hn (reverseLift l)).val = shadow l.σ⁻¹ from rfl,
    show (forget hn l).val = shadow l.σ from rfl,
    shadow_adj hn _ l.full.inv, shadow_adj hn _ l.full]
  simp only [Perm.inv_eq_iff_eq]
  tauto

theorem forget_surjective (hn : 3 ≤ Fintype.card V) (F : SimpleGraph V) :
    Function.Surjective (forget hn (F := F)) := by
  classical
  intro C
  have hd (v : V) : C.val.degree v = 2 := by
    simpa only [ncard_neighborSet] using C.property.2.1 v
  obtain ⟨σ, hσ, hgraph⟩ := raw_cycle_permutation C.val C.property.1 hd
  let l := canonicalLift hn F σ hσ (fun x y h => (hgraph x y).mp (C.property.2.2 h))
  refine ⟨l,Subtype.ext ?_⟩
  ext x y
  exact (shadow_adj hn σ hσ x y).trans (hgraph x y).symm

theorem forget_fiber (hn : 3 ≤ Fintype.card V) {F : SimpleGraph V}
    (a b : Lift F) : forget hn b = forget hn a ↔ b = a ∨ b = reverseLift a := by
  constructor
  · intro h
    have hb (x y : V) : (shadow a.σ).Adj x y ↔ b.σ x = y ∨ b.σ y = x := by
      have hh := congrArg Subtype.val h
      change shadow b.σ = shadow a.σ at hh
      rw [← hh]
      exact shadow_adj hn b.σ b.full x y
    have hs (x : V) : b.σ x = a.σ x ∨ a.σ (b.σ x) = x := by
      have hx := (shadow_adj hn a.σ a.full x (b.σ x)).mp ((hb x _).mpr (Or.inl rfl))
      exact hx.imp Eq.symm id
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    rcases hs x with hx | hx
    · exact Or.inl <| lift_ext hn <|
        equal_from_one_edge b.σ a.σ a.full (fun y => (no_short_cycle hn b.σ b.full y).2) hs hx
    · apply Or.inr
      apply lift_ext hn
      change b.σ = a.σ⁻¹
      refine equal_from_one_edge b.σ a.σ⁻¹ a.full.inv
        (fun y => (no_short_cycle hn b.σ b.full y).2) (x₀ := x) ?_ ?_
      · intro y
        rcases hs y with hy | hy
        · exact Or.inr (by rw [hy]; exact a.σ.symm_apply_apply y)
        · exact Or.inl (a.σ.eq_symm_apply.mpr hy)
      · exact a.σ.eq_symm_apply.mpr hx
  · rintro (rfl | rfl)
    · rfl
    · exact forget_reverse hn a

open scoped ENNReal
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)

private theorem uniform_map_of_two_preimages {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A → B)
    (hf : ∀ b, Nat.card {a : A // f a = b} = 2) :
    (uniformPmf A).map f = uniformPmf B := by
  classical
  let (b : B) : Fintype {a : A // f a = b} := Fintype.ofFinite _
  have hcard (b : B) : Fintype.card {a : A // f a = b} = 2 :=
    Nat.card_eq_fintype_card.symm.trans (hf b)
  have htotal : Fintype.card A = Fintype.card B * 2 := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
    simp [hcard]
  apply PMF.ext
  intro b
  rw [PMF.map_apply]
  simp only [uniformPmf, PMF.ofFintype_apply, tsum_fintype]
  conv_lhs =>
    arg 2
    ext a
    rw [eq_comm (a := b)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, ← Fintype.card_subtype (fun a : A => f a = b), hcard,
    nsmul_eq_mul, htotal, Nat.cast_mul, Nat.cast_ofNat]
  rw [ENNReal.mul_inv (by right; simp) (by right; simp)]
  rw [← mul_assoc, mul_comm 2, mul_assoc]
  rw [ENNReal.mul_inv_cancel (by simp : (2 : ℝ≥0∞) ≠ 0) (by simp), mul_one]

/-- The uniform law on lifts induces the uniform law on completed graphs. -/
theorem uniform_undirected_completion (hn : 3 ≤ Fintype.card V) (F : SimpleGraph V)
    (hF : Nonempty (CompletedGraph F)) :
    ∃ (μ : PMF (Lift F)) (ν : PMF (CompletedGraph F)),
      (∀ l, μ l = (Nat.card (Lift F) : ℝ≥0∞)⁻¹) ∧
      (∀ C, ν C = (Nat.card (CompletedGraph F) : ℝ≥0∞)⁻¹) ∧
      μ.map (forget hn) = ν := by
  classical
  let : Finite (Lift F) := Finite.of_injective (fun l : Lift F => l.σ) (fun _ _ h => lift_ext hn h)
  let : Finite (CompletedGraph F) := Finite.of_surjective _ (forget_surjective hn F)
  let : Fintype (Lift F) := Fintype.ofFinite _
  let : Fintype (CompletedGraph F) := Fintype.ofFinite _
  let : Nonempty (CompletedGraph F) := hF
  let : Nonempty (Lift F) := ⟨(forget_surjective hn F hF.some).choose⟩
  refine ⟨uniformPmf _, uniformPmf _, ?_, ?_, ?_⟩
  · simp [uniformPmf, Nat.card_eq_fintype_card]
  · simp [uniformPmf, Nat.card_eq_fintype_card]
  · apply uniform_map_of_two_preimages
    intro C
    obtain ⟨l, hl⟩ := forget_surjective hn F C
    let pick (b : Bool) : {a : Lift F // forget hn a = C} :=
      if b then ⟨reverseLift l, (forget_reverse hn l).trans hl⟩ else ⟨l, hl⟩
    have hpick : Function.Bijective pick := by
      constructor
      · intro a b h
        cases a <;> cases b
        · rfl
        · exact (reverse_distinct hn l (congrArg Subtype.val h)).elim
        · exact (reverse_distinct hn l (congrArg Subtype.val h).symm).elim
        · rfl
      · intro a
        rcases (forget_fiber hn l a).mp (a.property.trans hl.symm) with ha | ha
        · exact ⟨false, Subtype.ext ha.symm⟩
        · exact ⟨true, Subtype.ext ha.symm⟩
    exact (Nat.card_congr (Equiv.ofBijective pick hpick).symm).trans (by simp)

end D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw
