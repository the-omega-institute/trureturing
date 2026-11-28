import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.PureThreeTreeEmbedding

compile_only_with_mathlib

/-! A maximal-depth deletion recovers a stacking presentation of the
finite replicated history graph. -/
namespace Omega.PureThreeTree

open SimpleGraph Omega.RollingCliques
open StackedTriangleCurvature (Build Face)
noncomputable section

variable {n k : ℕ}
local notation "V" => Vertex n k
local notation "W" => StackedTriangleCurvature.Vertex

def parentVertex (b : History n k) (hb : 0 < b.stage.val) (p : ↥(parents b)) : Vertex n k := by
  classical
  have h := (Finset.mem_filter.mp p.property).2
  refine ⟨(b.prefix p.val.1 h.1.le,p.val.2),?_⟩
  by_cases hz : p.val.1=0
  · exact Or.inl hz
  · right
    exact Finset.mem_singleton.mp ((b.legal _ le_rfl hb).2.2.1 p.val.1
      (Nat.pos_of_ne_zero (fun h => hz (Fin.ext h))) h.1 h.2)

def older (v : Vertex n k) := {u : Vertex n k // depth u < depth v ∧ (graph n k).Adj u v}
instance (v : Vertex n k) : Fintype (older v) := by
  classical
  unfold older
  infer_instance

def olderEquiv (v : Vertex n k) (hv : 0 < depth v) : older v ≃ ↥(parents v.val.1) where
  toFun u := by
    classical
    have h := rolling_earlier data u.property.2 u.property.1.le
    refine ⟨(u.val.val.1.stage,u.val.val.2),Finset.mem_filter.mpr ⟨Finset.mem_univ _,u.property.1,?_⟩⟩
    exact h.2.resolve_left (fun he => u.property.1.ne (congrArg (fun b => b.stage.val) he))
  invFun p := by
    classical
    have hp := (Finset.mem_filter.mp p.property).2
    refine ⟨parentVertex v.val.1 hv p,hp.1,?_⟩
    exact ⟨fun h => hp.1.ne (congrArg (fun z => z.1.stage) h),
      Or.inr (Or.inl ⟨v.val.1.prefix_spec _ hp.1.le,hp.2⟩)⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change v.val.1.prefix u.val.val.1.stage u.property.1.le = u.val.val.1
      apply History.ext' (b := v.val.1.prefix u.val.val.1.stage u.property.1.le) (c := u.val.val.1) rfl
      funext i
      by_cases hi : i ≤ u.val.val.1.stage
      · change (if i ≤ u.val.val.1.stage then v.val.1.step i else _) = _
        rw [ite_eq_left hi]
        exact ((rolling_earlier data u.property.2 u.property.1.le).1.2 i hi).symm
      · change (if i ≤ u.val.val.1.stage then _ else rootStep n 3 k) = _
        rw [ite_eq_right hi,u.val.val.1.beyond i (lt_of_not_ge hi)]
    · rfl
  right_inv p := Subtype.ext rfl

/-- Every inserted vertex has exactly three older neighbours, without an assumed
localization or clique-number contract. -/
theorem older_card (v : Vertex n k) (hv : 0 < depth v) : Fintype.card (older v) = 3 := by
  rw [Fintype.card_congr (olderEquiv v hv),Fintype.card_coe]
  exact parents_card v.val.1 hv

theorem older_clique (v : Vertex n k) :
    (graph n k).IsClique {u | depth u < depth v ∧ (graph n k).Adj u v} := by
  intro a ha b hb hab
  exact rolling_clique data v.val ⟨ha.1.le,ha.2⟩ ⟨hb.1.le,hb.2⟩
    (fun he => hab (Subtype.ext he))

/-- Change copy indices while preserving every face choice. -/

private theorem depth_zero_eq_root {x : V} (h : depth x = 0) : x = root x.val.2 :=
  Subtype.ext (Prod.ext (History.stage_zero (Fin.ext h)) rfl)

private theorem root_injective : Function.Injective (root (n := n) (k := k)) :=
  fun _ _ h => congrArg (fun v : V => v.val.2) h

private theorem parent_selected (S : Finset V)
    (hclose : ∀ {u v : V}, pre u v → v ∈ S → u ∈ S)
    {v : V} (hv : v ∈ S) (u : older v) : u.val ∈ S :=
  hclose (rolling_earlier data u.property.2 u.property.1.le).1 hv

private theorem exists_stacking_on (S : Finset V)
    (hroot : ∀ a : Fin 3, root a ∈ S)
    (hclose : ∀ {u v : V}, pre u v → v ∈ S → u ∈ S) :
    ∃ (m : ℕ) (b : Build m) (f : W m ↪ V),
      Set.range f = (S : Set V) ∧
      ∀ x y, (graph n k).Adj (f x) (f y) ↔ b.graph.Adj x y := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image S depth ⟨root 0,hroot 0⟩
    by_cases hz : depth v = 0
    · let f : W 0 ↪ V := ⟨root,root_injective⟩
      refine ⟨0,Build.root,f,?_,fun x y => ?_⟩
      · ext u
        constructor
        · rintro ⟨a,rfl⟩
          exact hroot a
        · intro hu
          have hu' : depth u = 0 := Nat.eq_zero_of_le_zero (hz ▸ hmax u hu)
          exact ⟨u.val.2, (depth_zero_eq_root hu').symm⟩
      · change (graph n k).Adj (root x) (root y) ↔ x ≠ y
        exact ⟨fun h e => h.ne (congrArg root e),root_adj⟩
    let T := S.erase v
    have hTroot (a : Fin 3) : root a ∈ T :=
      Finset.mem_erase.mpr ⟨fun e => hz (congrArg depth e).symm,hroot a⟩
    have hTclose {x y : V} (h : pre x y) (hy : y ∈ T) : x ∈ T := by
      have hy' := Finset.mem_erase.mp hy
      refine Finset.mem_erase.mpr ⟨?_, hclose h hy'.2⟩
      intro e
      subst x
      have he : v.val.1.stage = y.val.1.stage :=
        Fin.le_antisymm h.1 (hmax _ hy'.2)
      have hh := h.eq_of_stage_eq he
      have hzv := v.property.resolve_left (fun e => hz (congrArg Fin.val e))
      have hzy := y.property.resolve_left (fun e => hz (congrArg Fin.val (he.trans e)))
      exact hy'.1 (Subtype.ext (Prod.ext hh.symm (hzy.trans hzv.symm)))
    obtain ⟨m,b,f,hf,ha⟩ := ih T (Finset.erase_ssubset hv) hTroot hTclose
    have hf_range (x : W m) : f x ∈ T := by
      have h : f x ∈ Set.range f := ⟨x,rfl⟩
      rwa [hf] at h
    have hparent (u : older v) : u.val ∈ T :=
      Finset.mem_erase.mpr ⟨u.property.2.ne,parent_selected S hclose hv u⟩
    let e : older v ≃ Fin 3 := Fintype.equivFinOfCardEq (older_card v (Nat.pos_of_ne_zero hz))
    let par (i : Fin 3) := (e.symm i).val
    have hpa (i : Fin 3) : ∃ x, f x = par i := by
      rw [← Set.mem_range, hf]
      exact hparent (e.symm i)
    let a (i : Fin 3) := (hpa i).choose
    have ea (i : Fin 3) : f (a i) = par i := (hpa i).choose_spec
    have hpair {i j : Fin 3} (hij : i ≠ j) : b.graph.Adj (a i) (a j) := by
      apply (ha _ _).1
      rw [ea,ea]
      exact older_clique v (e.symm i).property (e.symm j).property
        (fun h => hij (e.symm.injective (Subtype.ext h)))
    obtain ⟨p,hp⟩ := b.exists_face_of_triangle
      (hpair (by decide : (0 : Fin 3) ≠ 1))
      (hpair (by decide : (1 : Fin 3) ≠ 2))
      (hpair (by decide : (2 : Fin 3) ≠ 0))
    have hpar (x : W m) : (graph n k).Adj (f x) v ↔ x ∈ b.faceVertices p := by
      constructor
      · intro h
        have hle := hmax _ (Finset.mem_of_mem_erase (hf_range x))
        have hlt : depth (f x) < depth v := by
          refine lt_of_le_of_ne hle (fun he => hz ?_)
          have hzero := equal_depth_edge_root h.symm he.symm
          exact hzero
        let w : older v := ⟨f x,hlt,h⟩
        let i : Fin 3 := e w
        have hEq : x = a i := by
          apply f.injective
          rw [ea]
          change f x = (e.symm (e w)).val
          rw [e.symm_apply_apply]
        rw [hEq,hp]
        have hall (j : Fin 3) : a j ∈ ({a 0,a 1,a 2} : Set (W m)) := by
          fin_cases j <;> simp
        exact hall i
      · intro h
        rw [hp] at h
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
        rcases h with h | h | h
        all_goals
          rw [h,ea]
          exact (e.symm _).property.2
    let f' : W (m+1) ↪ V := {
      toFun := Sum.elim f (fun _ => v)
      inj' := by
        rintro (x|⟨⟩) (y|⟨⟩) h
        · exact congrArg Sum.inl (f.injective h)
        · exact ((Finset.mem_erase.mp (hf_range x)).1 h).elim
        · exact ((Finset.mem_erase.mp (hf_range y)).1 h.symm).elim
        · rfl }
    refine ⟨m+1,b.attach p,f',?_,?_⟩
    · ext u
      constructor
      · rintro ⟨(x|⟨⟩),rfl⟩
        · exact Finset.mem_of_mem_erase (hf_range x)
        · exact hv
      · intro hu
        by_cases he : u = v
        · exact ⟨Sum.inr (),he.symm⟩
        · have hr : u ∈ Set.range f := by
            rw [hf]
            exact Finset.mem_erase.mpr ⟨he,hu⟩
          obtain ⟨x,hx⟩ := hr
          exact ⟨Sum.inl x,hx⟩
    · rintro (x|⟨⟩) (y|⟨⟩)
      · exact ha x y
      · exact hpar x
      · exact ⟨fun h => (hpar y).1 h.symm, fun h => ((hpar y).2 h).symm⟩
      · exact ⟨fun h => h.ne rfl,False.elim⟩

/-- The finite replicated history graph itself has a stacking presentation. -/
theorem exists_stacking_presentation (n k : ℕ) :
    ∃ (m : ℕ) (b : Build m) (f : W m ≃ Vertex n k),
      ∀ x y, (graph n k).Adj (f x) (f y) ↔ b.graph.Adj x y := by
  classical
  obtain ⟨m,b,e,hr,he⟩ := exists_stacking_on (n := n) (k := k) Finset.univ
    (fun _ => Finset.mem_univ _) (fun {_ _} _ _ => Finset.mem_univ _)
  have hs : Function.Surjective e := fun v => by
    change v ∈ Set.range e
    rw [hr]
    exact Finset.mem_univ _
  exact ⟨m,b,Equiv.ofBijective e ⟨e.injective,hs⟩,he⟩

universe u

/-- A Banach coefficient uniformly valid for a finite stacking presentation. -/
def BuildBanachFeasible {m : ℕ} (b : Build m) (R : ℝ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : W m → W m → E), (∀ x y, g y x = -g x y) →
    (∀ x y z, b.graph.Adj x y → b.graph.Adj y z → b.graph.Adj x z →
      ‖g x y + g y z - g x z‖ ≤ 1) →
    ∃ p : W m → E, ∀ x y, b.graph.Adj x y → ‖g x y - (p y - p x)‖ ≤ R

/-- Uniform bounds over finite stacking presentations apply to the replicated
history graph because it has a finite stacking presentation. -/
theorem banach_of_stackings {R : ℝ}
    (h : ∀ (m : ℕ) (b : Build m), BuildBanachFeasible.{u} b R) :
    BanachFeasible.{u} n k R := by
  obtain ⟨m,b,e,he⟩ := exists_stacking_presentation n k
  intro E _ _ _ g hg ht
  obtain ⟨p,hp⟩ := h m b E (fun x y => g (e x) (e y))
    (fun _ _ => hg _ _) (fun x y z hxy hyz hxz =>
      ht _ _ _ ((he _ _).2 hxy) ((he _ _).2 hyz) ((he _ _).2 hxz))
  refine ⟨fun v => p (e.symm v),fun u v huv => ?_⟩
  have h' : b.graph.Adj (e.symm u) (e.symm v) := (he _ _).1 (by simpa using huv)
  simpa using hp _ _ h'

end
end Omega.PureThreeTree
