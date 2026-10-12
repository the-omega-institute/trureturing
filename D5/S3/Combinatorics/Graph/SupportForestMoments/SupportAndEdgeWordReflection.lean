/- GID: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.result; instance=D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.A_M4
   digest: Support counts and sound reflection of edge-word character moments. -/

/-
Mathematical judgement:
twoPoints_card: proof_shape: content
chi_eq_fastChi: proof_shape: content
mem_endpointSet: proof_shape: bind-only; consumers: endpointGraph_edge_card, endpointIso
edgeFinset_from_finset: proof_shape: bind-only; consumers: endpointGraph_edge_card
endpointGraph_edge_card: proof_shape: bind-only; consumers: iso_edge_card
iso_edge_card: proof_shape: bind-only; consumers: N_H_powersetCard
N_H_powersetCard: proof_shape: bind-only; consumers: N_H_of_enumeration
N_H_of_enumeration: proof_shape: bind-only; consumers: ShapiroQuarticInversionRefutation.A_P5, ShapiroQuarticInversionRefutation.B_P5, counts_eq_of_iso_enumerations
counts_eq_of_iso_enumerations: proof_shape: bind-only; consumers: ShapiroQuarticInversionRefutation.low_count_0, ShapiroQuarticInversionRefutation.low_count_1, ShapiroQuarticInversionRefutation.low_count_2, ShapiroQuarticInversionRefutation.low_count_3
digit_pack: proof_shape: bind-only; consumers: ShapiroQuarticInversionRefutation.q3_data
countNat_eq_card: proof_shape: bind-only; consumers: natChi_sound
natChi_sound: proof_shape: content
natSwap_sound: proof_shape: bind-only; consumers: natProd_sound
natProd_sound: proof_shape: content
sum_fin_cons: proof_shape: bind-only; consumers: evalMoment_sound
evalMoment_sound: proof_shape: content
evalMoment_two_levels: proof_shape: bind-only; consumers: evalMoment_two_fin
evalMoment_two_fin: proof_shape: bind-only; consumers: ShapiroQuarticInversionRefutation.evalA4, ShapiroQuarticInversionRefutation.evalB4
moment_reindex: proof_shape: bind-only; consumers: ShapiroQuarticInversionRefutation.evalA_sound, ShapiroQuarticInversionRefutation.evalB_sound
escape_witness: twoPoints_card; evalMoment_sound
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.
-/



import Mathlib.Combinatorics.SimpleGraph.LapMatrix

namespace D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection
open scoped BigOperators
set_option autoImplicit false

def endpointSet {n : ℕ} (S : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  S.biUnion Sym2.toFinset

def endpointGraph {n : ℕ} (S : Finset (Sym2 (Fin n))) :
    SimpleGraph {v : Fin n // v ∈ endpointSet S} :=
  (SimpleGraph.fromEdgeSet (S : Set (Sym2 (Fin n)))).induce (endpointSet S : Set (Fin n))

noncomputable def N_H {n h : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin h)) : ℕ := by
  classical
  exact (G.edgeFinset.powerset.filter fun S => Nonempty (endpointGraph S ≃g H)).card

def c1 {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun v => σ v = v).card

def c2 {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := σ.cycleType.count 2

def chi {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℤ :=
  ((c1 σ).choose 2 : ℤ) + (c2 σ : ℤ) - (c1 σ : ℤ)

def edgeSwap {n : ℕ} : Sym2 (Fin n) → Equiv.Perm (Fin n) :=
  Sym2.lift ⟨Equiv.swap, Equiv.swap_comm⟩

noncomputable def M_r2 {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℤ := by
  classical
  exact ∑ w : Fin r → G.edgeFinset, chi ((List.ofFn fun i => edgeSwap (w i).val).prod)

def noIsolated {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v, ∃ w, G.Adj v w


end D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection
namespace D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Equiv.Perm
open scoped BigOperators

def twoPoints {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) : Finset α :=
  σ.support \ (σ ^ 2).support

theorem twoPoints_card {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) :
    (twoPoints σ).card = 2 * σ.cycleType.count 2 := by
  classical
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one => simp [twoPoints]
  | base_cycles σ hs =>
    rw [hs.cycleType, Multiset.count_singleton]
    by_cases hc : σ.support.card = 2
    · have ho : σ ^ 2 = 1 := by rw [← hc, ← hs.orderOf]; exact pow_orderOf_eq_one σ
      simp [twoPoints, ho, hc]
    · have hp : (σ ^ 2).support = σ.support := by
        apply Finset.Subset.antisymm (Equiv.Perm.support_pow_le σ 2)
        intro x hx
        apply Equiv.Perm.mem_support.mpr
        intro hxx
        have hmod : (2 : ℤ) % (σ.support.card : ℤ) = 0 :=
          (Equiv.Perm.cycle_zpow_mem_support_iff hs (Equiv.Perm.mem_support.mp hx)).mp
            (by simpa using hxx)
        have hd : (σ.support.card : ℤ) ∣ (2 : ℤ) := Int.dvd_of_emod_eq_zero hmod
        have hd' : σ.support.card ∣ 2 := by exact_mod_cast hd
        have hu := Nat.le_of_dvd (by decide : 0 < 2) hd'
        have hl := hs.two_le_card_support
        exact hc (by omega)
      simp [twoPoints, hp]
      exact Ne.symm hc
  | induction_disjoint σ τ hd _ ihσ ihτ =>
    have he : twoPoints (σ * τ) = twoPoints σ ∪ twoPoints τ := by
      unfold twoPoints
      rw [hd.commute.mul_pow, hd.support_mul, (hd.pow_disjoint_pow 2 2).support_mul]
      ext x
      have hst := Equiv.Perm.disjoint_iff_disjoint_support.mp hd
      have hn : ¬ (x ∈ σ.support ∧ x ∈ τ.support) :=
        fun h => (Finset.disjoint_left.mp hst) h.1 h.2
      have hsp := Equiv.Perm.support_pow_le σ 2
      have htp := Equiv.Perm.support_pow_le τ 2
      simp only [Finset.mem_sdiff, Finset.mem_union]
      aesop (add safe Equiv.Perm.pow_apply_eq_self_of_apply_eq_self)
    have hdis : Disjoint (twoPoints σ) (twoPoints τ) :=
      (Equiv.Perm.disjoint_iff_disjoint_support.mp hd).mono
        Finset.sdiff_subset Finset.sdiff_subset
    rw [he, Finset.card_union_of_disjoint hdis, hd.cycleType_mul, Multiset.count_add,
      ihσ, ihτ]
    omega

private def fastChi {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℤ :=
  ((c1 σ).choose 2 : ℤ) + ((twoPoints σ).card / 2 : ℕ) - (c1 σ : ℤ)

private theorem chi_eq_fastChi {n : ℕ} (σ : Equiv.Perm (Fin n)) : chi σ = fastChi σ := by
  unfold chi fastChi c2
  rw [twoPoints_card, Nat.mul_div_right]
  decide

end D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection

namespace D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem mem_endpointSet {n : ℕ} (S : Finset (Sym2 (Fin n))) (v : Fin n) :
    v ∈ endpointSet S ↔ ∃ w, s(v, w) ∈ S := by
  simp only [endpointSet, Finset.mem_biUnion, Sym2.mem_toFinset, Sym2.mem_iff_exists]
  constructor
  · rintro ⟨e, he, w, rfl⟩
    exact ⟨w, he⟩
  · rintro ⟨w, hw⟩
    exact ⟨s(v, w), hw, w, rfl⟩

private def endpointIso {n : ℕ} (S S' : Finset (Sym2 (Fin n)))
    (q : Equiv.Perm (Fin n))
    (hq : ∀ u v, s(q u, q v) ∈ S' ↔ s(u, v) ∈ S) :
    endpointGraph S ≃g endpointGraph S' := by
  have hv : ∀ v, v ∈ endpointSet S ↔ q v ∈ endpointSet S' := by
    intro v
    simp only [mem_endpointSet]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨q w, (hq v w).mpr hw⟩
    · rintro ⟨w, hw⟩
      refine ⟨q.symm w, (hq v (q.symm w)).mp ?_⟩
      simpa using hw
  refine ⟨q.subtypeEquiv hv, ?_⟩
  intro u v
  change (s(q u.val, q v.val) ∈ S' ∧ q u.val ≠ q v.val) ↔
    (s(u.val, v.val) ∈ S ∧ u.val ≠ v.val)
  rw [hq, q.injective.ne_iff]

private theorem edgeFinset_from_finset {n : ℕ} (S : Finset (Sym2 (Fin n)))
    [fe : Fintype (SimpleGraph.fromEdgeSet (S : Set (Sym2 (Fin n)))).edgeSet]
    (hd : ∀ e ∈ S, ¬ e.IsDiag) :
    @SimpleGraph.edgeFinset _ (SimpleGraph.fromEdgeSet (S : Set (Sym2 (Fin n)))) fe = S := by
  apply Finset.coe_injective
  rw [SimpleGraph.coe_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
  constructor
  · exact And.left
  · intro he
    exact ⟨he, hd e he⟩

private theorem endpointGraph_edge_card {n : ℕ} (S : Finset (Sym2 (Fin n)))
    (hd : ∀ e ∈ S, ¬ e.IsDiag)
    [fe : Fintype (endpointGraph S).edgeSet] :
    (@SimpleGraph.edgeFinset _ (endpointGraph S) fe).card = S.card := by
  have hs : (SimpleGraph.fromEdgeSet (S : Set (Sym2 (Fin n)))).support ⊆
      (endpointSet S : Set (Fin n)) := by
    intro v hv
    obtain ⟨w, hw⟩ := hv
    exact (mem_endpointSet S v).mpr ⟨w, hw.1⟩
  have hh := SimpleGraph.card_edgeFinset_induce_of_support_subset hs
  have he : (SimpleGraph.fromEdgeSet (S : Set (Sym2 (Fin n)))).edgeFinset = S :=
    edgeFinset_from_finset S hd
  have hc := congrArg Finset.card he
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hh hc
  rw [@SimpleGraph.edgeFinset_card _ (endpointGraph S) fe, ← @Nat.card_eq_fintype_card _ fe]
  convert hh.trans hc using 1 <;> congr! 8

private theorem iso_edge_card {n h : ℕ} (S : Finset (Sym2 (Fin n)))
    (hd : ∀ e ∈ S, ¬ e.IsDiag) (H : SimpleGraph (Fin h))
    (f : endpointGraph S ≃g H) : S.card = H.edgeFinset.card := by
  classical
  rw [← endpointGraph_edge_card S hd, SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  exact Fintype.card_congr f.mapEdgeSet

private theorem N_H_powersetCard {n h : ℕ} (G : SimpleGraph (Fin n))
    (H : SimpleGraph (Fin h)) :
    N_H G H = ((G.edgeFinset.powersetCard H.edgeFinset.card).filter
      fun S => Nonempty (endpointGraph S ≃g H)).card := by
  classical
  unfold N_H
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hS, ⟨f⟩⟩
    have hd : ∀ e ∈ S, ¬e.IsDiag := by
      intro e he
      exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hS he))
    exact ⟨⟨hS, iso_edge_card S hd H f⟩, ⟨f⟩⟩
  · rintro ⟨⟨hS, _⟩, hf⟩
    exact ⟨hS, hf⟩

theorem N_H_of_enumeration {n h r t : ℕ} (G : SimpleGraph (Fin n))
    (H : SimpleGraph (Fin h)) (a : Fin t → Finset (Sym2 (Fin n)))
    (hi : Function.Injective a)
    (ha : Finset.univ.image a = G.edgeFinset.powersetCard r)
    (hr : H.edgeFinset.card = r) :
    N_H G H = ∑ i, if Nonempty (endpointGraph (a i) ≃g H) then 1 else 0 := by
  classical
  rw [N_H_powersetCard, hr, ← ha]
  rw [Finset.filter_image, Finset.card_image_of_injective _ hi]
  exact (Finset.sum_boole (R := ℕ) _ _).symm

theorem counts_eq_of_iso_enumerations {n h r t : ℕ}
    (G G' : SimpleGraph (Fin n)) (H : SimpleGraph (Fin h))
    (a b : Fin t → Finset (Sym2 (Fin n)))
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : Finset.univ.image a = G.edgeFinset.powersetCard r)
    (hb : Finset.univ.image b = G'.edgeFinset.powersetCard r)
    (hf : ∀ i, endpointGraph (a i) ≃g endpointGraph (b i))
    (hr : H.edgeFinset.card = r) : N_H G H = N_H G' H := by
  classical
  rw [N_H_of_enumeration G H a hai ha hr, N_H_of_enumeration G' H b hbi hb hr]
  apply Finset.sum_congr rfl
  intro i _
  have he : Nonempty (endpointGraph (a i) ≃g H) ↔ Nonempty (endpointGraph (b i) ≃g H) :=
    ⟨fun ⟨f⟩ => ⟨(hf i).symm.trans f⟩, fun ⟨f⟩ => ⟨(hf i).trans f⟩⟩
  simp only [he]

end D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection

namespace D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection
set_option maxHeartbeats 8000000
def digit (b p i : ℕ) : ℕ := p / b^i % b

def pack (b n : ℕ) (f : ℕ → ℕ) : ℕ := Nat.ofDigits b ((List.range n).map f)

theorem digit_pack (b n : ℕ) (hb : 0 < b) (f : ℕ → ℕ)
    (hf : ∀ i, i < n → f i < b) (i : ℕ) (hi : i < n) :
    digit b (pack b n f) i = f i := by
  unfold digit pack
  have hh : ∀ v ∈ (List.range n).map f, v < b := by
    rintro v hv
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
    exact hf j (List.mem_range.mp hj)
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i hb _ hh, Nat.ofDigits_mod_eq_head!]
  have he : (((List.range n).map f).drop i).head! = f i := by
    simp [List.head!_eq_getElem!, hi]
  rw [he, Nat.mod_eq_of_lt (hf i hi)]

def endpointIso_image {n : ℕ} (S S' : Finset (Sym2 (Fin n)))
    (q : Equiv.Perm (Fin n)) (hq : S.image (Sym2.map q) = S') :
    endpointGraph S ≃g endpointGraph S' := by
  apply endpointIso S S' q
  intro u v
  constructor
  · intro h
    rw [← hq] at h
    obtain ⟨e, he, hqe⟩ := Finset.mem_image.mp h
    have h : e = s(u,v) := (Sym2.map.injective q.injective) hqe
    exact h ▸ he
  · intro h
    rw [← hq]
    exact Finset.mem_image.mpr ⟨s(u,v), h, rfl⟩

end D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection

namespace D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open scoped BigOperators

def countNat (n : ℕ) (p : ℕ → Bool) : ℕ := ((List.range n).filter p).length

def natChi (n : ℕ) (p : ℕ → ℕ) : ℤ :=
  let c := countNat n (fun v => p v == v)
  let d := countNat n (fun v => p v != v && p (p v) == v)
  (c.choose 2 : ℤ) + (d / 2 : ℕ) - (c : ℤ)

def natProd : List (ℕ × ℕ) → ℕ → ℕ
  | [], x => x
  | (u,v)::w, x => Equiv.swapCore u v (natProd w x)

def evalMoment (n : ℕ) (edges : List (ℕ × ℕ)) : ℕ → List (ℕ × ℕ) → ℤ
  | 0, w => natChi n (natProd w)
  | r+1, w => (edges.map fun e => evalMoment n edges r (w ++ [e])).sum

private theorem countNat_eq_card {n : ℕ} (p : ℕ → Bool) :
    countNat n p = (Finset.univ.filter fun v : Fin n => p v.val).card := by
  rw [← List.toFinset_finRange, (List.nodup_finRange n).card_eq_countP]
  simp only [countNat, ← List.countP_eq_length_filter, List.countP_map]
  have h : (List.finRange n).map Fin.val = List.range n := by
    ext i
    simp
  rw [← h, List.countP_map]
  simp [Function.comp_def]

private theorem natChi_sound {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ℕ → ℕ)
    (hp : ∀ v : Fin n, p v.val = (σ v).val) : natChi n p = chi σ := by
  rw [chi_eq_fastChi]
  unfold natChi fastChi c1
  rw [countNat_eq_card, countNat_eq_card]
  have h₁ : (Finset.univ.filter fun v : Fin n => p v.val == v.val) =
      (Finset.univ.filter fun v => σ v = v) := by
    ext v
    simp [hp v, Fin.ext_iff]
  have h₂ : (Finset.univ.filter fun v : Fin n => p v.val != v.val && p (p v.val) == v.val) =
      twoPoints σ := by
    ext v
    simp [twoPoints, Equiv.Perm.mem_support, hp v, hp (σ v), pow_two,
      Equiv.Perm.mul_apply, Fin.ext_iff]
  rw [h₁, h₂]

private theorem natSwap_sound {n : ℕ} (u v x : Fin n) :
    Equiv.swapCore u.val v.val x.val = (Equiv.swap u v x).val := by
  by_cases h : x = u
  · subst x; simp [Equiv.swapCore]
  · by_cases h' : x = v
    · subst x; simp [Equiv.swapCore, Equiv.swap_apply_right, Ne.symm h, Fin.ext_iff] at *
    · have hu : x.val ≠ u.val := fun hval => h (Fin.ext hval)
      have hv : x.val ≠ v.val := fun hval => h' (Fin.ext hval)
      simp [Equiv.swapCore, Equiv.swap_apply_of_ne_of_ne h h', hu, hv]

private theorem natProd_sound {n : ℕ} (w : List (Fin n × Fin n)) (x : Fin n) :
    natProd (w.map fun e => (e.1.val, e.2.val)) x.val =
      ((w.map fun e => Equiv.swap e.1 e.2).prod x).val := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    simp only [List.map_cons, natProd, List.prod_cons, Equiv.Perm.mul_apply]
    rw [ih, natSwap_sound]

private theorem sum_fin_cons {m : ℕ} {α β : Type*} [Fintype α] [AddCommMonoid β]
    (f : (Fin (m+1) → α) → β) :
    ∑ w, f w = ∑ a, ∑ w : Fin m → α, f (Fin.cons a w) := by
  rw [← (Fin.consEquiv fun _ : Fin (m+1) => α).sum_comp f, Fintype.sum_prod_type]
  rfl

theorem evalMoment_sound {n m : ℕ} (e : Fin m → Fin n × Fin n) (r : ℕ)
    (w : List (Fin n × Fin n)) :
    evalMoment n ((List.finRange m).map fun i => ((e i).1.val, (e i).2.val)) r
      (w.map fun a => (a.1.val, a.2.val)) =
    ∑ v : Fin r → Fin m, chi ((w.map fun a => Equiv.swap a.1 a.2).prod *
      (List.ofFn fun i => Equiv.swap (e (v i)).1 (e (v i)).2).prod) := by
  induction r generalizing w with
  | zero =>
    simp only [evalMoment, List.ofFn_zero, List.prod_nil, mul_one, Fintype.sum_unique]
    apply natChi_sound
    exact natProd_sound w
  | succ r ih =>
    simp only [evalMoment, List.map_map]
    rw [← List.sum_toFinset _ (List.nodup_finRange m), List.toFinset_finRange]
    rw [sum_fin_cons]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [Function.comp_apply]
    rw [show w.map (fun a => (a.1.val, a.2.val)) ++ [((e i).1.val, (e i).2.val)] =
      (w ++ [e i]).map (fun a => (a.1.val, a.2.val)) by simp]
    rw [ih]
    apply Finset.sum_congr rfl
    intro v _
    simp [List.map_append, List.prod_append, List.ofFn_succ, mul_assoc]


private theorem evalMoment_two_levels (n : ℕ) (edges : List (ℕ × ℕ)) (r : ℕ) (w : List (ℕ × ℕ)) :
    evalMoment n edges (r+2) w =
    (edges.map fun a => (edges.map fun b => evalMoment n edges r (w ++ [a,b])).sum).sum := by
  simp only [evalMoment, List.append_assoc, List.singleton_append]

theorem evalMoment_two_fin (n m : ℕ) (e : Fin m → ℕ × ℕ) (r : ℕ) (w : List (ℕ × ℕ)) :
    evalMoment n ((List.finRange m).map e) (r+2) w =
    ∑ i, ∑ j, evalMoment n ((List.finRange m).map e) r (w ++ [e i,e j]) := by
  rw [evalMoment_two_levels]
  simp only [List.map_map, ← List.sum_toFinset _ (List.nodup_finRange m), List.toFinset_finRange,
    Function.comp_apply]

def wordMoment {n m : ℕ} (e : Fin m → Sym2 (Fin n)) (r : ℕ) : ℤ :=
  ∑ w : Fin r → Fin m, chi ((List.ofFn fun i => edgeSwap (e (w i))).prod)
section ClassicalBridge
attribute [local instance] Classical.propDecidable

private noncomputable def edgeEquiv {n m : ℕ} (G : SimpleGraph (Fin n))
    (e : Fin m → Sym2 (Fin n)) (he : Finset.univ.image e = G.edgeFinset)
    (hi : Function.Injective e) : Fin m ≃ G.edgeFinset := by
  classical
  have hm (i : Fin m) : e i ∈ G.edgeFinset := he ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  refine Equiv.ofBijective (fun i => ⟨e i, hm i⟩) ⟨?_, ?_⟩
  · intro i j h
    exact hi (congrArg Subtype.val h)
  · intro z
    have hz : z.val ∈ Finset.univ.image e := he.symm ▸ z.property
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
    exact ⟨i, Subtype.ext hi⟩

theorem moment_reindex {n m : ℕ} (G : SimpleGraph (Fin n)) (e : Fin m → Sym2 (Fin n))
    (he : Finset.univ.image e = G.edgeFinset) (hi : Function.Injective e) (r : ℕ) :
    M_r2 G r = wordMoment e r := by
  classical
  let q := edgeEquiv G e he hi
  let wq := Equiv.arrowCongr (Equiv.refl (Fin r)) q
  unfold M_r2 wordMoment
  symm
  convert wq.sum_comp (fun w : Fin r → G.edgeFinset =>
    chi ((List.ofFn fun i => edgeSwap (w i).val).prod)) using 1 <;> congr! 8

end ClassicalBridge


end D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection
