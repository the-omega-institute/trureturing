/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalFaceBound
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalFaceBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Multiplicity faces bound the determinant by the exceptional mass. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSwitch
import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound

open SimpleGraph ThreeTerminalBond ThreeTerminalTree ThreeTerminalFaceSwitch
open ThreeTerminalProduct
open scoped BigOperators
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

private def tag {E : Type*} (q : (E → Bool) × (E → Bool)) : E → Fin 3 :=
  fun e => ⟨ThreeTerminalFaceSwitch.multiplicity (q.1 e) (q.2 e), by
    cases q.1 e <;> cases q.2 e <;> decide⟩

private def representative {E : Type*} (α : E → Fin 3) :
    (E → Bool) × (E → Bool) :=
  (fun e => decide (α e ≠ 0),fun e => decide (α e = 2))

private lemma tag_representative {E : Type*} (α : E → Fin 3) :
    tag (representative α) = α := by
  funext e
  have h : ∀ i : Fin 3,
      (⟨ThreeTerminalFaceSwitch.multiplicity (decide (i ≠ 0)) (decide (i = 2)),by
        fin_cases i <;> decide⟩ : Fin 3) = i := by decide
  exact h (α e)

private lemma tag_face {E : Type*} (α : E → Fin 3)
    (q : (E → Bool) × (E → Bool)) :
    tag q = α ↔ Face (representative α) q := by
  constructor
  · intro h e
    exact (congrArg Fin.val (congrFun h e)).trans
      (congrArg Fin.val (congrFun (tag_representative α) e)).symm
  · intro h
    funext e
    exact Fin.ext ((h e).trans
      (congrArg Fin.val (congrFun (tag_representative α) e)))

private lemma tag_swap {E : Type*} (q : (E → Bool) × (E → Bool)) :
    tag (q.2,q.1) = tag q := by
  funext e
  apply Fin.ext
  simp [tag,ThreeTerminalFaceSwitch.multiplicity,add_comm]

private lemma face_fst_injective {E : Type*} (α : E → Fin 3) :
    Set.InjOn Prod.fst {q : (E → Bool) × (E → Bool) | tag q = α} := by
  intro q hq r hr heq
  apply Prod.ext heq
  funext e
  have hh := congrArg Fin.val (congrFun (hq.trans hr.symm) e)
  have he := congrFun heq e
  change ThreeTerminalFaceSwitch.multiplicity (q.1 e) (q.2 e) = ThreeTerminalFaceSwitch.multiplicity (r.1 e) (r.2 e) at hh
  cases h₁ : q.1 e <;> cases h₂ : q.2 e <;>
    cases h₃ : r.1 e <;> cases h₄ : r.2 e <;>
    simp_all [ThreeTerminalFaceSwitch.multiplicity]

private lemma half_count {E : Type*} [Fintype E] [DecidableEq E]
    (hm : 0 < Fintype.card E) (α : E → Fin 3)
    (mode : (E → Bool) → Mode) (u v : Mode) (huv : u ≠ v) :
    ((Finset.univ.filter fun q : (E → Bool) × (E → Bool) =>
      tag q = α ∧ mode q.1 = u ∧ mode q.2 = v).card : ℝ) ≤
        (2 : ℝ)^(Fintype.card E-1) := by
  classical
  let F := Finset.univ.filter fun q : (E → Bool) × (E → Bool) => tag q = α
  let A := F.filter fun q => mode q.1 = u ∧ mode q.2 = v
  let B := F.filter fun q => mode q.1 = v ∧ mode q.2 = u
  have hcard : A.card = B.card := by
    apply Finset.card_bij (fun q _ => (q.2,q.1))
    · intro q hq
      simp only [A,B,F,Finset.mem_filter,Finset.mem_univ,true_and] at hq ⊢
      exact ⟨(tag_swap q).trans hq.1,hq.2.2,hq.2.1⟩
    · intro q hq r hr h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq
      refine ⟨(q.2,q.1),?_,rfl⟩
      simp only [A,B,F,Finset.mem_filter,Finset.mem_univ,true_and] at hq ⊢
      exact ⟨(tag_swap q).trans hq.1,hq.2.2,hq.2.1⟩
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro q hA hB
    have ha := (Finset.mem_filter.mp hA).2.1
    have hb := (Finset.mem_filter.mp hB).2.1
    exact huv (ha.symm.trans hb)
  have hsub : A ∪ B ⊆ F := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact (Finset.mem_filter.mp hq).1
    · exact (Finset.mem_filter.mp hq).1
  have hF : F.card ≤ 2^Fintype.card E := by
    have hh := Finset.card_le_card_of_injOn (s := F)
      (t := (Finset.univ : Finset (E → Bool))) Prod.fst
      (fun _ _ => Finset.mem_univ _) (fun q hq r hr he =>
        face_fst_injective α (Finset.mem_filter.mp hq).2
          (Finset.mem_filter.mp hr).2 he)
    simpa using hh
  have hh : A.card+B.card ≤ 2^Fintype.card E := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact le_trans (Finset.card_le_card hsub) hF
  have hp : 2^Fintype.card E = 2*2^(Fintype.card E-1) := by
    calc
      _ = 2^((Fintype.card E-1)+1) := by congr 1; omega
      _ = _ := by rw [pow_succ]; omega
  have hn : A.card ≤ 2^(Fintype.card E-1) := by rw [hcard,hp] at hh; omega
  have heq : A = Finset.univ.filter fun q : (E → Bool) × (E → Bool) =>
      tag q = α ∧ mode q.1 = u ∧ mode q.2 = v := by
    ext q
    simp [A,F,and_assoc]
  rw [← heq]
  exact_mod_cast hn

private lemma pair_weight_face {E : Type*} [Fintype E] [DecidableEq E]
    (θ : E → ℝ) {r q : (E → Bool) × (E → Bool)} (h : Face r q) :
    weight θ q.1*weight θ q.2 = weight θ r.1*weight θ r.2 := by
  unfold weight
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  have hh := h e
  cases h₁ : q.1 e <;> cases h₂ : q.2 e <;>
    cases h₃ : r.1 e <;> cases h₄ : r.2 e <;>
    simp_all [ThreeTerminalFaceSwitch.multiplicity] <;> ring

private lemma grouped_weight {E : Type*} [Fintype E] [DecidableEq E]
    (θ : E → ℝ) (P : ((E → Bool) × (E → Bool)) → Prop) [DecidablePred P] :
    (∑ q : (E → Bool) × (E → Bool),
      if P q then weight θ q.1*weight θ q.2 else 0) =
    ∑ α : E → Fin 3,
      (weight θ (representative α).1*weight θ (representative α).2)*
        (Finset.univ.filter fun q : (E → Bool) × (E → Bool) => tag q = α ∧ P q).card := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset ((E → Bool) × (E → Bool))) tag
    (fun q => if P q then weight θ q.1*weight θ q.2 else 0)]
  apply Finset.sum_congr rfl
  intro α _
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter fun q : (E → Bool) × (E → Bool) =>
      tag q = α).filter P = Finset.univ.filter
      (fun q : (E → Bool) × (E → Bool) => tag q = α ∧ P q) := by
    ext q
    simp [and_assoc]
  rw [hfilter]
  calc
    _ = ∑ _q ∈ Finset.univ.filter
        (fun q : (E → Bool) × (E → Bool) => tag q = α ∧ P q),
        weight θ (representative α).1*weight θ (representative α).2 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact pair_weight_face θ ((tag_face α q).mp (Finset.mem_filter.mp hq).2.1)
    _ = _ := by simp [nsmul_eq_mul,mul_comm]

/-- A nonempty finite actual edge network has determinant at most the
exceptional mass times the stated edge-count constant. -/
theorem edge_count_bound {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (ends : E → V × V) (a b c : V)
    (θ : E → ℝ) (hθ : ∀ e, θ e ∈ Set.Icc 0 1) (hm : 0 < Fintype.card E) :
    |delta (law ends a b c θ)| ≤
      (2 : ℝ)^(Fintype.card E-1)*law ends a b c θ .ac := by
  classical
  let mode := fun ω : E → Bool => graphMode (openGraph ends ω) a b c
  let W := fun α : E → Fin 3 =>
    weight θ (representative α).1*weight θ (representative α).2
  let N := fun α : E → Fin 3 => fun u v : Mode =>
    (Finset.univ.filter fun q : (E → Bool) × (E → Bool) =>
      tag q = α ∧ mode q.1 = u ∧ mode q.2 = v).card
  let Z := fun α : E → Fin 3 =>
    (Finset.univ.filter fun q : (E → Bool) × (E → Bool) =>
      tag q = α ∧ mode q.1 = .ac).card
  let C : ℝ := 2^(Fintype.card E-1)
  have hw (ω : E → Bool) : 0 ≤ weight θ ω := by
    unfold weight
    apply Finset.prod_nonneg
    intro e _
    cases ω e
    · exact sub_nonneg.mpr (hθ e).2
    · exact (hθ e).1
  have hW (α) : 0 ≤ W α := mul_nonneg (hw _) (hw _)
  have hjoint (u v : Mode) :
      law ends a b c θ u*law ends a b c θ v =
        ∑ α : E → Fin 3, W α*(N α u v : ℝ) := by
    rw [← grouped_weight θ (fun q => mode q.1 = u ∧ mode q.2 = v)]
    rw [Fintype.sum_prod_type]
    unfold law
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    apply Finset.sum_congr rfl
    intro η _
    simp only [partition_graphMode]
    change (if mode ω = u then _ else 0)*(if mode η = v then _ else 0) = _
    split_ifs <;> simp_all
  have hZ : law ends a b c θ .ac = ∑ α : E → Fin 3, W α*(Z α : ℝ) := by
    rw [← grouped_weight θ (fun q => mode q.1 = .ac),Fintype.sum_prod_type]
    unfold law
    simp_rw [partition_graphMode]
    apply Finset.sum_congr rfl
    intro ω _
    change (if mode ω = .ac then weight θ ω else 0) = _
    by_cases h : mode ω = .ac
    · simp [h,← Finset.mul_sum,weight_sum]
    · simp [h]
  have hlocal (α : E → Fin 3) :
      |(N α .separate .all : ℝ)-(N α .ab .bc : ℝ)| ≤ C*(Z α : ℝ) := by
    by_cases hz : Z α = 0
    · have hno : ∀ q, Face (representative α) q →
          graphMode (openGraph ends q.1) a b c ≠ .ac := by
        intro q hq hmode
        have hmem : q ∈ Finset.univ.filter
            (fun q : (E → Bool) × (E → Bool) => tag q = α ∧ mode q.1 = .ac) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,(tag_face α q).mpr hq,hmode⟩
        have hn := Finset.card_pos.mpr ⟨q,hmem⟩
        change 0 < Z α at hn
        omega
      have hc := face_cancel ends (representative α) a b c hno
      have heq : N α .separate .all = N α .ab .bc := by
        simpa only [N,mode,← tag_face] using hc
      simp [heq,hz]
    · have hz1 : (1 : ℝ) ≤ (Z α : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      have h₁ := half_count hm α mode .separate .all (by decide)
      have h₂ := half_count hm α mode .ab .bc (by decide)
      have hC : 0 ≤ C := by positivity
      change (N α .separate .all : ℝ) ≤ C at h₁
      change (N α .ab .bc : ℝ) ≤ C at h₂
      have hn₁ : 0 ≤ (N α .separate .all : ℝ) := Nat.cast_nonneg _
      have hn₂ : 0 ≤ (N α .ab .bc : ℝ) := Nat.cast_nonneg _
      have hCZ : C ≤ C*(Z α : ℝ) := by
        nlinarith [mul_nonneg hC (sub_nonneg.mpr hz1)]
      apply abs_le.mpr
      constructor <;> linarith
  rw [delta,hjoint,hjoint,← Finset.sum_sub_distrib]
  calc
    _ = |∑ α : E → Fin 3, W α*((N α .separate .all : ℝ)-(N α .ab .bc : ℝ))| := by
      congr 1
      apply Finset.sum_congr rfl
      intro α _
      ring
    _ ≤ ∑ α : E → Fin 3, |W α*((N α .separate .all : ℝ)-(N α .ab .bc : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ α : E → Fin 3, C*(W α*(Z α : ℝ)) := by
      apply Finset.sum_le_sum
      intro α _
      rw [abs_mul,abs_of_nonneg (hW α)]
      nlinarith [mul_le_mul_of_nonneg_left (hlocal α) (hW α)]
    _ = C*law ends a b c θ .ac := by rw [← Finset.mul_sum,← hZ]

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound.edge_count_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_count_bound

end
end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound
