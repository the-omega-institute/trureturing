import D5.S3.FiniteGroups.Quandles.TaThreeInvariantRefutation

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! Genevois's Question 9.4 (arXiv:2505.09194v1). In the two-factor product
of Example 2.6, two conjugates of the upper factor have an intersection
whose image in the upper cyclic group is proper and nontrivial. -/

namespace D5.S3.FiniteGroups.Quandles.GenevoisQ94Settlement

structure Oposet (I : Type) [PartialOrder I] where
  orthogonal : I → I → Prop
  symmetric : Std.Symm orthogonal
  irreflexive : ∀ i : I, ¬ orthogonal i i
  incomparable : ∀ {i j : I}, orthogonal i j → ¬ i ≤ j ∧ ¬ j ≤ i
  downward : ∀ {i j k : I}, i ≤ j → orthogonal j k → orthogonal i k

abbrev LowerIndex {I : Type} [PartialOrder I] (k : I) := {i : I // i < k}

structure LowerAction {I : Type} [PartialOrder I] (G : I → Type)
    [∀ i, Group (G i)] (k : I) where
  onIndex : G k →* Equiv.Perm (LowerIndex k)
  onFactor : ∀ (b : G k) (i : LowerIndex k), G i.val ≃* G (onIndex b i).val
  one_action : ∀ (i : LowerIndex k) (a : G i.val),
    (⟨onIndex 1 i, onFactor 1 i a⟩ : Σ j : LowerIndex k, G j.val) = ⟨i, a⟩
  mul_action : ∀ (b c : G k) (i : LowerIndex k) (a : G i.val),
    (⟨onIndex (b * c) i, onFactor (b * c) i a⟩ : Σ j : LowerIndex k, G j.val) =
      ⟨onIndex b (onIndex c i), onFactor b (onIndex c i) (onFactor c i a)⟩

def LowerAction.apply {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] {k : I} (A : LowerAction G k) (b : G k) (i : LowerIndex k)
    (a : G i.val) : Σ j : LowerIndex k, G j.val :=
  ⟨A.onIndex b i, A.onFactor b i a⟩

def PreservesOrder {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] {k : I} (A : LowerAction G k) : Prop :=
  ∀ (b : G k) (i j : LowerIndex k), A.onIndex b i ≤ A.onIndex b j ↔ i ≤ j

def IsQuandleAction {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] (A : ∀ k : I, LowerAction G k)
    (order : ∀ k : I, PreservesOrder (A k)) : Prop :=
  ∀ (i j k : I) (hij : i < j) (hjk : j < k)
      (a : G i) (b : G j) (c : G k),
    let aUnderB := (A j).apply b ⟨i, hij⟩ a
    let aUnderC := (A k).apply c ⟨i, lt_trans hij hjk⟩ a
    let bUnderC := (A k).apply c ⟨j, hjk⟩ b
    let aLeft := (A k).apply c ⟨aUnderB.1.val, lt_trans aUnderB.1.property hjk⟩ aUnderB.2
    let hij' : aUnderC.1.val < bUnderC.1.val :=
      (lt_iff_lt_of_le_iff_le' (order k c _ _) (order k c _ _)).2 hij
    let aRight := (A bUnderC.1.val).apply bUnderC.2 ⟨aUnderC.1.val, hij'⟩ aUnderC.2
    (⟨aLeft.1.val, aLeft.2⟩ : Σ l : I, G l) = ⟨aRight.1.val, aRight.2⟩

structure QuandleSystem (I : Type) [PartialOrder I] (G : I → Type)
    [∀ i, Group (G i)] where
  oposet : Oposet I
  nontrivial : ∀ i : I, Nontrivial (G i)
  action : ∀ k : I, LowerAction G k
  preservesOrder : ∀ k : I, PreservesOrder (action k)
  preservesOrthogonal : ∀ (k : I) (b : G k) (i j : LowerIndex k),
    oposet.orthogonal ((action k).onIndex b i).val ((action k).onIndex b j).val ↔
      oposet.orthogonal i.val j.val
  quandle : IsQuandleAction action preservesOrder

def relators {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] (S : QuandleSystem I G) : Set (Monoid.CoprodI G) :=
  {r | ∃ (i j : I) (a : G i) (b : G j),
    let ai := Monoid.CoprodI.of a
    let bj := Monoid.CoprodI.of b
    (S.oposet.orthogonal i j ∧ r = ai * bj * (bj * ai)⁻¹) ∨
      ∃ h : i < j,
        let ba := (S.action j).apply b ⟨i, h⟩ a
        r = ai * bj * (bj * Monoid.CoprodI.of ba.2)⁻¹}

abbrev QuandleProduct {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] (S : QuandleSystem I G) :=
  Monoid.CoprodI G ⧸ Subgroup.normalClosure (relators S)

def factor {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] (S : QuandleSystem I G) (i : I) : G i →* QuandleProduct S :=
  (QuotientGroup.mk' (Subgroup.normalClosure (relators S))).comp Monoid.CoprodI.of

def standardParabolic {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] (S : QuandleSystem I G) (J : Set I) :
    Subgroup (QuandleProduct S) :=
  Subgroup.closure {q | ∃ (j : I), j ∈ J ∧ ∃ a : G j, factor S j a = q}

def claim : Prop :=
  ∀ (I : Type) (_ : PartialOrder I) (G : I → Type) (_ : ∀ i : I, Group (G i))
    (S : QuandleSystem I G) (J L : Set I) (g h : QuandleProduct S),
    ∃ (T : Set I) (k : QuandleProduct S),
      (standardParabolic S J).map (MulAut.conj g).toMonoidHom ⊓
        (standardParabolic S L).map (MulAut.conj h).toMonoidHom =
          (standardParabolic S T).map (MulAut.conj k).toMonoidHom

private abbrev Lower := Multiplicative (ZMod 16)
private abbrev Upper := Multiplicative (ZMod 4)
private abbrev Model := TaThreeInvariantRefutation.Gr false

private def forwardAction {N B : Type} [Group N] [Group B]
    {action : B →* MulAut N} (_ : N ⋊[action] B) : B →* MulAut N :=
  action

private abbrev inverseAction : Upper →* MulAut Lower :=
  (forwardAction (1 : Model)).comp invMonoidHom

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check the action on all residues by kernel reduction.
private theorem inverseAction_formula : ∀ (b : Upper) (a : Lower),
    (inverseAction b a).toAdd = (13 : ZMod 16) ^ b.toAdd.val * a.toAdd := by
  intro b
  fin_cases b <;> decide

private abbrev ChainFactor (i : Fin 2) : Type :=
  match i.val with
  | 0 => Lower
  | _ + 1 => Upper

private instance chainGroup (i : Fin 2) : Group (ChainFactor i) :=
  match i with
  | ⟨0, _⟩ => inferInstanceAs (Group Lower)
  | ⟨_ + 1, _⟩ => inferInstanceAs (Group Upper)

private theorem chain_lt {i j : Fin 2} (h : i < j) : i = 0 ∧ j = 1 := by
  change i.val < j.val at h
  have hi := i.isLt
  have hj := j.isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

private def chainActionOnFactor (k : Fin 2) (i : LowerIndex k) :
    ChainFactor k →* MulAut (ChainFactor i.val) :=
  (chain_lt i.property).1.symm ▸ (chain_lt i.property).2.symm ▸ inverseAction

private def chainAction (k : Fin 2) : LowerAction ChainFactor k where
  onIndex := 1
  onFactor b i := chainActionOnFactor k i b
  one_action := by
    intro i a
    change (⟨i, chainActionOnFactor k i 1 a⟩ : Σ j : LowerIndex k, ChainFactor j.val) = ⟨i, a⟩
    rw [map_one]
    rfl
  mul_action := by
    intro b c i a
    change (⟨i, chainActionOnFactor k i (b * c) a⟩ : Σ j : LowerIndex k, ChainFactor j.val) =
      ⟨i, chainActionOnFactor k i b (chainActionOnFactor k i c a)⟩
    rw [map_mul]
    rfl

private def chain : QuandleSystem (Fin 2) ChainFactor where
  oposet :=
    { orthogonal := fun _ _ => False
      symmetric := ⟨fun _ _ h => h⟩
      irreflexive := fun _ h => h
      incomparable := fun h => h.elim
      downward := fun _ h => h }
  nontrivial :=
    Fin.cases (motive := fun i => Nontrivial (ChainFactor i))
      (ZMod.nontrivial_iff.mpr (by decide : 16 ≠ 1))
      (fun _ => ZMod.nontrivial_iff.mpr (by decide : 4 ≠ 1))
  action := chainAction
  preservesOrder := fun _ _ _ _ => Iff.rfl
  preservesOrthogonal := fun _ _ _ _ => Iff.rfl
  quandle := by
    intro i j k hij hjk
    have hj := (chain_lt hij).2
    have hj' := (chain_lt hjk).1
    exact ((by decide : (1 : Fin 2) ≠ 0) (hj.symm.trans hj')).elim

private abbrev Q := QuandleProduct chain
private abbrev modelInl : Lower →* Model := SemidirectProduct.inl
private abbrev modelInr : Upper →* Model := SemidirectProduct.inr

private def modelFactor (i : Fin 2) : ChainFactor i →* Model :=
  Fin.cases (motive := fun i => ChainFactor i →* Model) modelInl (fun _ => modelInr) i

private def fromCoproduct : Monoid.CoprodI ChainFactor →* Model :=
  Monoid.CoprodI.lift modelFactor

private theorem model_twist (a : Lower) (b : Upper) :
    modelInl a * modelInr b = modelInr b * modelInl (inverseAction b a) := by
  have conjugation :
      modelInl (inverseAction b a) = modelInr b⁻¹ * modelInl a * modelInr b := by
    have formula := SemidirectProduct.inl_aut (φ := forwardAction (1 : Model)) b⁻¹ a
    rw [inv_inv] at formula
    exact formula
  rw [conjugation, ← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

private theorem relators_in_kernel :
    Subgroup.normalClosure (relators chain) ≤ fromCoproduct.ker := by
  apply Subgroup.normalClosure_le_normal
  rintro r ⟨i, j, a, b, h⟩
  rcases h with ⟨h, _⟩ | ⟨h, rfl⟩
  · exact h.elim
  · obtain ⟨rfl, rfl⟩ := chain_lt h
    change fromCoproduct (_ * _ * (_ * _)⁻¹) = 1
    simp only [map_mul, map_inv, mul_inv_eq_one]
    simp only [fromCoproduct, Monoid.CoprodI.lift_of]
    exact model_twist a b

private def toModel : Q →* Model :=
  QuotientGroup.lift _ fromCoproduct relators_in_kernel

private theorem toModel_factor (i : Fin 2) (b : ChainFactor i) :
    toModel (factor chain i b) = modelFactor i b := by
  exact Monoid.CoprodI.lift_of modelFactor b

private def projectTop : Q →* Upper :=
  (SemidirectProduct.rightHom : Model →* Upper).comp toModel

private theorem project_lower (b : ChainFactor 0) : projectTop (factor chain 0 b) = 1 :=
  congrArg (SemidirectProduct.rightHom : Model →* Upper) (toModel_factor 0 b)

private theorem project_upper (b : ChainFactor 1) : projectTop (factor chain 1 b) = b :=
  congrArg (SemidirectProduct.rightHom : Model →* Upper) (toModel_factor 1 b)

private theorem quotient_twist {I : Type} [PartialOrder I] {G : I → Type}
    [∀ i, Group (G i)] (S : QuandleSystem I G) {i j : I} (h : i < j)
    (a : G i) (b : G j) :
    let ba := (S.action j).apply b ⟨i, h⟩ a
    factor S i a * factor S j b = factor S j b * factor S ba.1.val ba.2 := by
  let ba := (S.action j).apply b ⟨i, h⟩ a
  let ai := Monoid.CoprodI.of a
  let bj := Monoid.CoprodI.of b
  let bai := Monoid.CoprodI.of ba.2
  have relator : ai * bj * (bj * bai)⁻¹ ∈ relators S :=
    ⟨i, j, a, b, Or.inr ⟨h, rfl⟩⟩
  have killed := (QuotientGroup.eq_one_iff (N := Subgroup.normalClosure (relators S)) _).2
    (Subgroup.subset_normalClosure relator)
  change (QuotientGroup.mk' _) (ai * bj * (bj * bai)⁻¹) = 1 at killed
  rw [map_mul, map_inv, map_mul, map_mul, mul_inv_eq_one] at killed
  exact killed

private abbrev lowerOne : Lower := Multiplicative.ofAdd 1
private abbrev lowerTwo : Lower := Multiplicative.ofAdd 2
private abbrev upperOne : Upper := Multiplicative.ofAdd 1
private abbrev upperTwo : Upper := Multiplicative.ofAdd 2
private def a : Q := factor chain 0 lowerOne
private def t : Q := factor chain 1 upperOne
private def H : Subgroup Q := standardParabolic chain {1}

private theorem a_sq : a ^ 2 = factor chain 0 lowerTwo :=
  (map_pow (factor chain 0) lowerOne 2).symm

private theorem t_sq : t ^ 2 = factor chain 1 upperTwo :=
  (map_pow (factor chain 1) upperOne 2).symm

private theorem H_eq_range : H = (factor chain 1).range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    rintro _ ⟨j, hj, b, rfl⟩
    have hj' := Set.mem_singleton_iff.mp hj
    subst j
    exact ⟨b, rfl⟩
  · rintro _ ⟨b, rfl⟩
    exact Subgroup.subset_closure ⟨1, rfl, b, rfl⟩

private theorem t_sq_mem_intersection :
    t ^ 2 ∈ H ⊓ H.map (MulAut.conj (a ^ 2)).toMonoidHom := by
  have inH : t ^ 2 ∈ H := by
    rw [t_sq, H_eq_range]
    exact ⟨upperTwo, rfl⟩
  have twist := quotient_twist chain (by decide : (0 : Fin 2) < 1) lowerTwo upperTwo
  change factor chain 0 lowerTwo * factor chain 1 upperTwo =
    factor chain 1 upperTwo * factor chain 0 (inverseAction upperTwo lowerTwo) at twist
  have fixed : inverseAction upperTwo lowerTwo = lowerTwo := by
    change (inverseAction upperTwo lowerTwo).toAdd = lowerTwo.toAdd
    rw [inverseAction_formula]
    decide
  rw [fixed, ← a_sq, ← t_sq] at twist
  refine ⟨inH, t ^ 2, inH, ?_⟩
  change a ^ 2 * t ^ 2 * (a ^ 2)⁻¹ = t ^ 2
  rw [twist, mul_inv_cancel_right]

private theorem model_intersection_restriction (b c : Upper)
    (same : modelInr b = modelInl lowerTwo * modelInr c * (modelInl lowerTwo)⁻¹) :
    b.toAdd = 0 ∨ b.toAdd = 2 := by
  have hright := congrArg SemidirectProduct.right same
  simp only [SemidirectProduct.right_inr, SemidirectProduct.right_inl,
    SemidirectProduct.mul_right, SemidirectProduct.inv_right, inv_one, one_mul, mul_one] at hright
  subst b
  have hleft := congrArg SemidirectProduct.left same
  have restrict : ∀ c : Upper,
      (modelInl lowerTwo * modelInr c * (modelInl lowerTwo)⁻¹).left = 1 →
        c.toAdd = 0 ∨ c.toAdd = 2 := by decide
  exact restrict c hleft.symm

private theorem intersection_top_image (j : Upper) :
    j ∈ (H ⊓ H.map (MulAut.conj (a ^ 2)).toMonoidHom).map projectTop ↔
      j.toAdd = 0 ∨ j.toAdd = 2 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨hH, y, hy, hyq⟩
    rw [H_eq_range] at hH hy
    obtain ⟨b, rfl⟩ := hH
    obtain ⟨c, rfl⟩ := hy
    change a ^ 2 * factor chain 1 c * (a ^ 2)⁻¹ = factor chain 1 b at hyq
    have same := congrArg toModel hyq
    rw [a_sq, map_mul, map_mul, map_inv, toModel_factor, toModel_factor, toModel_factor] at same
    rw [project_upper]
    exact model_intersection_restriction b c same.symm
  · rintro (zero | two)
    · have hj : j = 1 := zero
      rw [hj]
      exact Subgroup.one_mem _
    · have hj : j = upperTwo := two
      rw [hj]
      exact ⟨t ^ 2, t_sq_mem_intersection, by rw [t_sq, project_upper]⟩

private theorem project_conj (g : Q) (K : Subgroup Q) :
    (K.map (MulAut.conj g).toMonoidHom).map projectTop = K.map projectTop := by
  have unchanged : projectTop.comp (MulAut.conj g).toMonoidHom = projectTop := by
    apply MonoidHom.ext
    intro x
    change projectTop (g * x * g⁻¹) = projectTop x
    rw [map_mul, map_mul, map_inv, mul_comm (projectTop g), mul_inv_cancel_right]
  rw [Subgroup.map_map, unchanged]

private theorem parabolic_top_image (T : Set (Fin 2)) (g : Q) :
    let projection := ((standardParabolic chain T).map (MulAut.conj g).toMonoidHom).map projectTop
    projection = ⊥ ∨ projection = ⊤ := by
  dsimp only
  rw [project_conj]
  by_cases included : (1 : Fin 2) ∈ T
  · right
    apply top_unique
    intro b _
    exact ⟨factor chain 1 b, Subgroup.subset_closure ⟨1, included, b, rfl⟩, project_upper b⟩
  · left
    apply bot_unique
    rw [Subgroup.map_le_iff_le_comap]
    apply (Subgroup.closure_le _).2
    rintro _ ⟨j, hj, b, rfl⟩
    have notUpper : j.val ≠ 1 := by
      intro h
      have eq : j = 1 := Fin.ext h
      exact included (eq ▸ hj)
    have lower : j = 0 := Fin.ext (by have := j.isLt; omega)
    subst j
    exact Subgroup.mem_bot.mpr (project_lower b)

/-- The universal affirmative answer to Genevois's Question 9.4 fails. -/
theorem result : ¬ claim := by
  intro universal
  obtain ⟨T, g, equal⟩ :=
    universal (Fin 2) inferInstance ChainFactor chainGroup chain {1} {1} 1 (a ^ 2)
  change H.map (MulAut.conj (1 : Q)).toMonoidHom ⊓
    H.map (MulAut.conj (a ^ 2)).toMonoidHom =
      (standardParabolic chain T).map (MulAut.conj g).toMonoidHom at equal
  have identity : H.map (MulAut.conj (1 : Q)).toMonoidHom = H := by
    have conjOne : (MulAut.conj (1 : Q)).toMonoidHom = MonoidHom.id Q := by
      apply MonoidHom.ext
      intro x
      simp
    rw [conjOne, Subgroup.map_id]
  rw [identity] at equal
  have projected := congrArg (fun K : Subgroup Q => K.map projectTop) equal
  rcases parabolic_top_image T g with trivial | whole
  · have present := (intersection_top_image upperTwo).2 (Or.inr rfl)
    rw [projected, trivial] at present
    exact (by decide : upperTwo ≠ 1) (Subgroup.mem_bot.mp present)
  · have present : upperOne ∈ (H ⊓ H.map (MulAut.conj (a ^ 2)).toMonoidHom).map projectTop := by
      rw [projected, whole]
      exact Subgroup.mem_top _
    exact (by decide : ¬ (upperOne.toAdd = 0 ∨ upperOne.toAdd = 2))
      ((intersection_top_image upperOne).1 present)

end D5.S3.FiniteGroups.Quandles.GenevoisQ94Settlement
