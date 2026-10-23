/- GID: D5/S3/ConceptDynamics/Fibers/ConfigurationReadout
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/ConfigurationReadout
   mirror-E: none(waiver:content-registration-pending)
   anchors: []
   utility: none
   digest: Actual legal configuration edge maps admit a faithful optional completion and local diamond criterion. -/

import D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option relaxedAutoImplicit false
open D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
open D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
namespace D5.S3.ConceptDynamics.Fibers.ConfigurationReadout
universe u v
variable {E : Type u} [PartialOrder E] (compatible : Finset E → Prop)

/-- Only legal finite configurations have original fibres. Maps are supplied on actual basic edges. -/
structure LocalReadout where
  fibre : FiniteConfigurations compatible → Type v
  edge : ∀ (C D : FiniteConfigurations compatible) (e : E),
    Enabled C.1 e → D.1 = insert e C.1 → fibre C → fibre D

abbrev Legal (K : Set E) := K.Finite ∧ Configuration compatible K

/-- None completes illegal vertices without choosing any vector in an original fibre.
At a legal vertex Some embeds the original state injectively. -/
def optionalReadout (R : LocalReadout compatible) : DependentReadout E := by
  classical
  exact {
  fibre := fun K => Option (Σ' h : Legal compatible K, R.fibre ⟨K,h⟩)
  edge := fun {K} {e} hen x => match x with
    | none => none
    | some ⟨h,s⟩ => if hd : Legal compatible (insert e K) then
        some ⟨hd,R.edge ⟨K,h⟩ ⟨insert e K,hd⟩ e hen rfl s⟩ else none }

private theorem optional_none (R : LocalReadout compatible) {K : Set E} {e : E}
    (hen : Enabled K e) : (optionalReadout compatible R).edge hen none = none := rfl

private theorem optional_illegal (R : LocalReadout compatible) {K : Set E} {e : E}
    (hen : Enabled K e) (hn : ¬ Legal compatible (insert e K))
    (x : (optionalReadout compatible R).fibre K) :
    (optionalReadout compatible R).edge hen x = none := by
  cases x with
  | none => rfl
  | some q => cases q; simp [optionalReadout,hn]

@[simp] private theorem optional_cast_none (R : LocalReadout compatible)
    {K L : Set E} (h : K = L) :
    Eq.rec (motive := fun L (_ : K = L) => (optionalReadout compatible R).fibre L)
      (none : (optionalReadout compatible R).fibre K) h =
      (none : (optionalReadout compatible R).fibre L) := by
  cases h
  rfl

/-- The two paths contain precisely two actual basic edges and have a legal common endpoint. -/
def LegalDiamonds (R : LocalReadout compatible) : Prop :=
  ∀ (C D : FiniteConfigurations compatible) (a b : E)
    (ha : Enabled C.1 a) (hb : Enabled C.1 b)
    (hab : Enabled (insert a C.1) b) (hba : Enabled (insert b C.1) a)
    (he : D.1 = insert b (insert a C.1)) (s : R.fibre C),
    pathMap (optionalReadout compatible R) [a,b]
      (show Exec C.1 [a,b] D.1 from ⟨ha,hab,he.symm⟩) (some ⟨C.2,s⟩) =
    pathMap (optionalReadout compatible R) [b,a]
      (show Exec C.1 [b,a] D.1 from ⟨hb,hba,(Set.insert_comm a b C.1).trans he.symm⟩)
      (some ⟨C.2,s⟩)

/-- Equality of the completed values at Some is equality in the original endpoint fibre. -/
def LegalPathIndependent (R : LocalReadout compatible) : Prop :=
  ∀ (C D : FiniteConfigurations compatible) (l m : List E)
    (hl : Exec C.1 l D.1) (hm : Exec C.1 m D.1) (s : R.fibre C),
    pathMap (optionalReadout compatible R) l hl (some ⟨C.2,s⟩) =
      pathMap (optionalReadout compatible R) m hm (some ⟨C.2,s⟩)

/-- The only added state is None. Illegal endpoint diamonds are forced to None, while every
legal endpoint diamond is the original two-edge composite. No full-path swap law is assumed. -/
private theorem legal_pathIndependent_iff_diamonds (R : LocalReadout compatible) :
    LegalPathIndependent compatible R ↔ LegalDiamonds compatible R := by
  constructor
  · intro hi C D a b ha hb hab hba he s
    exact hi C D [a,b] [b,a] _ _ s
  · intro hd
    have hall : DiamondCompatible (optionalReadout compatible R) := by
      intro K a b hK hf ha hb hab hba x
      cases x with
      | none => simp only [pathMap,optional_none,optional_cast_none]
      | some q =>
        obtain ⟨h,s⟩ := q
        by_cases hD : Legal compatible (insert b (insert a K))
        · exact hd ⟨K,h⟩ ⟨insert b (insert a K),hD⟩ a b ha hb hab hba rfl s
        · have hn : ¬ Legal compatible (insert a (insert b K)) := by
            simpa only [Set.insert_comm a b K] using hD
          simp only [pathMap]
          rw [optional_illegal compatible R hab hD,
            optional_illegal compatible R hba hn]
          simp only [optional_cast_none]
    intro C D l m hl hm s
    exact (pathIndependent_iff_diamondCompatible _).mpr hall C.2.2.1 D.2.2.1 D.2.1
      l m hl hm (some ⟨C.2,s⟩)

private theorem exec_subset {I J : Set E} {l : List E} (hl : Exec I l J) : I ⊆ J := by
  induction l generalizing I with
  | nil => cases hl; exact Set.Subset.rfl
  | cons e l ih => exact Set.subset_insert e I |>.trans (ih hl.2)

private theorem legal_insert (C D : FiniteConfigurations compatible) {e : E} {l : List E}
    (he : Enabled C.1 e) (hl : Exec (insert e C.1) l D.1) :
    Legal compatible (insert e C.1) := by
  refine ⟨C.2.1.insert e, ?_, ?_⟩
  · intro a b hab hb
    rcases hb with hbe | hb
    · subst a
      by_cases hb : b = e
      · exact Or.inl hb
      · exact Or.inr (he.2 b (lt_of_le_of_ne hab hb))
    · exact Or.inr (C.2.2.1 hab hb)
  · intro t ht
    exact D.2.2.2 t (ht.trans (exec_subset hl))

/-- Every legal execution remains in original fibres; the optional completion cannot discard it. -/
private theorem path_some (R : LocalReadout compatible) (C D : FiniteConfigurations compatible)
    (l : List E) (hl : Exec C.1 l D.1) (x : R.fibre C) :
    ∃ y : R.fibre D, pathMap (optionalReadout compatible R) l hl (some ⟨C.2,x⟩) =
      some ⟨D.2,y⟩ := by
  induction l generalizing C with
  | nil =>
    have hCD : C = D := Subtype.ext hl
    subst D
    exact ⟨x,rfl⟩
  | cons e l ih =>
    let hN := legal_insert compatible C D hl.1 hl.2
    let N : FiniteConfigurations compatible := ⟨insert e C.1,hN⟩
    obtain ⟨y,hy⟩ := ih N hl.2 (R.edge C N e hl.1 rfl x)
    refine ⟨y,?_⟩
    simpa only [pathMap,optionalReadout,dif_pos hN] using hy

/-- The genuine endpoint composite, extracted from its proved Some value. -/
def legalPathMap (R : LocalReadout compatible) (C D : FiniteConfigurations compatible)
    (l : List E) (hl : Exec C.1 l D.1) (x : R.fibre C) : R.fibre D :=
  Classical.choose (path_some compatible R C D l hl x)

private theorem legalPathMap_spec (R : LocalReadout compatible) (C D : FiniteConfigurations compatible)
    (l : List E) (hl : Exec C.1 l D.1) (x : R.fibre C) :
    pathMap (optionalReadout compatible R) l hl (some ⟨C.2,x⟩) =
      some ⟨D.2,legalPathMap compatible R C D l hl x⟩ :=
  Classical.choose_spec (path_some compatible R C D l hl x)

/-- Legal path independence is equality of the actual original endpoint maps. -/
theorem actual_path_composition_iff (R : LocalReadout compatible) :
    (∀ (C D : FiniteConfigurations compatible) (l m : List E)
      (hl : Exec C.1 l D.1) (hm : Exec C.1 m D.1) (x : R.fibre C),
      legalPathMap compatible R C D l hl x = legalPathMap compatible R C D m hm x) ↔
      LegalDiamonds compatible R := by
  rw [← legal_pathIndependent_iff_diamonds compatible R]
  constructor
  · intro h C D l m hl hm x
    rw [legalPathMap_spec compatible R C D l hl x,legalPathMap_spec compatible R C D m hm x,
      h C D l m hl hm x]
  · intro h C D l m hl hm x
    have hh := h C D l m hl hm x
    rw [legalPathMap_spec compatible R C D l hl x,legalPathMap_spec compatible R C D m hm x] at hh
    exact eq_of_heq (PSigma.mk.inj (Option.some.inj hh)).2

def emptyConfiguration (hempty : compatible ∅) : FiniteConfigurations compatible :=
  ⟨∅,Set.finite_empty,by
    refine ⟨by simp [IsLowerSet],?_⟩
    intro t ht
    have : t = ∅ := by simpa using ht
    simpa [this] using hempty⟩

def StaticCompatible (R : LocalReadout compatible)
    (f : ∀ C, R.fibre C) : Prop :=
  ∀ C D e (hen : Enabled C.1 e) (he : D.1 = insert e C.1),
    R.edge C D e hen he (f C) = f D

private theorem one_edge (R : LocalReadout compatible) (C D : FiniteConfigurations compatible)
    (e : E) (hen : Enabled C.1 e) (he : D.1 = insert e C.1) (x : R.fibre C) :
    pathMap (optionalReadout compatible R) [e] ⟨hen,he.symm⟩ (some ⟨C.2,x⟩) =
      some ⟨D.2,R.edge C D e hen he x⟩ := by
  rcases C with ⟨C,hC⟩
  rcases D with ⟨D,hD⟩
  dsimp at he
  subst D
  change (optionalReadout compatible R).edge hen (some ⟨hC,x⟩) = _
  dsimp only [optionalReadout]
  rw [dif_pos hD]

private theorem section_paths (R : LocalReadout compatible) (f : ∀ C, R.fibre C)
    (hf : StaticCompatible compatible R f) (C D : FiniteConfigurations compatible)
    (l : List E) (hl : Exec C.1 l D.1) :
    pathMap (optionalReadout compatible R) l hl (some ⟨C.2,f C⟩) = some ⟨D.2,f D⟩ := by
  induction l generalizing C with
  | nil => have he : C = D := Subtype.ext hl; subst D; rfl
  | cons e l ih =>
    let hN := legal_insert compatible C D hl.1 hl.2
    let N : FiniteConfigurations compatible := ⟨insert e C.1,hN⟩
    have hstep := hf C N e hl.1 rfl
    have ht := ih N hl.2
    change pathMap (optionalReadout compatible R) l hl.2
      ((optionalReadout compatible R).edge hl.1 (some ⟨C.2,f C⟩)) = _
    have hopt : (optionalReadout compatible R).edge hl.1 (some ⟨C.2,f C⟩) =
        some ⟨hN,f N⟩ := by
      dsimp only [optionalReadout]
      rw [dif_pos hN]
      change (some ⟨hN,R.edge C N e hl.1 rfl (f C)⟩ :
        (optionalReadout compatible R).fibre (insert e C.1)) = some ⟨hN,f N⟩
      rw [hstep]
    rw [hopt]
    exact ht

/-- An empty-configuration reference value uniquely determines a static compatible assignment.
The proof uses actual legal edge composition, not a postulated family of full-path maps. -/
theorem static_assignment_unique (R : LocalReadout compatible) (hempty : compatible ∅)
    (hd : LegalDiamonds compatible R) (x : R.fibre (emptyConfiguration compatible hempty)) :
    ∃! f : ∀ C, R.fibre C, f (emptyConfiguration compatible hempty) = x ∧
      StaticCompatible compatible R f := by
  classical
  let O := emptyConfiguration compatible hempty
  have execution (C : FiniteConfigurations compatible) : ∃ l, Exec O.1 l C.1 :=
    (exec_exists_iff_subset O.2.2.1 C.2.2.1 C.2.1).mpr (Set.empty_subset _)
  let p (C : FiniteConfigurations compatible) := Classical.choose (execution C)
  have hp (C : FiniteConfigurations compatible) := Classical.choose_spec (execution C)
  let f (C : FiniteConfigurations compatible) := legalPathMap compatible R O C (p C) (hp C) x
  have hf (C : FiniteConfigurations compatible) :
      pathMap (optionalReadout compatible R) (p C) (hp C) (some ⟨O.2,x⟩) = some ⟨C.2,f C⟩ :=
    legalPathMap_spec compatible R O C (p C) (hp C) x
  have hi := (legal_pathIndependent_iff_diamonds compatible R).mpr hd
  have hroot : f O = x := by
    have hh := hi O O (p O) [] (hp O) rfl x
    rw [hf O] at hh
    exact eq_of_heq (PSigma.mk.inj (Option.some.inj hh)).2
  have hpar : StaticCompatible compatible R f := by
    intro C D e hen he
    let hs : Exec C.1 [e] D.1 := ⟨hen,he.symm⟩
    have hh := hi O D ((p C) ++ [e]) (p D) (exec_append (hp C) hs) (hp D) x
    rw [pathMap_append _ (hp C) hs, hf C, one_edge compatible R C D e hen he, hf D] at hh
    exact eq_of_heq (PSigma.mk.inj (Option.some.inj hh)).2
  refine ⟨f,⟨hroot,hpar⟩,?_⟩
  intro g hg
  funext C
  have hh := section_paths compatible R g hg.2 O C (p C) (hp C)
  rw [hg.1,hf C] at hh
  exact (eq_of_heq (PSigma.mk.inj (Option.some.inj hh)).2).symm

#print axioms actual_path_composition_iff
#print axioms static_assignment_unique
#print axioms legal_pathIndependent_iff_diamonds
end D5.S3.ConceptDynamics.Fibers.ConfigurationReadout
