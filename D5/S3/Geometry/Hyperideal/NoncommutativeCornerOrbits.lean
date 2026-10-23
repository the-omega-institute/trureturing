/- GID: D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits
   mirror-E: none(waiver:arbitrary-right-action-corner-orbit-characterization)
   anchors: []
   utility: none
   digest: Actual corner relations equal the prescribed nonnormal subgroup orbits. -/

import D5.S3.Geometry.Hyperideal.ActualCornerTransport
import Mathlib.Algebra.Group.Subgroup.MulOpposite
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open D5.S3.Geometry.Hyperideal.ActualCornerTransport
variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

def act (x : Ω) (g : G) : Ω := MulOpposite.op g • x

@[simp] lemma act_one (x : Ω) : act x (1 : G) = x := by simp [act]
lemma act_mul (x : Ω) (g h : G) : act (act x g) h = act x (g*h) := by
  simp only [act, MulOpposite.op_mul, mul_smul]

def facePair (u v : G) (c : Corner Ω) : Corner Ω :=
  ![(act c.1 u,3),(act c.1 v,2),(act c.1 v⁻¹,1),(act c.1 u⁻¹,0)] c.2

def slotMap (f : Fin 4) : Equiv.Perm (Fin 3) where
  toFun r := (![![0,1,2],![2,0,1],![1,2,0],![0,1,2]]) f r
  invFun r := (![![0,1,2],![1,2,0],![2,0,1],![0,1,2]]) f r
  left_inv := by intro r; fin_cases f <;> fin_cases r <;> decide
  right_inv := by intro r; fin_cases f <;> fin_cases r <;> decide

def pairing (u v : G) : Pairing Ω where
  p := facePair u v
  involutive := by
    rintro ⟨x,f⟩
    fin_cases f <;> simp [facePair,act_mul]
  fixedPointFree := by
    rintro ⟨x,f⟩ h
    have := congrArg Prod.snd h
    fin_cases f <;> simp [facePair] at this
  sigma c := slotMap c.2
  compatible := by
    rintro ⟨x,f⟩ r
    fin_cases f <;> fin_cases r <;> simp [facePair,slotMap]

def normalize (u : G) (c : Corner Ω) : Ω := act c.1 (u ^ c.2.val)
def sWord (u v : G) : G := (u ^ 2)⁻¹ * v
def tWord (u v : G) : G := (u ^ 3)⁻¹ * v * u
def kWord (u v : G) : G := v * u ^ 3
def boundaryGroup (u v : G) : Subgroup G :=
  Subgroup.closure ({sWord u v,tWord u v,kWord u v} : Set G)

lemma actual_step (u v : G) (x : Ω) (f : Fin 4) (r : Fin 3) :
    Relation.EqvGen (cornerRel (pairing u v)) (x,faceVertex f r)
      ((facePair u v (x,f)).1,
        faceVertex (facePair u v (x,f)).2 (slotMap f r)) :=
  Relation.EqvGen.rel _ _ ⟨((x,f),r),rfl,rfl⟩

private lemma normalize_path (u v : G) (c : Corner Ω) :
    Relation.EqvGen (cornerRel (pairing u v)) c (normalize u c,0) := by
  rcases c with ⟨x,j⟩
  fin_cases j
  · simpa [normalize] using (Relation.EqvGen.refl (x,0))
  · simpa [normalize,facePair,faceVertex,slotMap] using actual_step u v x 0 0
  · have h₁ : Relation.EqvGen (cornerRel (pairing u v)) (x,2) (act x u,1) := by
      simpa [facePair,faceVertex,slotMap] using actual_step u v x 0 1
    have h₂ : Relation.EqvGen (cornerRel (pairing u v)) (act x u,1)
        (act (act x u) u,0) := by
      simpa [facePair,faceVertex,slotMap] using actual_step u v (act x u) 0 0
    simpa [normalize,act_mul,pow_two] using Relation.EqvGen.trans _ _ _ h₁ h₂
  · have h₁ : Relation.EqvGen (cornerRel (pairing u v)) (x,3) (act x u,2) := by
      simpa [facePair,faceVertex,slotMap] using actual_step u v x 0 2
    have h₂ : Relation.EqvGen (cornerRel (pairing u v)) (act x u,2)
        (act (act x u) u,1) := by
      simpa [facePair,faceVertex,slotMap] using actual_step u v (act x u) 0 1
    have h₃ : Relation.EqvGen (cornerRel (pairing u v)) (act (act x u) u,1)
        (act (act (act x u) u) u,0) := by
      simpa [facePair,faceVertex,slotMap] using actual_step u v (act (act x u) u) 0 0
    simpa [normalize,act_mul,pow_succ,pow_two,mul_assoc] using Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ h₁ h₂) h₃

private lemma generator_path (u v : G) (g : G)
    (hg : g ∈ ({sWord u v,tWord u v,kWord u v} : Set G)) (x : Ω) :
    Relation.EqvGen (cornerRel (pairing u v)) (x,0) (act x g,0) := by
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · let y := act x (u ^ 2)⁻¹
    have hn : normalize u (y,2) = x := by simp [normalize,y,act_mul]
    have h₁ := (normalize_path u v (y,2)).symm
    have h₂ : Relation.EqvGen (cornerRel (pairing u v)) (y,2) (act y v,0) := by
      simpa [facePair,faceVertex,slotMap] using actual_step u v y 1 1
    simpa [hn,y,sWord,act_mul] using Relation.EqvGen.trans _ _ _ h₁ h₂
  · let y := act x (u ^ 3)⁻¹
    have hn : normalize u (y,3) = x := by simp [normalize,y,act_mul]
    have h₁ := (normalize_path u v (y,3)).symm
    have h₂ : Relation.EqvGen (cornerRel (pairing u v)) (y,3) (act y v,1) := by
      simpa [facePair,faceVertex,slotMap] using actual_step u v y 1 2
    have h₃ := normalize_path u v (act y v,1)
    simpa [hn,y,tWord,normalize,act_mul,mul_assoc] using Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ h₁ h₂) h₃
  · have h₁ : Relation.EqvGen (cornerRel (pairing u v)) (x,0) (act x v,3) := by
      simpa [facePair,faceVertex,slotMap] using actual_step u v x 1 0
    simpa [normalize,kWord,act_mul] using Relation.EqvGen.trans _ _ _ h₁ (normalize_path u v (act x v,3))

private lemma subgroup_path (u v : G) (g : G) (hg : g ∈ boundaryGroup u v) (x : Ω) :
    Relation.EqvGen (cornerRel (pairing u v)) (x,0) (act x g,0) := by
  have h : ∀ x : Ω, Relation.EqvGen (cornerRel (pairing u v)) (x,0) (act x g,0) := by
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact generator_path u v g hg
    | one => intro x; simpa using Relation.EqvGen.refl (x,0)
    | mul g h hg hh ihg ihh =>
      intro x
      simpa [act_mul] using Relation.EqvGen.trans _ _ _ (ihg x) (ihh (act x g))
    | inv g hg ih =>
      intro x
      simpa [act_mul] using (ih (act x g⁻¹)).symm
  exact h x

private lemma normalize_generator (u v : G) (c d : Corner Ω)
    (h : cornerRel (pairing u v) c d) :
    ∃ g ∈ boundaryGroup u v, act (normalize u c) g = normalize u d := by
  rcases h with ⟨⟨⟨x,f⟩,r⟩,rfl,rfl⟩
  have hs : sWord u v ∈ boundaryGroup u v := Subgroup.subset_closure (by simp)
  have ht : tWord u v ∈ boundaryGroup u v := Subgroup.subset_closure (by simp)
  have hk : kWord u v ∈ boundaryGroup u v := Subgroup.subset_closure (by simp)
  fin_cases f <;> fin_cases r
  all_goals dsimp only [b,J,pairing,facePair,faceVertex,slotMap,normalize]
  · exact ⟨1,(boundaryGroup u v).one_mem,by simp [act_mul,pow_succ,mul_assoc]⟩
  · exact ⟨1,(boundaryGroup u v).one_mem,by simp [act_mul,pow_succ,mul_assoc]⟩
  · exact ⟨1,(boundaryGroup u v).one_mem,by simp [act_mul,pow_succ,mul_assoc]⟩
  · exact ⟨kWord u v,hk,by simp [act_mul,kWord]⟩
  · exact ⟨sWord u v,hs,by simp [act_mul,sWord,mul_assoc]⟩
  · exact ⟨tWord u v,ht,by simp [act_mul,tWord,mul_assoc]⟩
  · exact ⟨(sWord u v)⁻¹,(boundaryGroup u v).inv_mem hs,by simp [act_mul,sWord]⟩
  · refine ⟨(tWord u v)⁻¹,(boundaryGroup u v).inv_mem ht,?_⟩
    simp [act_mul,tWord,mul_assoc]
  · exact ⟨(kWord u v)⁻¹,(boundaryGroup u v).inv_mem hk,by simp [act_mul,kWord]⟩
  · exact ⟨1,(boundaryGroup u v).one_mem,by simp [act_mul]⟩
  · exact ⟨1,(boundaryGroup u v).one_mem,by simp [act_mul,pow_succ,mul_assoc]⟩
  · exact ⟨1,(boundaryGroup u v).one_mem,by simp [act_mul,pow_succ,mul_assoc]⟩

theorem actual_corner_orbit_iff (u v : G) (c d : Corner Ω) :
    Relation.EqvGen (cornerRel (pairing u v)) c d ↔
      ∃ g ∈ boundaryGroup u v, act (normalize u c) g = normalize u d := by
  constructor
  · intro h
    induction h with
    | rel c d h => exact normalize_generator u v c d h
    | refl c => exact ⟨1,(boundaryGroup u v).one_mem,by simp⟩
    | symm c d h ih =>
      rcases ih with ⟨g,hg,heq⟩
      refine ⟨g⁻¹,(boundaryGroup u v).inv_mem hg,?_⟩
      rw [← heq,act_mul]
      simp
    | trans c d e hcd hde ihcd ihde =>
      rcases ihcd with ⟨g,hg,hgact⟩
      rcases ihde with ⟨h,hh,hhact⟩
      refine ⟨g*h,(boundaryGroup u v).mul_mem hg hh,?_⟩
      rw [← act_mul,hgact,hhact]
  · rintro ⟨g,hg,heq⟩
    have hp := subgroup_path u v g hg (normalize u c)
    rw [heq] at hp
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ (normalize_path u v c) hp) (normalize_path u v d).symm

end D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
