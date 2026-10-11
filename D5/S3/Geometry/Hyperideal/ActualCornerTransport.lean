/- GID: D5/S3/Geometry/Hyperideal/ActualCornerTransport
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/ActualCornerTransport
   mirror-E: none(waiver:arbitrary-finite-actual-face-pairing)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected]
   utility: none
   digest: Actual paired-corner paths lift weighted component transport with the six-slot bound. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Quotient
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.Hyperideal.ActualCornerTransport

abbrev Corner (T : Type*) := T × Fin 4
abbrev Occurrence (T : Type*) := T × Fin 6
abbrev Slot (T : Type*) := (T × Fin 4) × Fin 3

/-- The whole-face pairing and its compatible permutation of opposite-edge/corner slots. -/
structure Pairing (T : Type*) where
  p : Corner T → Corner T
  involutive : Function.Involutive p
  fixedPointFree : ∀ x, p x ≠ x
  sigma : Corner T → Equiv.Perm (Fin 3)
  compatible : ∀ x r, sigma (p x) (sigma x r) = r

/-- A face omits its numbered vertex; its slots are the other vertices in increasing order. -/
def faceVertex (f : Fin 4) (r : Fin 3) : Fin 4 :=
  ![![1,2,3], ![0,2,3], ![0,1,3], ![0,1,2]] f r

/-- Edges are ordered (12,13,14,34,24,23); a slot is opposite its corner. -/
def faceEdge (f : Fin 4) (r : Fin 3) : Fin 6 :=
  ![![3,4,5], ![3,2,1], ![4,2,0], ![5,1,0]] f r

def endpoints (j : Fin 6) : Fin 4 × Fin 4 :=
  ![(0,1),(0,2),(0,3),(2,3),(1,3),(1,2)] j

def b {T : Type*} (i : Slot T) : Corner T := (i.1.1, faceVertex i.1.2 i.2)

def J {T : Type*} (q : Pairing T) (i : Slot T) : Slot T :=
  (q.p i.1, q.sigma i.1 i.2)

def edge {T : Type*} (i : Slot T) : Occurrence T := (i.1.1, faceEdge i.1.2 i.2)

def cornerRel {T : Type*} (q : Pairing T) (c d : Corner T) : Prop :=
  ∃ i, b i = c ∧ b (J q i) = d

def edgeRel {T : Type*} (q : Pairing T) (o z : Occurrence T) : Prop :=
  ∃ i, edge i = o ∧ edge (J q i) = z

abbrev Vertex {T : Type*} (q : Pairing T) := Quotient (Relation.EqvGen.setoid (cornerRel q))
abbrev GlobalEdge {T : Type*} (q : Pairing T) := Quotient (Relation.EqvGen.setoid (edgeRel q))

def label {T : Type*} (q : Pairing T) (c : Corner T) : Vertex q := Quotient.mk _ c
def P {T : Type*} (q : Pairing T) (o : Occurrence T) : GlobalEdge q := Quotient.mk _ o

variable {T S K : Type*} [Fintype T] [Fintype S]
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def M (q : Pairing T) (a : Occurrence T → K) (e : GlobalEdge q) : K := by
  classical
  exact ∑ o, if P q o = e then a o else 0

def Q (a : Occurrence T → K) (c : Corner T) : K := by
  classical
  exact ∑ j : Fin 6, if c.2 = (endpoints j).1 ∨ c.2 = (endpoints j).2 then a (c.1,j) else 0

/-- Contributions are summed by local slot occurrence, including every repeated global label. -/
def localLift (i : Slot T) (o : Occurrence T) : K := by
  classical
  exact ∑ r : Fin 3, if (i.1.1,faceEdge i.1.2 r) = o then
    (if i.2 = r then (1:K)/2 else -1/2) else 0

/-- The actual oriented slots form a path from u to v. -/
def Follows (q : Pairing T) : Corner T → Corner T → List (Slot T) → Prop
  | u, v, [] => u = v
  | u, v, i::is => b i = u ∧ Follows q (b (J q i)) v is

def chi (q : Pairing T) (paths : S → List (Slot T)) (s : S) (i : Slot T) : ℤ := by
  classical
  exact (paths s).count i - ((paths s).count (J q i) : ℤ)

def load (q : Pairing T) (paths : S → List (Slot T)) (w : S → K) (i : Slot T) : K :=
  ∑ s, w s * (chi q paths s i : K)

def lift (q : Pairing T) (paths : S → List (Slot T)) (w : S → K) (o : Occurrence T) : K :=
  ∑ i : Slot T, load q paths w i * localLift i o

def mass (q : Pairing T) (u : S → Corner T) (w : S → K) (v : Vertex q) : K := by
  classical
  exact ∑ s, if label q (u s) = v then w s else 0

/-- The entire actual path, signed-count, component-load and bounded-lifting contract. -/
def Transport (q : Pairing T) (u v : S → Corner T) (w : S → K) (B : K) : Prop := by
  classical
  exact ∃ paths : S → List (Slot T),
    (∀ s, Follows q (u s) (v s) (paths s)) ∧
    (∀ s, (u s :: (paths s).map (fun i => b (J q i))).Nodup) ∧
    (∀ s, u s = v s → paths s = []) ∧
    (∀ s i, (paths s).count i ≤ 1) ∧
    (∀ s i, chi q paths s (J q i) = -chi q paths s i) ∧
    (∀ s i, |chi q paths s i| ≤ 1) ∧
    (∀ s i, label q (b i) ≠ label q (u s) → chi q paths s i = 0) ∧
    (∀ s c, ∑ i : Slot T, (chi q paths s i : K) * (if b i = c then 1 else 0) =
      (if u s = c then 1 else 0) - (if v s = c then 1 else 0)) ∧
    (∀ i, load q paths w (J q i) = -load q paths w i) ∧
    (∀ i, |load q paths w i| ≤ mass q u w (label q (b i))) ∧
    (∀ e, M q (lift q paths w) e = 0) ∧
    (∀ c, -Q (lift q paths w) c =
      ∑ s, w s * ((if u s = c then 1 else 0) - (if v s = c then 1 else 0))) ∧
    (∀ o, |lift q paths w o| ≤ 3 * B)

set_option maxHeartbeats 2000000 in
-- The proof checks every local face/corner and edge/face/slot coefficient.
set_option maxRecDepth 10000 in
/-- Actual face-pairing-generated paths admit componentwise bounded occurrence lifts. -/
theorem actual_corner_transport (q : Pairing T) (u v : S → Corner T) (w : S → K)
    (same : ∀ s, label q (u s) = label q (v s))
    (nonneg : ∀ s, 0 ≤ w s) (B : K)
    (bounded : ∀ z : Vertex q, mass q u w z ≤ B) :
    Transport q u v w B := by
  classical
  have jj : Function.Involutive (J q) := by
    intro i
    apply Prod.ext
    · exact q.involutive i.1
    · exact q.compatible i.1 i.2
  have jj_apply (i : Slot T) : J q (J q i) = i := jj i
  let je : Slot T ≃ Slot T := { toFun := J q, invFun := J q, left_inv := jj, right_inv := jj }
  have labels (i : Slot T) : label q (b i) = label q (b (J q i)) :=
    Quotient.sound (Relation.EqvGen.rel _ _ ⟨i,rfl,rfl⟩)
  let G : SimpleGraph (Corner T) := {
    Adj := fun x y => x ≠ y ∧ cornerRel q x y
    symm := ⟨by
      rintro x y ⟨hne,i,hi,hj⟩
      refine ⟨hne.symm,J q i,hj,?_⟩
      simpa [jj i] using hi⟩
    loopless := ⟨fun x h => h.1 rfl⟩ }
  have reachable {x y : Corner T} (h : label q x = label q y) : G.Reachable x y := by
    have he : Relation.EqvGen (cornerRel q) x y := Quotient.exact h
    clear h
    induction he with
    | rel x y h =>
      by_cases hxy : x = y
      · subst y; exact SimpleGraph.Reachable.refl x
      · exact SimpleGraph.Adj.reachable (show G.Adj x y from ⟨hxy,h⟩)
    | refl x => exact SimpleGraph.Reachable.refl x
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have actual_lift {x y : Corner T} (p : G.Walk x y) :
      ∃ is : List (Slot T), Follows q x y is ∧
        (x :: is.map (fun i => b (J q i))) = p.support ∧
        is.map (fun i => s(b i,b (J q i))) = p.edges := by
    induction p with
    | nil => exact ⟨[],rfl,rfl,rfl⟩
    | @cons x y z h p ih =>
      obtain ⟨is,hfollow,hsupport,hedges⟩ := ih
      obtain ⟨i,hi,hj⟩ := h.2
      refine ⟨i::is,⟨hi,?_⟩,?_,?_⟩
      · simpa [hj] using hfollow
      · simpa [List.map_cons,SimpleGraph.Walk.support_cons,hj] using congrArg (x :: ·) hsupport
      · simpa [List.map_cons,SimpleGraph.Walk.edges_cons,hi,hj] using
          congrArg (s(x,y) :: ·) hedges
  have paths_exist (s : S) : ∃ is : List (Slot T), Follows q (u s) (v s) is ∧
      (u s :: is.map (fun i => b (J q i))).Nodup ∧ is.Nodup := by
    obtain ⟨p,hp⟩ := (reachable (same s)).exists_isPath
    obtain ⟨is,hfollow,hsupport,hedges⟩ := actual_lift p
    refine ⟨is,hfollow,hsupport ▸ hp.support_nodup,?_⟩
    have hn : (is.map (fun i => s(b i,b (J q i)))).Nodup := hedges ▸ hp.isTrail.edges_nodup
    exact List.Nodup.of_map _ hn
  choose paths follows simple nodup using paths_exist
  have nilpath (s : S) (h : u s = v s) : paths s = [] := by
    have ends : ∀ {x y : Corner T} {is : List (Slot T)}, Follows q x y is →
        y ∈ x :: is.map (fun i => b (J q i)) := by
      intro x y is hf
      induction is generalizing x with
      | nil => simpa [Follows] using hf.symm
      | cons i is ih => exact List.mem_cons_of_mem _ (ih hf.2)
    cases he : paths s with
    | nil => rfl
    | cons i is =>
      have hf := follows s
      rw [he] at hf
      have hm := ends hf.2
      have hs := simple s
      rw [he,List.map_cons,List.nodup_cons] at hs
      exact False.elim (hs.1 (h ▸ hm))
  have counts (s : S) (i : Slot T) : (paths s).count i ≤ 1 :=
    List.nodup_iff_count_le_one.mp (nodup s) i
  have anti (s : S) (i : Slot T) : chi q paths s (J q i) = -chi q paths s i := by
    simp only [chi,jj i]
    ring
  have chi_bound (s : S) (i : Slot T) : |chi q paths s i| ≤ 1 := by
    have h₁ := counts s i
    have h₂ := counts s (J q i)
    simp only [chi,abs_le]
    constructor <;> omega
  have in_component : ∀ {x y : Corner T} {is : List (Slot T)}, Follows q x y is →
      ∀ i ∈ is, label q (b i) = label q x := by
    intro x y is hf
    induction is generalizing x with
    | nil => simp
    | cons j is ih =>
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact congrArg (label q) hf.1
      · exact (ih hf.2 i hi).trans ((labels j).symm.trans (congrArg (label q) hf.1))
  have support (s : S) (i : Slot T) (h : label q (b i) ≠ label q (u s)) :
      chi q paths s i = 0 := by
    have hi : i ∉ paths s := fun hi => h (in_component (follows s) i hi)
    have hji : J q i ∉ paths s := fun hi => h ((labels i).trans (in_component (follows s) _ hi))
    simp [chi,List.count_eq_zero.mpr hi,List.count_eq_zero.mpr hji]
  have count_sum (is : List (Slot T)) (f : Slot T → K) :
      (∑ i : Slot T, (is.count i : K) * f i) = (is.map f).sum := by
    rw [Finset.sum_list_map_count]
    simp only [nsmul_eq_mul]
    symm
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
      (Finset.sum_subset
        (s₁ := is.toFinset) (s₂ := (Finset.univ : Finset (Slot T)))
        (f := fun i : Slot T => (is.count i : K) * f i)
        (Finset.subset_univ is.toFinset) (by
          intro i _ hi
          simp only [List.mem_toFinset] at hi
          simp [List.count_eq_zero.mpr hi]))
  have telescoping : ∀ {x y : Corner T} {is : List (Slot T)}, Follows q x y is →
      ∀ c : Corner T,
      (is.map (fun i => ((if b i = c then 1 else 0) -
        (if b (J q i) = c then 1 else 0) : K))).sum =
      (if x = c then 1 else 0) - (if y = c then 1 else 0) := by
    intro x y is hf
    induction is generalizing x with
    | nil =>
      change x = y at hf
      subst y
      simp
    | cons i is ih =>
      intro c
      rw [List.map_cons,List.sum_cons,ih hf.2 c,hf.1]
      ring
  have divergence (s : S) (c : Corner T) :
      (∑ i : Slot T, (chi q paths s i : K) * (if b i = c then 1 else 0)) =
      (if u s = c then 1 else 0) - (if v s = c then 1 else 0) := by
    simp only [chi,Int.cast_sub,Int.cast_natCast,sub_mul,Finset.sum_sub_distrib]
    have reindex := je.sum_comp (fun i => ((paths s).count (J q i) : K) *
      (if b i = c then 1 else 0))
    dsimp only [je] at reindex
    change (∑ i, ((paths s).count (J q (J q i)) : K) *
      (if b (J q i) = c then 1 else 0)) = _ at reindex
    simp only [jj_apply] at reindex
    change (∑ i, ((paths s).count i : K) * (if b (J q i) = c then 1 else 0)) =
      ∑ i, ((paths s).count (J q i) : K) * (if b i = c then 1 else 0) at reindex
    rw [← reindex]
    simp_rw [← Finset.sum_sub_distrib,← mul_sub]
    rw [count_sum]
    exact telescoping (follows s) c
  have load_anti (i : Slot T) : load q paths w (J q i) = -load q paths w i := by
    simp [load,anti,Finset.sum_neg_distrib]
  have load_bound (i : Slot T) : |load q paths w i| ≤ mass q u w (label q (b i)) := by
    unfold load mass
    calc
      |∑ s, w s * (chi q paths s i : K)| ≤ ∑ s, |w s * (chi q paths s i : K)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, if label q (u s) = label q (b i) then w s else 0 := by
        apply Finset.sum_le_sum
        intro s _
        split_ifs with h
        · rw [abs_mul,abs_of_nonneg (nonneg s)]
          have hc : |(chi q paths s i : K)| ≤ 1 := by
            exact_mod_cast chi_bound s i
          simpa using mul_le_mul_of_nonneg_left hc (nonneg s)
        · have hc := support s i (Ne.symm h)
          simp [hc]
  have qlocal (i : Slot T) (c : Corner T) :
      Q (localLift i : Occurrence T → K) c = -(if b i = c then 1 else 0) := by
    rcases i with ⟨⟨t,f⟩,r⟩
    rcases c with ⟨t',z⟩
    by_cases ht : t = t'
    · subst t'
      fin_cases f <;> fin_cases r <;> fin_cases z <;>
        norm_num [Q,localLift,b,faceVertex,faceEdge,endpoints,Fin.sum_univ_succ] <;>
        simp only [Fin.ext_iff] <;> norm_num
    · simp [Q,localLift,b,Prod.mk.injEq,ht]
  have edge_labels (i : Slot T) : P q (edge i) = P q (edge (J q i)) :=
    Quotient.sound (Relation.EqvGen.rel _ _ ⟨i,rfl,rfl⟩)
  have mform (i : Slot T) (e : GlobalEdge q) :
      M q (localLift i : Occurrence T → K) e =
        ∑ r : Fin 3, (if i.2 = r then (1:K)/2 else -1/2) *
          (if P q (i.1.1,faceEdge i.1.2 r) = e then 1 else 0) := by
    unfold M localLift
    calc
      (∑ o : Occurrence T, if P q o = e then
          ∑ r : Fin 3, if (i.1.1,faceEdge i.1.2 r) = o then
            (if i.2 = r then (1:K)/2 else -1/2) else 0 else 0) =
        ∑ o : Occurrence T, ∑ r : Fin 3,
          if (i.1.1,faceEdge i.1.2 r) = o then
            (if P q o = e then (if i.2 = r then (1:K)/2 else -1/2) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro o _
        split_ifs with h
        · apply Finset.sum_congr rfl
          intro r _
          simp
        · simp
      _ = _ := by
        rw [Finset.sum_comm]
        simp [eq_comm,mul_ite]
  have mlocal (i : Slot T) (e : GlobalEdge q) :
      M q (localLift (J q i) : Occurrence T → K) e = M q (localLift i) e := by
    rw [mform,mform,← Equiv.sum_comp (q.sigma i.1) (fun r : Fin 3 =>
      (if (J q i).2 = r then (1:K)/2 else -1/2) *
        (if P q ((J q i).1.1,faceEdge (J q i).1.2 r) = e then 1 else 0))]
    apply Finset.sum_congr rfl
    intro r _
    have he := edge_labels (i.1,r)
    change P q (i.1.1,faceEdge i.1.2 r) =
      P q ((q.p i.1).1,faceEdge (q.p i.1).2 (q.sigma i.1 r)) at he
    simp only [J,Equiv.apply_eq_iff_eq,← he]
  have mlinear (e : GlobalEdge q) :
      M q (lift q paths w) e = ∑ i : Slot T, load q paths w i * M q (localLift i) e := by
    unfold M lift
    calc
      (∑ o : Occurrence T, if P q o = e then
        ∑ i : Slot T, load q paths w i * localLift i o else 0) =
          ∑ o : Occurrence T, ∑ i : Slot T,
            load q paths w i * (if P q o = e then localLift i o else 0) := by
        apply Finset.sum_congr rfl
        intro o _
        split_ifs <;> simp
      _ = _ := by rw [Finset.sum_comm]; simp [Finset.mul_sum]
  have zeroM (e : GlobalEdge q) : M q (lift q paths w) e = 0 := by
    rw [mlinear]
    have hre := je.sum_comp (fun i => load q paths w i * M q (localLift i) e)
    dsimp only [je] at hre
    change (∑ i, load q paths w (J q i) * M q (localLift (J q i)) e) = _ at hre
    simp only [load_anti,mlocal,neg_mul,Finset.sum_neg_distrib] at hre
    linarith
  have qlinear (c : Corner T) :
      Q (lift q paths w) c = ∑ i : Slot T, load q paths w i * Q (localLift i) c := by
    unfold Q lift
    calc
      (∑ j : Fin 6, if c.2 = (endpoints j).1 ∨ c.2 = (endpoints j).2 then
        ∑ i : Slot T, load q paths w i * localLift i (c.1,j) else 0) =
          ∑ j : Fin 6, ∑ i : Slot T, load q paths w i *
            (if c.2 = (endpoints j).1 ∨ c.2 = (endpoints j).2 then localLift i (c.1,j) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      _ = _ := by rw [Finset.sum_comm]; simp [Finset.mul_sum]
  have deficit (c : Corner T) : -Q (lift q paths w) c =
      ∑ s, w s * ((if u s = c then 1 else 0) - (if v s = c then 1 else 0)) := by
    rw [qlinear]
    simp_rw [qlocal,mul_neg,Finset.sum_neg_distrib,neg_neg]
    unfold load
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc,← Finset.mul_sum,divergence]
  have global_load (i : Slot T) : |load q paths w i| ≤ B :=
    (load_bound i).trans (bounded _)
  have local_bound (o : Occurrence T) : |lift q paths w o| ≤ 3 * B := by
    have Bnonneg : 0 ≤ B := (abs_nonneg (load q paths w ((o.1,0),0))).trans (global_load _)
    unfold lift
    have component_zero (i : Slot T) (h : i.1.1 ≠ o.1) :
        (localLift i o : K) = 0 := by
      unfold localLift
      apply Finset.sum_eq_zero
      intro r _
      rw [if_neg (fun he => h (congrArg Prod.fst he))]
    have tetra_sum : (∑ i : Slot T, load q paths w i * localLift i o) =
      ∑ f : Fin 4, ∑ r : Fin 3, load q paths w ((o.1,f),r) * localLift ((o.1,f),r) o := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      apply Finset.sum_eq_single o.1
      · intro t _ ht
        apply Finset.sum_eq_zero
        intro f _
        apply Finset.sum_eq_zero
        intro r _
        rw [component_zero ((t,f),r) ht,mul_zero]
      · simp
    rw [tetra_sum]
    have lift_abs (f : Fin 4) (r : Fin 3) :
        |(localLift ((o.1,f),r) o : K)| =
          if f = (endpoints o.2).1 ∨ f = (endpoints o.2).2 then 0 else (1:K)/2 := by
      rcases o with ⟨t,j⟩
      fin_cases j <;> fin_cases f <;> fin_cases r <;>
        norm_num [localLift,faceEdge,endpoints,Fin.sum_univ_succ] <;>
        simp only [Fin.ext_iff] <;> norm_num
    calc
      |∑ f : Fin 4, ∑ r : Fin 3, load q paths w ((o.1,f),r) * localLift ((o.1,f),r) o| ≤
        ∑ f : Fin 4, ∑ r : Fin 3, |load q paths w ((o.1,f),r) * localLift ((o.1,f),r) o| := by
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum (fun f _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ f : Fin 4, ∑ r : Fin 3, B *
        (if f = (endpoints o.2).1 ∨ f = (endpoints o.2).2 then 0 else (1:K)/2) := by
          apply Finset.sum_le_sum
          intro f _
          apply Finset.sum_le_sum
          intro r _
          rw [abs_mul,lift_abs]
          exact mul_le_mul_of_nonneg_right (global_load _) (by split_ifs <;> positivity)
      _ = 3 * B := by
          rcases o with ⟨t,j⟩
          fin_cases j <;> norm_num [endpoints,Fin.sum_univ_succ] <;>
            norm_num <;> ring
  exact ⟨paths,follows,simple,nilpath,counts,anti,chi_bound,support,divergence,
    load_anti,load_bound,zeroM,deficit,local_bound⟩

end D5.S3.Geometry.Hyperideal.ActualCornerTransport
