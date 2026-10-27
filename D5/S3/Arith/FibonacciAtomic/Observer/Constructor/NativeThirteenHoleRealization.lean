/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Correlated finite signed thirteen-hole sources approach one guarded completion. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalEffectivePrefix
import D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber

/-! Explicit finite tuples satisfy both signed thirteen-hole rows and approach one completion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeThirteenHoleRealization

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open NativeCompletionPrefixLifting
open CompletionHomogeneousFixedPoints (Omega rho omega_node iterate_full iterate_omega)
open NativePrefixIdentityReflection (comb gamma gamma_iterate gamma_pair gamma_comb kappa kappa_iterate)
open NativeSymbolicFiniteForcing (FunctionalSystem canonicalSolution symbolic_finite_forcing)
open FiniteHereditaryPatternRealization (B_T hole locate hole_locate locate_eq)

/-- The exact one-coordinate equation, with an infinite token denoting Omega. -/
def system : FunctionalSystem 1 1 := fun _ =>
  some (.pair (.token 0 0) (.pair (.var 1 0) (.ground (.of true))))

noncomputable def K : CompletionTree := canonicalSolution system (fun _ => false) (fun _ => 0) 0

private theorem k_law : K = node Omega (node (rho K) (leaf true)) := by
  have law := (symbolic_finite_forcing system (fun _ => false)
    (fun _ : Fin 0 => .ground (.of true))).1 (fun _ => 0) 0 _ rfl
  exact law

/-- Both pair levels belong to the original finite value. -/
def G (x t : Source) : Source := .mul x (.mul (substitution t) (.of true))

def tail (x : Source) (n m : Nat) : Source := (G x)^[n] (comb m)

private theorem cutoff_mono (d e : Nat) (S T : CompletionTree) (le : d ≤ e)
    (eq : cutoff e S = cutoff e T) : cutoff d S = cutoff d T :=
  (cutoff_readout d S T).mpr (fun a ha => (cutoff_readout e S T).mp eq a (ha.trans_le le))

private theorem rho_prefix (d : Nat) (S T : CompletionTree)
    (eq : cutoff d S = cutoff d T) : cutoff d (rho S) = cutoff d (rho T) := by
  simpa only [Function.iterate_one] using
    (NativeFunctionalEffectivePrefix.iterate_cutoff d 1 S).symm.trans
      ((congrArg _ eq).trans (NativeFunctionalEffectivePrefix.iterate_cutoff d 1 T))

/-- Two guarded pair levels consume two prefix levels per recursive call. -/
private theorem guarded_prefix (d n m : Nat) (x : Source)
    (hx : cutoff d (embed x) = cutoff d Omega) (hn : d ≤ 2*n) :
    cutoff d (embed (tail x n m)) = cutoff d K := by
  induction d using Nat.twoStepInduction generalizing n with
  | zero => rfl
  | one =>
    cases n with
    | zero => omega
    | succ n =>
      rw [tail, Function.iterate_succ_apply', G, embed, k_law]
      rfl
  | more d ih _ =>
    cases n with
    | zero => omega
    | succ n =>
      have hx' := cutoff_mono d (d+2) (embed x) Omega (by omega) hx
      have smaller := ih n hx' (by omega)
      rw [tail, Function.iterate_succ_apply', G, embed, k_law]
      change Sum.inr (cutoff (d+1) (embed x),
        Sum.inr (cutoff d (embed (substitution (tail x n m))), cutoff d (leaf true))) =
        Sum.inr (cutoff (d+1) Omega,
        Sum.inr (cutoff d (rho K), cutoff d (leaf true)))
      rw [cutoff_mono (d+1) (d+2) (embed x) Omega (by omega) hx,
        ← CompletionHomogeneousFixedPoints.rho_embed, rho_prefix d _ _ smaller]

/-- One tuple is shared by both source fillings. -/
def x (h : Nat) : Source := substitution^[2*(h+1)] (comb 1)
def y (h : Nat) : Source := substitution^[2*(h+1)+3] (comb 1)
def z (h : Nat) : Source := substitution^[2*(h+1)+6] (comb 1)
def w (h : Nat) : Source := substitution^[2*(h+1)+9] (comb 1)
def v (h : Nat) : Source := tail (x h) (h+1) 4

/-- The ten entire values compared by all forty-five retained negatives. -/
def base (h : Nat) : Fin 10 → Source :=
  ![x h, y h, z h, w h, substitution (x h), substitution (y h),
    .mul (y h) (z h), .mul (x h) (w h), v h, G (x h) (v h)]

private theorem mass_x (h : Nat) : gamma (x h) = 1 := by
  rw [x, gamma_iterate, gamma_comb]

private theorem mass_tail (h n m : Nat) (hm : 0 < m) :
    gamma (tail (x h) n m) = m+3*n := by
  induction n with
  | zero => exact gamma_comb m
  | succ n ih =>
    rw [tail, Function.iterate_succ_apply', G]
    rw [gamma_pair _ _ (Or.inl (by rw [mass_x]; omega))]
    rw [gamma_pair _ _ (Or.inl (by rw [gamma_iterate]; exact lt_of_lt_of_le hm (by omega)))]
    simp only [gamma_iterate, show gamma (.of true : Source) = 0 from rfl]
    change 1+gamma (x h)+(1+gamma (tail (x h) n m)+0) = _
    rw [mass_x, ih]; omega

private theorem base_distinct (h : Nat) : Function.Injective (base h) := by
  have gx : gamma (x h) = 1 := mass_x h
  have gy : gamma (y h) = 1 := by rw [y, gamma_iterate, gamma_comb]
  have gz : gamma (z h) = 1 := by rw [z, gamma_iterate, gamma_comb]
  have gw : gamma (w h) = 1 := by rw [w, gamma_iterate, gamma_comb]
  have gA : gamma (.mul (y h) (z h)) = 3 := by
    rw [gamma_pair _ _ (Or.inl (by omega)), gy, gz]
  have gB : gamma (.mul (x h) (w h)) = 3 := by
    rw [gamma_pair _ _ (Or.inl (by omega)), gx, gw]
  have gv : gamma (v h) = 4+3*(h+1) := mass_tail h (h+1) 4 (by omega)
  have gH : gamma (G (x h) (v h)) = 4+3*(h+2) := by
    simpa only [v, tail, Function.iterate_succ_apply'] using mass_tail h (h+2) 4 (by omega)
  have cx : kappa (x h) = 2+2*(h+1) := by rw [x,kappa_iterate]; rfl
  have cy : kappa (y h) = 2+(2*(h+1)+3) := by rw [y,kappa_iterate]; rfl
  have cz : kappa (z h) = 2+(2*(h+1)+6) := by rw [z,kappa_iterate]; rfl
  have cw : kappa (w h) = 2+(2*(h+1)+9) := by rw [w,kappa_iterate]; rfl
  have kA : kappa (.mul (y h) (z h)) = 2+kappa (z h) := rfl
  have kB : kappa (.mul (x h) (w h)) = 2+kappa (w h) := rfl
  intro i j eq
  have gm := congrArg gamma eq
  have ck := congrArg kappa eq
  fin_cases i <;> fin_cases j
  all_goals simp only [base,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one] at gm ck ⊢
  all_goals try rfl
  all_goals simp only [show substitution = substitution^[1] from rfl,
    gamma_iterate,kappa_iterate,gx,gy,gz,gw,gA,gB,gv,gH,cx,cy,cz,cw,kA,kB] at gm ck
  all_goals omega

/-- Zero-based equality classes for the complete thirteen-hole rows. -/
def classes (side : Bool) : Fin 13 → Fin 10 :=
  if side then ![0,1,2,3,6,7,4,5,6,7,8,9,9]
  else ![0,1,2,3,4,5,4,5,6,7,8,8,9]

def values (side : Bool) (h : Nat) : Fin 13 → Source := base h ∘ classes side

def theta (side : Bool) (h : Nat) : Source := B_T 12 (values side h)

def position : Fin 13 → Address := hole 12

def Q : ActualCutPartitionRecovery.CutSet := Finset.univ.image position

private theorem position_injective : Function.Injective position := by
  intro i j eq
  exact (FiniteHereditaryPatternRealization.result.2.2.2.1 12 i j [] [] (by simpa using eq)).1

private theorem Q_mem (i : Fin 13) : position i ∈ Q := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

private theorem Q_prefix_free : ActualCutPartitionRecovery.CutPrefixFree Q := by
  rintro p hp q hq ⟨s,eq⟩
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
  have e : hole 12 i ++ s = hole 12 j ++ [] := by simpa [position] using eq
  exact congrArg position (FiniteHereditaryPatternRealization.result.2.2.2.1 12 i j s [] e).1

private theorem epoch_at (a : Nat) (side : Bool) (h : Nat) (i : Fin 13) :
    subtree (position i) (substitution^[a] (theta side h)) =
      some (substitution^[a] (values side h i)) :=
  NativeDepthPatterns.original_present_transport a (position i) _ _
    (NativeSharpPredecessorFiber.comb_at 12 (values side h) i)

/-- All sixteen old branch replies and the old alpha reply. -/
def literals : List NativePayloadHistoryInstallation.Record :=
  (List.range 12).map (fun j => .literal 0 (List.replicate j true) .branch) ++
  [.literal 0 (position 8) .branch, .literal 0 (position 9) .branch,
   .literal 0 (position 12) .branch, .literal 0 (position 12 ++ [true]) .branch,
   .literal 0 (position 12 ++ [true,true]) .alpha]

/-- The exact eight whole-subtree positive records, with their original epochs. -/
def positives : List NativePayloadHistoryInstallation.Record :=
  [.positive 0 (position 6) 1 (position 0),
   .positive 0 (position 7) 1 (position 1),
   .positive 0 (position 8 ++ [false]) 0 (position 1),
   .positive 0 (position 8 ++ [true]) 0 (position 2),
   .positive 0 (position 9 ++ [false]) 0 (position 0),
   .positive 0 (position 9 ++ [true]) 0 (position 3),
   .positive 0 (position 12 ++ [false]) 0 (position 0),
   .positive 0 (position 12 ++ [true,false]) 1 (position 10)]

/-- The ten original endpoints, in the source order. -/
def endpoints : Fin 10 → Fin 13 := ![0,1,2,3,6,7,8,9,10,12]

def negatives : List NativeFiveHoleFiber.NegativeRecord :=
  ((List.finRange 10).flatMap fun i => ((List.finRange 10).filter fun j => i < j).map
    fun j => (0,position (endpoints i),0,position (endpoints j)))

/-- The full acquired input, including the attained old root row and every sign. -/
def Acquired (u : Source) : Prop :=
  ActualCutPartitionDecoder.literalRecord {[]} u = NativeFiveHoleFiber.rootLabel ∧
  NativePayloadHistoryInstallation.Holds u literals ∧
  NativePayloadHistoryInstallation.Holds u positives ∧
  ∀ e ∈ negatives, NativeFiveHoleFiber.Negative e u

private theorem child_at (side : Bool) (h : Nat) (i : Fin 13) (p : Address) :
    subtree (position i ++ p) (theta side h) = subtree p (values side h i) := by
  rw [ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  rw [show subtree (position i) (theta side h) = some (values side h i) from epoch_at 0 side h i]
  rfl

private theorem all_literals (side : Bool) (h : Nat) :
    NativePayloadHistoryInstallation.Holds (theta side h) literals := by
  intro r hr
  simp only [literals,List.mem_append,List.mem_map,List.mem_cons,List.mem_singleton] at hr
  rcases hr with ⟨j,hj,rfl⟩ | rfl | rfl | rfl | rfl | rfl
  · have small : j < 12 := List.mem_range.mp hj
    interval_cases j <;> rfl
  all_goals change readout _ (theta side h) = _
  all_goals rw [FiniteHereditaryPatternRealization.result.1]
  all_goals simp only [position, hole_locate, show ∀ i, hole 12 i = hole 12 i ++ [] from fun _ => (List.append_nil _).symm]
  all_goals cases side <;> rfl

private theorem all_positives (side : Bool) (h : Nat) :
    NativePayloadHistoryInstallation.Holds (theta side h) positives := by
  have at (i : Fin 13) : subtree (position i) (theta side h) = some (values side h i) := epoch_at 0 side h i
  simp only [NativePayloadHistoryInstallation.Holds,positives,List.forall_mem_cons,List.forall_mem_singleton]
  simp only [NativePayloadHistoryInstallation.Record.Holds, NativeFiveHoleFiber.GuardedEqual]
  simp only [Function.iterate_zero_apply,at,child_at,epoch_at]
  cases side <;> simp [values,classes,base,G,Function.comp_apply,subtree]

private theorem endpoint_value (side : Bool) (h : Nat) (i : Fin 10) :
    values side h (endpoints i) = base h i := by
  fin_cases i <;> cases side <;> rfl

private theorem all_negatives (side : Bool) (h : Nat) :
    ∀ e ∈ negatives, NativeFiveHoleFiber.Negative e (theta side h) := by
  intro e he
  obtain ⟨i,_,j,hj,rfl⟩ := List.mem_flatMap.mp he |>.imp_right (fun h => List.mem_map.mp h)
  have ij : i < j := (List.mem_filter.mp hj).2
  simp only [NativeFiveHoleFiber.Negative,epoch_at,Function.iterate_zero_apply,
    endpoint_value,Option.isSome_some,true_and,ne_eq,Option.some.injEq]
  intro eq
  have bad := base_distinct h eq
  exact (ne_of_lt ij) bad

private theorem acquired_theta (side : Bool) (h : Nat) : Acquired (theta side h) :=
  ⟨NativeFiveHoleFiber.root_record _,all_literals side h,all_positives side h,all_negatives side h⟩

open ActualCutPartitionRecovery (CutSet orderedHoles reachedHoles canonicalRow)
open ActualCutPartitionDecoder (HoleExterior cutExterior actualPartition literalRecord canonicalRow_record_iff)

def exterior : HoleExterior := cutExterior Q [] (B_T 12 (fun _ => .of true))

def classAt (side : Bool) (p : Address) : Fin 10 := classes side ((locate 12 p).getD (0,[])).1

/-- The comb exterior and every equality bit among all thirteen reached holes. -/
def row (side : Bool) : HoleExterior × Finset (Address × Address) :=
  (exterior,(Q.product Q).filter fun pq => classAt side pq.1 = classAt side pq.2)

private theorem classAt_position (side : Bool) (i : Fin 13) :
    classAt side (position i) = classes side i := by
  unfold classAt position
  rw [← List.append_nil (hole 12 i),hole_locate]
  rfl

private theorem whole_exterior (X : Fin 13 → Source) :
    cutExterior Q [] (B_T 12 X) = exterior := by
  have stop (i : Fin 13) (t : Source) :
      cutExterior Q (position i) t = .of (.inr (position i)) := by
    cases t <;> simp [cutExterior,Q_mem]
  have n0 : (List.replicate 0 true : Address) ∉ Q := by decide +kernel
  have n1 : (List.replicate 1 true : Address) ∉ Q := by decide +kernel
  have n2 : (List.replicate 2 true : Address) ∉ Q := by decide +kernel
  have n3 : (List.replicate 3 true : Address) ∉ Q := by decide +kernel
  have n4 : (List.replicate 4 true : Address) ∉ Q := by decide +kernel
  have n5 : (List.replicate 5 true : Address) ∉ Q := by decide +kernel
  have n6 : (List.replicate 6 true : Address) ∉ Q := by decide +kernel
  have n7 : (List.replicate 7 true : Address) ∉ Q := by decide +kernel
  have n8 : (List.replicate 8 true : Address) ∉ Q := by decide +kernel
  have n9 : (List.replicate 9 true : Address) ∉ Q := by decide +kernel
  have n10 : (List.replicate 10 true : Address) ∉ Q := by decide +kernel
  have n11 : (List.replicate 11 true : Address) ∉ Q := by decide +kernel
  unfold exterior
  simp only [B_T,cutExterior,List.nil_append,List.cons_append,List.singleton_append]
  all_goals simp only [List.replicate_succ,List.replicate_zero] at n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11
  simp only [n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,if_false]
  rw [show ∀ t, cutExterior Q (hole 12 (0 : Fin 13)) t = .of (.inr (position 0)) from stop 0]
  rw [show ∀ t, cutExterior Q (hole 12 (1 : Fin 13)) t = .of (.inr (position 1)) from stop 1]
  rw [show ∀ t, cutExterior Q (hole 12 (2 : Fin 13)) t = .of (.inr (position 2)) from stop 2]
  rw [show ∀ t, cutExterior Q (hole 12 (3 : Fin 13)) t = .of (.inr (position 3)) from stop 3]
  rw [show ∀ t, cutExterior Q (hole 12 (4 : Fin 13)) t = .of (.inr (position 4)) from stop 4]
  rw [show ∀ t, cutExterior Q (hole 12 (5 : Fin 13)) t = .of (.inr (position 5)) from stop 5]
  rw [show ∀ t, cutExterior Q (hole 12 (6 : Fin 13)) t = .of (.inr (position 6)) from stop 6]
  rw [show ∀ t, cutExterior Q (hole 12 (7 : Fin 13)) t = .of (.inr (position 7)) from stop 7]
  rw [show ∀ t, cutExterior Q (hole 12 (8 : Fin 13)) t = .of (.inr (position 8)) from stop 8]
  rw [show ∀ t, cutExterior Q (hole 12 (9 : Fin 13)) t = .of (.inr (position 9)) from stop 9]
  rw [show ∀ t, cutExterior Q (hole 12 (10 : Fin 13)) t = .of (.inr (position 10)) from stop 10]
  rw [show ∀ t, cutExterior Q (hole 12 (11 : Fin 13)) t = .of (.inr (position 11)) from stop 11]
  rw [show ∀ t, cutExterior Q (hole 12 (12 : Fin 13)) t = .of (.inr (position 12)) from stop 12]
  rfl

private theorem whole_holes (X : Fin 13 → Source) :
    (orderedHoles Q (B_T 12 X)).toFinset = Q := by
  have stop (i : Fin 13) (t : Source) : reachedHoles Q (position i) t = [position i] := by
    cases t <;> simp [reachedHoles,Q_mem]
  have n0 : (List.replicate 0 true : Address) ∉ Q := by decide +kernel
  have n1 : (List.replicate 1 true : Address) ∉ Q := by decide +kernel
  have n2 : (List.replicate 2 true : Address) ∉ Q := by decide +kernel
  have n3 : (List.replicate 3 true : Address) ∉ Q := by decide +kernel
  have n4 : (List.replicate 4 true : Address) ∉ Q := by decide +kernel
  have n5 : (List.replicate 5 true : Address) ∉ Q := by decide +kernel
  have n6 : (List.replicate 6 true : Address) ∉ Q := by decide +kernel
  have n7 : (List.replicate 7 true : Address) ∉ Q := by decide +kernel
  have n8 : (List.replicate 8 true : Address) ∉ Q := by decide +kernel
  have n9 : (List.replicate 9 true : Address) ∉ Q := by decide +kernel
  have n10 : (List.replicate 10 true : Address) ∉ Q := by decide +kernel
  have n11 : (List.replicate 11 true : Address) ∉ Q := by decide +kernel
  unfold orderedHoles
  simp only [Finset.sort_toFinset,B_T,reachedHoles,List.nil_append,List.cons_append,List.singleton_append]
  all_goals simp only [List.replicate_succ,List.replicate_zero] at n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11
  simp only [n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,if_false]
  rw [show ∀ t, reachedHoles Q (hole 12 (0 : Fin 13)) t = [position 0] from stop 0]
  rw [show ∀ t, reachedHoles Q (hole 12 (1 : Fin 13)) t = [position 1] from stop 1]
  rw [show ∀ t, reachedHoles Q (hole 12 (2 : Fin 13)) t = [position 2] from stop 2]
  rw [show ∀ t, reachedHoles Q (hole 12 (3 : Fin 13)) t = [position 3] from stop 3]
  rw [show ∀ t, reachedHoles Q (hole 12 (4 : Fin 13)) t = [position 4] from stop 4]
  rw [show ∀ t, reachedHoles Q (hole 12 (5 : Fin 13)) t = [position 5] from stop 5]
  rw [show ∀ t, reachedHoles Q (hole 12 (6 : Fin 13)) t = [position 6] from stop 6]
  rw [show ∀ t, reachedHoles Q (hole 12 (7 : Fin 13)) t = [position 7] from stop 7]
  rw [show ∀ t, reachedHoles Q (hole 12 (8 : Fin 13)) t = [position 8] from stop 8]
  rw [show ∀ t, reachedHoles Q (hole 12 (9 : Fin 13)) t = [position 9] from stop 9]
  rw [show ∀ t, reachedHoles Q (hole 12 (10 : Fin 13)) t = [position 10] from stop 10]
  rw [show ∀ t, reachedHoles Q (hole 12 (11 : Fin 13)) t = [position 11] from stop 11]
  rw [show ∀ t, reachedHoles Q (hole 12 (12 : Fin 13)) t = [position 12] from stop 12]
  decide +kernel

private theorem complete_row (side : Bool) (h : Nat) :
    literalRecord Q (theta side h) = row side := by
  apply Prod.ext (whole_exterior _)
  change actualPartition Q (theta side h) = (row side).2
  ext ⟨p,q⟩
  simp only [actualPartition,theta,whole_holes,row,Finset.mem_filter,
    Finset.product_eq_sprod,Finset.mem_product]
  by_cases hp : p ∈ Q
  · by_cases hq : q ∈ Q
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
      simp only [Q_mem,true_and,← theta,show ∀ k, subtree (position k) (theta side h) =
        some (values side h k) from epoch_at 0 side h,Option.some.injEq,
        classAt_position,values,Function.comp_apply]
      exact ⟨base_distinct h,congrArg (base h)⟩
    · simp [hq]
  · simp [hp]

private theorem row_difference : row false ≠ row true := by
  intro eq
  have test := Finset.ext_iff.mp (congrArg Prod.snd eq) (position 10,position 11)
  simp only [row,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Q_mem,
    true_and,classAt_position] at test
  simp [classes] at test

private theorem pair_prefix (d : Nat) (A B X Y : CompletionTree)
    (hA : cutoff d A = cutoff d X) (hB : cutoff d B = cutoff d Y) :
    cutoff d (node A B) = cutoff d (node X Y) := by
  rw [← NativeFunctionalEffectivePrefix.pair_cutoff,
    ← NativeFunctionalEffectivePrefix.pair_cutoff,hA,hB]

private theorem x_prefix (h : Nat) : cutoff (h+1) (embed (x h)) = cutoff (h+1) Omega := by
  apply (cutoff_readout _ _ _).mpr
  intro p hp
  have lhs := iterate_full (h+1) (embed (comb 1)) p hp
  have rhs := iterate_full (h+1) Omega p hp
  rw [iterate_omega] at rhs
  rw [x,← CompletionHomogeneousFixedPoints.iterate_embed]
  exact lhs.trans rhs.symm

private theorem shifted_prefix (h a : Nat) :
    cutoff (h+1) (embed (substitution^[a] (x h))) = cutoff (h+1) Omega := by
  rw [← CompletionHomogeneousFixedPoints.iterate_embed,← iterate_omega a]
  rw [← NativeFunctionalEffectivePrefix.iterate_cutoff,
    ← NativeFunctionalEffectivePrefix.iterate_cutoff,x_prefix]

private theorem v_prefix (h : Nat) : cutoff (h+1) (embed (v h)) = cutoff (h+1) K :=
  guarded_prefix (h+1) (h+1) 4 (x h) (x_prefix h) (by omega)

private theorem H_prefix (h : Nat) : cutoff (h+1) (embed (G (x h) (v h))) = cutoff (h+1) K := by
  rw [k_law,G,embed,embed]
  exact pair_prefix _ _ _ _ _ (x_prefix h)
    (pair_prefix _ _ _ _ _ (by rw [← CompletionHomogeneousFixedPoints.rho_embed];
      exact rho_prefix _ _ _ (v_prefix h)) rfl)

/-- The same completed output for both source rows. -/
noncomputable def Lambda : CompletionTree :=
  node Omega (node Omega (node Omega (node Omega (node Omega
    (node Omega (node Omega (node Omega (node Omega (node Omega
      (node K (node K K)))))))))))

private theorem theta_prefix (side : Bool) (h : Nat) :
    cutoff (h+1) (embed (theta side h)) = cutoff (h+1) Lambda := by
  have py : cutoff (h+1) (embed (y h)) = cutoff (h+1) Omega := by
    simpa only [y,x,← Function.iterate_add_apply] using shifted_prefix h 3
  have pz : cutoff (h+1) (embed (z h)) = cutoff (h+1) Omega := by
    simpa only [z,x,← Function.iterate_add_apply] using shifted_prefix h 6
  have pw : cutoff (h+1) (embed (w h)) = cutoff (h+1) Omega := by
    simpa only [w,x,← Function.iterate_add_apply] using shifted_prefix h 9
  have prx : cutoff (h+1) (embed (substitution (x h))) = cutoff (h+1) Omega := shifted_prefix h 1
  have pry : cutoff (h+1) (embed (substitution (y h))) = cutoff (h+1) Omega := by
    simpa only [Function.iterate_one] using
      (rho_prefix (h+1) (embed (y h)) Omega py).trans
        (congrArg (cutoff (h+1)) CompletionHomogeneousFixedPoints.rho_omega)
  have pA : cutoff (h+1) (embed (.mul (y h) (z h))) = cutoff (h+1) Omega := by
    conv_rhs => rw [omega_node]
    exact pair_prefix _ _ _ _ _ py pz
  have pB : cutoff (h+1) (embed (.mul (x h) (w h))) = cutoff (h+1) Omega := by
    conv_rhs => rw [omega_node]
    exact pair_prefix _ _ _ _ _ (x_prefix h) pw
  have pv := v_prefix h
  have pH := H_prefix h
  unfold theta Lambda
  cases side <;> simp only [B_T,values,Function.comp_apply,classes,Bool.false_eq_true,
    Bool.true_eq_true,if_false,if_true,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one,base,embed]
  all_goals repeat' apply pair_prefix
  all_goals first | exact x_prefix h | exact py | exact pz | exact pw | exact prx |
    exact pry | exact pA | exact pB | exact pv | exact pH

/-- Both originals satisfy the entire input and their distinct complete rows,
and agree through the inclusive depth with the single Lambda. -/
def SignedJoint (h : Nat) (u₀ u₁ : Source) : Prop :=
  Acquired u₀ ∧ Acquired u₁ ∧
  literalRecord Q u₀ = row false ∧ literalRecord Q u₁ = row true ∧
  (∀ i : Fin 13, (subtree (position i) u₀).isSome ∧ (subtree (position i) u₁).isSome) ∧
  canonicalRow Q u₀ = canonicalRow Q (theta false 0) ∧
  canonicalRow Q u₁ = canonicalRow Q (theta true 0) ∧
  u₀ ≠ u₁ ∧
  ∀ p : Address, p.length ≤ h →
    readout p u₀ = completionReadout p Lambda ∧ readout p u₁ = completionReadout p Lambda

/-- A terminating finite shared tuple gives actual signed realizations at every depth. -/
theorem actual_joint_realization (h : Nat) : SignedJoint h (theta false h) (theta true h) := by
  refine ⟨acquired_theta false h,acquired_theta true h,complete_row false h,complete_row true h,
    ?_,?_,?_,?_,?_⟩
  · intro i
    simp only [show ∀ side i, subtree (position i) (theta side h) = some (values side h i)
      from fun side i => epoch_at 0 side h i,Option.isSome_some,and_self]
  · exact (canonicalRow_record_iff Q Q_prefix_free _ _).mpr
      ((complete_row false h).trans (complete_row false 0).symm)
  · exact (canonicalRow_record_iff Q Q_prefix_free _ _).mpr
      ((complete_row true h).trans (complete_row true 0).symm)
  · intro eq
    exact row_difference ((complete_row false h).symm.trans
      ((congrArg (literalRecord Q) eq).trans (complete_row true h)))
  · intro p hp
    have a := (cutoff_readout (h+1) _ _).mp (theta_prefix false h) p (by omega)
    have b := (cutoff_readout (h+1) _ _).mp (theta_prefix true h) p (by omega)
    simpa only [embed_readout] using And.intro a b

#print axioms actual_joint_realization

end D5.S3.Arith.FibonacciAtomic.Observer.NativeThirteenHoleRealization
