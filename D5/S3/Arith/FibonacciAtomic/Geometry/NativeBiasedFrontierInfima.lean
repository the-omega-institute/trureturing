/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Biased native frontier distances and exact shift-copy product minima. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation
import D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeBiasedFrontierInfima

open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)

/-- Directional cylinder weight, with `false` as the left edge. -/
def weight (θ : ℝ) : Address → ℝ
  | [] => 1
  | false :: p => θ * weight θ p
  | true :: p => (1 - θ) * weight θ p

/-- Biased mass of the existing first-disagreement frontier. -/
def distance (θ : ℝ) (s t : Source) : ℝ :=
  ∑ p ∈ D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier s t, weight θ p

private theorem distance_self (θ : ℝ) (s : Source) : distance θ s s = 0 := by
  cases s <;> simp [distance, D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier]

private theorem distance_of_of (θ : ℝ) (b c : Bool) (h : b ≠ c) :
    distance θ (.of b) (.of c) = 1 := by
  have hn : (FreeMagma.of b : Source) ≠ .of c := by
    intro he
    injection he with he
    exact h he
  simp only [distance, D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier, if_neg hn, Finset.sum_singleton, weight, List.length_nil,
    pow_zero]

private theorem distance_of_mul (θ : ℝ) (b : Bool) (u v : Source) :
    distance θ (.of b) (.mul u v) = 1 := by
  simp [distance, D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier, weight]

private theorem distance_mul_of (θ : ℝ) (u v : Source) (b : Bool) :
    distance θ (.mul u v) (.of b) = 1 := by
  simp [distance, D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier, weight]

private theorem distance_mul_mul (θ : ℝ) (s u t v : Source) :
    distance θ (.mul s u) (.mul t v) =
      θ * distance θ s t + (1 - θ) * distance θ u v := by
  by_cases he : (.mul s u : Source) = .mul t v
  · injection he with hs hu
    subst t
    subst v
    rw [distance_self, distance_self, distance_self]
    ring
  · have hd : Disjoint ((D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier s t).image (List.cons false))
        ((D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier u v).image (List.cons true)) := by
        simp only [Finset.disjoint_left, Finset.mem_image]
        rintro _ ⟨a, _, rfl⟩ ⟨b, _, hb⟩
        cases hb
    simp only [distance, D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier, if_neg he]
    rw [Finset.sum_union hd,
      Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
      Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
    simp only [weight]
    rw [← Finset.mul_sum, ← Finset.mul_sum]

private theorem distance_nonneg (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (s t : Source) : 0 ≤ distance θ s t := by
  classical
  have hw : ∀ p : Address, 0 ≤ weight θ p := by
    intro p
    induction p with
    | nil => simp [weight]
    | cons b p ih =>
        cases b
        · simpa [weight] using mul_nonneg hθ ih
        · simpa [weight] using mul_nonneg (sub_nonneg.mpr hθ1) ih
  unfold distance
  exact Finset.sum_nonneg (fun p hp => hw p)

private theorem distance_le_one (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (s t : Source) : distance θ s t ≤ 1 := by
  induction s generalizing t with
  | of b =>
    cases t with
    | of c =>
      by_cases h : b = c
      · subst c
        rw [distance_self]
        norm_num
      · rw [distance_of_of θ b c h]
    | mul u v => rw [distance_of_mul]
  | mul s u hs hu =>
    cases t with
    | of c => rw [distance_mul_of]
    | mul t v =>
      rw [distance_mul_mul]
      calc
        θ * distance θ s t + (1 - θ) * distance θ u v ≤
            θ * 1 + (1 - θ) * 1 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hs t) hθ)
            (mul_le_mul_of_nonneg_left (hu v) (sub_nonneg.mpr hθ1))
        _ = 1 := by ring

/-- The weighted first-disagreement mass satisfies the triangle inequality. -/
theorem biased_frontier_triangle (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (s z t : Source) : distance θ s t ≤ distance θ s z + distance θ z t := by
  induction s generalizing z t with
  | of b =>
    cases z with
    | of c =>
      cases t with
      | of d =>
          by_cases hbc : b = c <;> by_cases hcd : c = d <;>
            by_cases hbd : b = d <;>
            simp_all [distance_self, distance_of_of]
      | mul u v =>
          rw [distance_of_mul]
          rw [distance_of_mul]
          by_cases h : b = c
          · subst c
            rw [distance_self]
            norm_num
          · rw [distance_of_of θ b c h]
            norm_num
    | mul l r =>
      cases t with
      | of d =>
          rw [distance_of_mul, distance_mul_of]
          by_cases h : b = d
          · subst d
            rw [distance_self]
            norm_num
          · rw [distance_of_of θ b d h]
            norm_num
      | mul u v =>
          rw [distance_of_mul, distance_of_mul]
          exact le_add_of_nonneg_right (distance_nonneg θ hθ hθ1 _ _)
  | mul s u hs hu =>
    cases z with
    | of c =>
      cases t with
      | of d =>
          rw [distance_mul_of, distance_mul_of]
          by_cases h : c = d
          · subst d
            rw [distance_self]
            norm_num
          · rw [distance_of_of θ c d h]
            norm_num
      | mul t v =>
          have hle := distance_le_one θ hθ hθ1 (.mul s u) (.mul t v)
          rw [distance_mul_mul] at hle
          rw [distance_mul_mul, distance_mul_of, distance_of_mul]
          exact hle.trans (by norm_num)
    | mul z w =>
      cases t with
      | of d =>
          rw [distance_mul_of, distance_mul_mul, distance_mul_of]
          have hn : 0 ≤ θ * distance θ s z + (1 - θ) * distance θ u w :=
            add_nonneg
              (mul_nonneg hθ (distance_nonneg θ hθ hθ1 _ _))
              (mul_nonneg (sub_nonneg.mpr hθ1) (distance_nonneg θ hθ hθ1 _ _))
          linarith
      | mul t v =>
          rw [distance_mul_mul, distance_mul_mul, distance_mul_mul]
          calc
            θ * distance θ s t + (1 - θ) * distance θ u v ≤
                θ * (distance θ s z + distance θ z t) +
                  (1 - θ) * (distance θ u w + distance θ w v) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left (hs z t) hθ)
                (mul_le_mul_of_nonneg_left (hu w v) (sub_nonneg.mpr hθ1))
            _ = θ * distance θ s z + (1 - θ) * distance θ u w +
                  (θ * distance θ z t + (1 - θ) * distance θ w v) := by ring

/-- The same finite induction gives the probability bounds. -/
theorem biased_frontier_bounds (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (s t : Source) : 0 ≤ distance θ s t ∧ distance θ s t ≤ 1 := by
  exact ⟨distance_nonneg θ hθ hθ1 s t, distance_le_one θ hθ hθ1 s t⟩


open GenealogicalFiberTransport (substitution)
open ActualImageAlphaSeparation (frontier)
open ActualImageSevenLeafSeparation (leafAddresses)

private theorem iterate_pair (a : ℕ) (s t : Source) :
    substitution^[a] (.mul s t) = .mul (substitution^[a] s) (substitution^[a] t) :=
  Function.Semiconj₂.iterate
    (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
      substitution.map_mul) a s t

private theorem shift_ne (a : ℕ) (ha : 1 ≤ a) (t : Source) :
    t ≠ substitution^[a] t := by
  intro h
  have hk := Observer.NativePrefixIdentityReflection.kappa_iterate a t
  rw [← h] at hk
  omega

private theorem frontier_self (s : Source) : frontier s s = ∅ := by
  cases s <;> simp [ActualImageAlphaSeparation.frontier]

private theorem frontier_pair (s u t v : Source) :
    frontier (.mul s u) (.mul t v) =
      (frontier s t).image (List.cons false) ∪ (frontier u v).image (List.cons true) := by
  by_cases h : (.mul s u : Source) = .mul t v
  · injection h with hs hu
    subst t
    subst v
    simp [frontier_self]
  · simp only [ActualImageAlphaSeparation.frontier, if_neg h]

/-- Every positive shift first disagrees at precisely the original leaves. -/
theorem frontier_shift (a : ℕ) (ha : 1 ≤ a) (t : Source) :
    frontier t (substitution^[a] t) = leafAddresses t := by
  induction t with
  | of b =>
      simp [ActualImageAlphaSeparation.frontier, shift_ne a ha (.of b), leafAddresses,
        ActualTreeReadoutAcquisition.leaves]
  | mul s t hs ht =>
      rw [iterate_pair, frontier_pair, hs, ht]
      ext p
      simp [leafAddresses, ActualTreeReadoutAcquisition.leaves]

private theorem weighted_split (θ : ℝ) (A B : Finset Address) :
    (∑ p ∈ A.image (List.cons false) ∪ B.image (List.cons true), weight θ p) =
      θ * (∑ p ∈ A, weight θ p) + (1 - θ) * (∑ p ∈ B, weight θ p) := by
  have hd : Disjoint (A.image (List.cons false)) (B.image (List.cons true)) := by
    simp only [Finset.disjoint_left, Finset.mem_image]
    rintro _ ⟨a, _, rfl⟩ ⟨b, _, hb⟩
    cases hb
  rw [Finset.sum_union hd,
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
  simp only [weight]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- The leaves of every finite full binary source have total cylinder weight one. -/
theorem leaf_partition (θ : ℝ) (t : Source) :
    (∑ p ∈ leafAddresses t, weight θ p) = 1 := by
  induction t with
  | of b => simp [leafAddresses, ActualTreeReadoutAcquisition.leaves, weight]
  | mul s t hs ht =>
      have h : leafAddresses (.mul s t) =
          (leafAddresses s).image (List.cons false) ∪
            (leafAddresses t).image (List.cons true) := by
        ext p
        simp [leafAddresses, ActualTreeReadoutAcquisition.leaves]
      rw [h, weighted_split, hs, ht]
      ring

/-- A source and any positive native shift have unit biased distance. -/
theorem distance_shift (θ : ℝ) (a : ℕ) (ha : 1 ≤ a) (t : Source) :
    distance θ t (substitution^[a] t) = 1 := by
  unfold distance
  rw [frontier_shift a ha, leaf_partition]

private theorem distance_symm (θ : ℝ) (s t : Source) :
    distance θ s t = distance θ t s := by
  induction s generalizing t with
  | of b =>
      cases t with
      | of c =>
          by_cases h : b = c
          · subst c; rfl
          · rw [distance_of_of θ b c h, distance_of_of θ c b (Ne.symm h)]
      | mul u v => rw [distance_of_mul, distance_mul_of]
  | mul s u hs hu =>
      cases t with
      | of c => rw [distance_mul_of, distance_of_mul]
      | mul t v => rw [distance_mul_mul, distance_mul_mul, hs t, hu v]


/-- First disagreements of three original reply traces, stopping at their common leaves. -/
def tripleFrontier : Source → Source → Source → Finset Address
  | .mul s u, .mul t v, .mul z w =>
      (tripleFrontier s t z).image (List.cons false) ∪
        (tripleFrontier u v w).image (List.cons true)
  | .of b, .of c, .of d => if b = c ∧ c = d then ∅ else {[]}
  | _, _, _ => {[]}

/-- Normalized three-source frontier mass with per-original-address weights. -/
def tripleMass (θ : ℝ) (s t u : Source) : ℝ :=
  ∑ p ∈ tripleFrontier s t u, weight θ p

private theorem triple_leaf (b : Bool) (y z : Source) (h : (.of b : Source) ≠ y) :
    tripleFrontier (.of b) y z = {[]} := by
  cases y with
  | of c =>
      have bc : b ≠ c := by intro eq; apply h; rw [eq]
      cases z <;> simp [tripleFrontier,bc]
  | mul l r => rfl

/-- The first two positive-shift coordinates already disagree at every original leaf. -/
theorem triple_frontier_shift (a : ℕ) (ha : 1 ≤ a) (t : Source) :
    tripleFrontier t (substitution^[a] t) (substitution^[a] (substitution^[a] t)) =
      leafAddresses t := by
  induction t with
  | of b =>
      rw [triple_leaf b _ _ (shift_ne a ha _)]
      simp [leafAddresses,ActualTreeReadoutAcquisition.leaves]
  | mul s t hs ht =>
      simp only [iterate_pair,tripleFrontier,hs,ht]
      ext p
      simp [leafAddresses,ActualTreeReadoutAcquisition.leaves]

private theorem triple_mass_shift (θ : ℝ) (a : ℕ) (ha : 1 ≤ a) (t : Source) :
    tripleMass θ t (substitution^[a] t) (substitution^[a] (substitution^[a] t)) = 1 := by
  unfold tripleMass
  rw [triple_frontier_shift a ha,leaf_partition]


open Observer.NativeFiveHoleFiber (GuardedEqual Negative rootLabel)
open ActualTreeReadoutAcquisition (readout)
open ActualLeafHistoryRigidity (subtree)
open Observer.ActualCutPartitionRecovery
  (CutSet CutPrefixFree orderedHoles reachedHoles canonicalRow)
open Observer.ActualCutPartitionDecoder
  (HoleExterior cutExterior actualPartition literalRecord)

/-- The same whole finite value fills both the unshifted and shifted right holes. -/
def U (a : ℕ) (x y : Source) : Source := .mul x (.mul y (substitution^[a] y))

/-- The complete old row, four literal observations, and three guarded relations. -/
def Retained (a : ℕ) (u : Source) : Prop :=
  literalRecord {[]} u = rootLabel ∧
  readout [] u = .branch ∧ readout [true] u = .branch ∧
  readout [] (substitution^[a] u) = .branch ∧
  readout [true] (substitution^[a] u) = .branch ∧
  GuardedEqual a [true,false] 0 [true,true] u ∧
  Negative (0,[true,false],0,[true,true]) u ∧
  Negative (0,[],0,[false]) u

private theorem u_ne_left (a : ℕ) (x y : Source) : U a x y ≠ x := by
  intro h
  have he := congrArg FreeMagma.length h
  have hy := y.length_pos
  have hz := (substitution^[a] y).length_pos
  change x.length + (y.length + (substitution^[a] y).length) = x.length at he
  omega

/-- The retained input has exactly the entire two-parameter source fiber. -/
theorem retained_iff (a : ℕ) (ha : 1 ≤ a) (u : Source) :
    Retained a u ↔ ∃ x y : Source, u = U a x y := by
  constructor
  · rintro ⟨_,root,right,_,_,copy,_,_⟩
    cases u with
    | of b => cases b <;> simp [readout] at root
    | mul x v =>
      cases v with
      | of b => cases b <;> simp [readout] at right
      | mul y z =>
        have copy' : GuardedEqual 0 [true,true] a [true,false] (.mul x (.mul y z)) :=
          ⟨copy.2.1,copy.1,copy.2.2.symm⟩
        have installed := (Observer.NativePayloadHistoryInstallation.payload_history_exact
          (Observer.NativePrefixIdentityReflection.MixedExpr.residual a ())
          (fun _ : Unit => [true,false]) [true,true] (.mul x (.mul y z))
          (fun _ : Unit => y) (by intro i hi; rfl)).mp
          (by simpa [Observer.NativePayloadHistoryInstallation.Holds,
            Observer.NativePayloadHistoryInstallation.compile,
            Observer.NativePayloadHistoryInstallation.Record.Holds] using copy')
        have hz : z = substitution^[a] y := by
          simpa [subtree, Observer.NativePrefixIdentityReflection.eval] using installed
        exact ⟨x,y,by rw [hz]; rfl⟩
  · rintro ⟨x,y,rfl⟩
    refine ⟨Observer.NativeFiveHoleFiber.root_record _, ?_⟩
    have transport := Observer.NativeDepthPatterns.original_present_transport a
      [true,false] (U a x y) y (by rfl)
    have neq := shift_ne a ha y
    have off := u_ne_left a x y
    simp only [U, iterate_pair] at transport ⊢
    simp [readout, GuardedEqual, Negative, subtree, neq]
    exact off

/-- The target cut is ordered left, right-left, right-right. -/
def position : Fin 3 → Address := ![[false], [true,false], [true,true]]
def Q : CutSet := {position 0, position 1, position 2}

def exterior : HoleExterior := .mul (.of (.inr (position 0)))
  (.mul (.of (.inr (position 1))) (.of (.inr (position 2))))

def labelClass (i : Fin 3) (p : Address) : ℕ :=
  if i = 0 then (if p = position 2 then 1 else 0)
  else if i = 1 then (if p = position 1 then 1 else 0)
  else if p = position 0 then 0 else if p = position 1 then 1 else 2

/-- Every label retains the entire exterior and the entire hole partition. -/
def label (i : Fin 3) : HoleExterior × Finset (Address × Address) :=
  (exterior, (Q.product Q).filter (fun pq => labelClass i pq.1 = labelClass i pq.2))

def rowCondition (a : ℕ) (i : Fin 3) (x y : Source) : Prop :=
  if i = 0 then x = y else if i = 1 then x = substitution^[a] y
  else x ≠ y ∧ x ≠ substitution^[a] y

/-- A stratum includes the entire retained input, with its complete target record. -/
def Stratum (a : ℕ) (i : Fin 3) (u : Source) : Prop :=
  Retained a u ∧ ∃ v : Source, canonicalRow Q u = canonicalRow Q v ∧
    literalRecord Q v = label i

private def hole (a : ℕ) (x y : Source) : Fin 3 → Source :=
  ![x, y, substitution^[a] y]

@[simp] private theorem exterior_stop (p : Address) (t : Source) (hp : p ∈ Q) :
    cutExterior Q p t = .of (.inr p) := by
  cases t <;> simp [cutExterior,hp]

private theorem u_exterior (a : ℕ) (x y : Source) :
    cutExterior Q [] (U a x y) = exterior := by
  simp only [U, cutExterior, List.nil_append, List.cons_append,
    show ([] : Address) ∉ Q by decide, show ([true] : Address) ∉ Q by decide, if_false]
  rw [exterior_stop _ _ (by decide), exterior_stop _ _ (by decide),
    exterior_stop _ _ (by decide)]
  rfl

private theorem u_holes (a : ℕ) (x y : Source) :
    (orderedHoles Q (U a x y)).toFinset = Q := by
  have holes := Observer.ActualCutPartitionDecoder.exteriorHoles_cut Q [] (U a x y)
  rw [u_exterior] at holes
  have reached : reachedHoles Q [] (U a x y) =
      [position 0,position 1,position 2] := by
    simpa [exterior,Observer.ActualCutPartitionDecoder.exteriorHoles,position] using holes.symm
  unfold orderedHoles
  rw [reached]
  simp [Q]

private theorem hole_at (a : ℕ) (x y : Source) (i : Fin 3) :
    subtree (position i) (U a x y) = some (hole a x y i) := by
  fin_cases i <;> rfl

private theorem position_exists (p : Address) (hp : p ∈ Q) :
    ∃ i : Fin 3, p = position i := by
  simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩

private theorem cut_prefix_free : CutPrefixFree Q := by
  intro p hp q hq hpre
  obtain ⟨i,rfl⟩ := position_exists p hp
  obtain ⟨j,rfl⟩ := position_exists q hq
  fin_cases i <;> fin_cases j <;> simp_all [position]

/-- The three full row labels are exactly the three displayed parameter conditions. -/
theorem label_iff (a : ℕ) (ha : 1 ≤ a) (i : Fin 3) (x y : Source) :
    literalRecord Q (U a x y) = label i ↔ rowCondition a i x y := by
  have mem (j : Fin 3) : position j ∈ Q := by fin_cases j <;> simp [Q]
  have pair (j k : Fin 3) :
      (position j,position k) ∈ actualPartition Q (U a x y) ↔
        hole a x y j = hole a x y k := by
    simp [actualPartition, u_holes, hole_at, mem]
  have lpair (j k : Fin 3) :
      (position j,position k) ∈ (label i).2 ↔
        labelClass i (position j) = labelClass i (position k) := by
    simp [label,mem]
  constructor
  · intro h
    have pairs (j k : Fin 3) : hole a x y j = hole a x y k ↔
        labelClass i (position j) = labelClass i (position k) := by
      rw [← pair, ← lpair]
      exact Finset.ext_iff.mp (congrArg Prod.snd h) _
    fin_cases i
    · simpa [rowCondition,hole,labelClass,position] using (pairs 0 1).mpr (by decide)
    · simpa [rowCondition,hole,labelClass,position] using (pairs 0 2).mpr (by decide)
    · have h1 := pairs 0 1
      have h2 := pairs 0 2
      simp [hole,labelClass,position] at h1 h2
      simpa [rowCondition] using And.intro h1 h2
  · intro h
    have tests (j k : Fin 3) : hole a x y j = hole a x y k ↔
        labelClass i (position j) = labelClass i (position k) := by
      have ne := shift_ne a ha y
      fin_cases i
      · simp only [rowCondition, if_pos rfl] at h
        subst x
        fin_cases j <;> fin_cases k <;> simp [hole,labelClass,position,ne,Ne.symm ne]
      · have hx : x = substitution^[a] y := by simpa [rowCondition] using h
        subst x
        fin_cases j <;> fin_cases k <;> simp [hole,labelClass,position,ne,Ne.symm ne]
      · have hx : x ≠ y ∧ x ≠ substitution^[a] y := by simpa [rowCondition] using h
        fin_cases j <;> fin_cases k <;>
          simp [hole,labelClass,position,ne,Ne.symm ne,hx.1,hx.2,Ne.symm hx.1,Ne.symm hx.2]
    apply Prod.ext (u_exterior a x y)
    change actualPartition Q _ = (label i).2
    ext ⟨p,q⟩
    simp only [actualPartition,u_holes,label,Finset.mem_filter,
      Finset.product_eq_sprod,Finset.mem_product]
    by_cases hp : p ∈ Q
    · by_cases hq : q ∈ Q
      · simp only [hp,hq,true_and]
        obtain ⟨j,rfl⟩ := position_exists p hp
        obtain ⟨k,rfl⟩ := position_exists q hq
        rw [hole_at,hole_at,Option.some.injEq]
        exact tests j k
      · simp [hq]
    · simp [hp]

/-- This parametrization ranges over every original in each complete row stratum. -/
theorem stratum_iff (a : ℕ) (ha : 1 ≤ a) (i : Fin 3) (u : Source) :
    Stratum a i u ↔ ∃ x y : Source, u = U a x y ∧ rowCondition a i x y := by
  constructor
  · rintro ⟨hr,v,hrow,hl⟩
    have full : literalRecord Q u = label i :=
      ((Observer.ActualCutPartitionDecoder.canonicalRow_record_iff Q cut_prefix_free u v).mp
        hrow).trans hl
    obtain ⟨x,y,rfl⟩ := (retained_iff a ha u).mp hr
    exact ⟨x,y,rfl,(label_iff a ha i x y).mp full⟩
  · rintro ⟨x,y,rfl,h⟩
    exact ⟨(retained_iff a ha _).mpr ⟨x,y,rfl⟩,
      U a x y,rfl,(label_iff a ha i x y).mpr h⟩


/-- Exact decomposition on arbitrary independently chosen alternatives. -/
theorem pair_decomposition (θ : ℝ) (a : ℕ) (s t : Source) :
    distance θ (U a s s) (U a (substitution^[a] t) t) =
      θ * distance θ s (substitution^[a] t) +
      θ * (1 - θ) * distance θ s t +
      (1 - θ)^2 * distance θ (substitution^[a] s) (substitution^[a] t) := by
  simp only [U,distance_mul_mul]
  ring

private theorem pair_lower (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (a : ℕ) (ha : 1 ≤ a) (s t : Source) :
    min θ (1 - θ) ≤ distance θ (U a s s) (U a (substitution^[a] t) t) := by
  let A := distance θ s (substitution^[a] t)
  let B := distance θ s t
  let C := distance θ (substitution^[a] s) (substitution^[a] t)
  have hab := biased_frontier_triangle θ hθ.le hθ1.le t s (substitution^[a] t)
  rw [distance_shift θ a ha t, distance_symm θ t s] at hab
  have hac := biased_frontier_triangle θ hθ.le hθ1.le s
    (substitution^[a] t) (substitution^[a] s)
  rw [distance_shift θ a ha s,
    distance_symm θ (substitution^[a] t) (substitution^[a] s)] at hac
  have hA := biased_frontier_bounds θ hθ.le hθ1.le s (substitution^[a] t)
  have hB : 1 - A ≤ B := by dsimp [A,B]; linarith
  have hC : 1 - A ≤ C := by dsimp [A,C]; linarith
  have hb := mul_le_mul_of_nonneg_left hB
    (mul_nonneg hθ.le (sub_nonneg.mpr hθ1.le))
  have hc := mul_le_mul_of_nonneg_left hC (sq_nonneg (1 - θ))
  have hm1 := mul_le_mul_of_nonneg_right (min_le_left θ (1 - θ)) hA.1
  have hm2 := mul_le_mul_of_nonneg_right (min_le_right θ (1 - θ))
    (sub_nonneg.mpr hA.2)
  rw [pair_decomposition]
  change min θ (1 - θ) ≤ θ * A + θ * (1 - θ) * B + (1 - θ)^2 * C
  change 0 ≤ A ∧ A ≤ 1 at hA
  change min θ (1 - θ) * A ≤ θ * A at hm1
  change min θ (1 - θ) * (1 - A) ≤ (1 - θ) * (1 - A) at hm2
  nlinarith

private theorem in_zero (a : ℕ) (ha : 1 ≤ a) (t : Source) :
    Stratum a 0 (U a t t) := by
  apply (stratum_iff a ha 0 _).mpr
  exact ⟨t,t,rfl,by simp [rowCondition]⟩

private theorem in_one (a : ℕ) (ha : 1 ≤ a) (t : Source) :
    Stratum a 1 (U a (substitution^[a] t) t) := by
  apply (stratum_iff a ha 1 _).mpr
  exact ⟨_,t,rfl,by simp [rowCondition]⟩

/-- The values range over the entire Cartesian product of the first two strata. -/
def pairValues (θ : ℝ) (a : ℕ) : Set ℝ :=
  {m | ∃ u v : Source, Stratum a 0 u ∧ Stratum a 1 v ∧ distance θ u v = m}

/-- Both endpoint values are attained by actual originals in their full strata. -/
private theorem pair_attained (θ : ℝ) (a : ℕ) (ha : 1 ≤ a) (t : Source) :
    θ ∈ pairValues θ a ∧ (1 - θ) ∈ pairValues θ a := by
  constructor
  · refine ⟨U a t t,U a (substitution^[a] t) t,in_zero a ha t,in_one a ha t,?_⟩
    rw [pair_decomposition, distance_shift θ a ha, distance_self, distance_self]
    ring
  · refine ⟨U a (substitution^[a] t) (substitution^[a] t),
      U a (substitution^[a] t) t,in_zero a ha _,in_one a ha t,?_⟩
    rw [pair_decomposition,distance_self,distance_symm θ (substitution^[a] t) t,
      distance_shift θ a ha,distance_symm θ (substitution^[a] (substitution^[a] t))
        (substitution^[a] t),distance_shift θ a ha]
    ring

/-- The exact binary-product infimum is attained, uniformly in the supplied shift. -/
theorem binary_product_minimum (a : ℕ) (ha : 1 ≤ a) (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    IsLeast (pairValues θ a) (min θ (1 - θ)) := by
  refine ⟨?_,?_⟩
  · have attained := pair_attained θ a ha (.of true)
    by_cases h : θ ≤ 1 - θ
    · simpa [min_eq_left h] using attained.1
    · simpa [min_eq_right (le_of_not_ge h)] using attained.2
  · rintro m ⟨u,v,hu,hv,hm⟩
    obtain ⟨x,s,rfl,hs⟩ := (stratum_iff a ha 0 u).mp hu
    obtain ⟨y,t,rfl,ht⟩ := (stratum_iff a ha 1 v).mp hv
    have xs : x = s := by simpa [rowCondition] using hs
    have yt : y = substitution^[a] t := by simpa [rowCondition] using ht
    subst x
    subst y
    rw [← hm]
    exact pair_lower θ hθ hθ1 a ha s t

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeBiasedFrontierInfima
