/- GID: D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every open gate ordering is proportional to a double-row transfer matrix. -/

/-
proof_shape: result: content
escape_witness: form (2), result; path-word sorting and the permutation train construct
  a signed inhomogeneity for every ordering and identify the actual auxiliary trace.
admission_basis: open-problem-resolution (#13232; Proved)
Direct frozen dependencies:
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft;
    statement_id: sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d.
  D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.Gate;
    statement_id: sha256:5973958239314b36ca0df6f8fa1c50c422abbe5b5ead7b7954640b6be885aba9.
  D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.Gate.U;
    statement_id: sha256:36060f767c39ec1a87e987d9fb5875ea7baccd93e17faaa08b762a68a399ba09.
  D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.Gate.K1;
    statement_id: sha256:7ff679a4b74411c14ec4669517d97a5ff50507d3c45a44329b77668f4ca15e7e.
  D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.Gate.KN;
    statement_id: sha256:8256533b26b3682eec1bf87ac5d69a3bc80af7aaaf4da7aa56e60c0ce875722a.
  D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.circuit;
    statement_id: sha256:b9fddddd3e27c8b0961df18bcfb68720b180faf6b8e571adf3c46b514ec2be06.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Dynamics.OpenIntegrableCircuitDepthRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace D5.S3.Quantum.Dynamics.OpenIntegrableCircuitIntegrability
open scoped BigOperators
open D5.S3.Quantum.Dynamics.OpenIntegrableCircuitDepthRefutation (Gate circuit)

private def inversionSet (N : ℕ) (w : List ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun k => w.idxOf k < w.idxOf (k - 1)

private def key (S : Finset ℕ) (k : ℕ) : ℤ := if k ∈ S then -(k : ℤ) else k



def oneOp {Sites Local : Type*} [DecidableEq Sites] [Fintype Local] (i : Sites) (B : Matrix Local Local ℂ) : Module.End ℂ ((Sites → Local) → ℂ) where
  toFun f x := ∑ p, B (x i) p * f (Function.update x i p)
  map_add' f g := by funext x; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by funext x; simp [Finset.mul_sum, mul_left_comm, mul_assoc]

def twoOp {Sites Local : Type*} [DecidableEq Sites] [Fintype Local] (i j : Sites) (R : Matrix (Local × Local) (Local × Local) ℂ) : Module.End ℂ ((Sites → Local) → ℂ) where
  toFun f x := ∑ p, R (x i, x j) p * f (Function.update (Function.update x i p.1) j p.2)
  map_add' f g := by funext x; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by funext x; simp [Finset.mul_sum, mul_left_comm, mul_assoc]


def checkedR {Local : Type*} [Fintype Local]  [DecidableEq Local] (R : Matrix (Local × Local) (Local × Local) ℂ) : Matrix (Local × Local) (Local × Local) ℂ := ((Equiv.prodComm _ _).toPEquiv.toMatrix) * R

private def starWord {Sites Local : Type*} [DecidableEq Sites] [Fintype Local] (R S : Sites → Matrix (Local × Local) (Local × Local) ℂ) (K : Matrix Local Local ℂ) :
    List Sites → Sites → Module.End ℂ ((Sites → Local) → ℂ)
  | [], p => oneOp p K
  | i :: l, p => twoOp p i (R i) * starWord R S K l p * twoOp i p (S i)

private def nearestWord {Sites Local : Type*} [Fintype Sites] [DecidableEq Sites]
    [Fintype Local]  [DecidableEq Local] (R S : Sites → Matrix (Local × Local) (Local × Local) ℂ) (K : Matrix Local Local ℂ) :
    List Sites → Sites → Module.End ℂ ((Sites → Local) → ℂ)
  | [], p => oneOp p K
  | i :: l, p => twoOp i p (checkedR (R i)) * nearestWord R S K l i *
      twoOp i p (checkedR (S i))

private def putAux {Sites Local : Type*} [DecidableEq Local] (a : Local) : ((Sites → Local) → ℂ) →ₗ[ℂ] ((Option Sites → Local) → ℂ) where
  toFun f y := if y none = a then f (y ∘ some) else 0
  map_add' f g := by funext y; split_ifs with h <;> simp [h]
  map_smul' c f := by funext y; split_ifs with h <;> simp [h]

private def takeAux {Sites Local : Type*} (a : Local) : ((Option Sites → Local) → ℂ) →ₗ[ℂ] ((Sites → Local) → ℂ) where
  toFun f x := f ((Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def traceSum {Sites Local : Type*} [Fintype Local] [DecidableEq Local] (F : Module.End ℂ ((Option Sites → Local) → ℂ)) : Module.End ℂ ((Sites → Local) → ℂ) :=
  ∑ a : Local, (takeAux a).comp (F.comp (putAux a))

def partialTrace {Sites Local : Type*} [Fintype Sites] [DecidableEq Sites]
    [Fintype Local] [DecidableEq Local] (F : Module.End ℂ ((Option Sites → Local) → ℂ)) : Module.End ℂ ((Sites → Local) → ℂ) :=
  (LinearMap.toMatrixAlgEquiv' (R := ℂ)).symm
    (D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft
      (Matrix.reindex (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local))
        (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local))
        (LinearMap.toMatrixAlgEquiv' (R := ℂ) F)))

private def liftPhysical {Sites Local : Type*} (B : Module.End ℂ ((Sites → Local) → ℂ)) : Module.End ℂ ((Option Sites → Local) → ℂ) where
  toFun f y := B (fun x => f ((Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (y none, x))) (y ∘ some)
  map_add' f g := by funext y; exact congrFun (B.map_add _ _) _
  map_smul' c f := by funext y; exact congrFun (B.map_smul c _) _

private def transferWord {Sites Local : Type*} [Fintype Sites] [DecidableEq Sites]
    [Fintype Local] [DecidableEq Local] (R S : Option Sites → Matrix (Local × Local) (Local × Local) ℂ) (KR KL : Matrix Local Local ℂ)
    (l : List Sites) (p : Sites) (endR endS : Matrix (Local × Local) (Local × Local) ℂ) : Module.End ℂ ((Sites → Local) → ℂ) :=
  partialTrace (oneOp none KL * twoOp none (some p) endR *
    starWord R S KR (l.map some) none * twoOp (some p) none endS)

def leftGate {Sites Local : Type*} [Fintype Sites] [DecidableEq Sites]
    [Fintype Local] [DecidableEq Local] (KL : Matrix Local Local ℂ) (p : Sites) (C : Matrix (Local × Local) (Local × Local) ℂ) : Module.End ℂ ((Sites → Local) → ℂ) :=
  partialTrace (oneOp none KL * twoOp (some p) none (checkedR C))

/-- The explicit double-row product; this chain has `N + 1` physical sites. -/
def transfer (N D : ℕ) (R : ℂ → ℂ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (KR KL : ℂ → Matrix (Fin D) (Fin D) ℂ) (u : ℂ) (θ : Fin (N + 1) → ℂ) :
    Module.End ℂ ((Fin (N + 1) → Fin D) → ℂ) :=
  partialTrace (oneOp none (KL u) *
    (((List.range (N + 1)).reverse.map fun i =>
      twoOp none (some (Fin.ofNat (N + 1) i)) (R u (θ (Fin.ofNat (N + 1) i)))).prod) *
    oneOp none (KR u) *
    ((List.range (N + 1)).map fun i =>
      twoOp (some (Fin.ofNat (N + 1) i)) none (R (θ (Fin.ofNat (N + 1) i)) (-u))).prod)

/-- Labels `0` and `N + 1` denote the right and left boundary gates. -/
def gate (N D : ℕ) (R : ℂ → ℂ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (KR KL : ℂ → Matrix (Fin D) (Fin D) ℂ) (κ : ℂ) :
    ℕ → Module.End ℂ ((Fin (N + 1) → Fin D) → ℂ)
  | 0 => oneOp 0 (KR κ)
  | i + 1 => if i = N then leftGate (KL κ) (Fin.last N) (R κ (-κ))
    else twoOp (Fin.ofNat (N + 1) i) (Fin.ofNat (N + 1) (i + 1)) (checkedR (R κ (-κ)))

/-- The ordered product uses the operator-product order of the permutation. -/
def circuitProduct (N D : ℕ) (R : ℂ → ℂ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (KR KL : ℂ → Matrix (Fin D) (Fin D) ℂ) (κ : ℂ) (π : Equiv.Perm (Fin (N + 2))) :
    Module.End ℂ ((Fin (N + 1) → Fin D) → ℂ) :=
  (List.ofFn fun i => gate N D R KR KL κ (π i).val).prod

/-- Every ordering is proportional to a double-row transfer matrix, and therefore
commutes with that family whenever the transfer matrices mutually commute.
The source's chain length is `N + 1`, and its site `i + 1` is encoded by `i : Fin (N + 1)`. -/
def claim : Prop :=
  ∀ (N D : ℕ) (R : ℂ → ℂ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (KR KL : ℂ → Matrix (Fin D) (Fin D) ℂ)
    (g : ℂ → ℂ) (κ : ℂ), 1 ≤ N →
    (∀ u, R u u = g u • ((Equiv.prodComm _ _).toPEquiv.toMatrix)) → g κ ≠ 0 → g (-κ) ≠ 0 →
    ∀ π : Equiv.Perm (Fin (N + 2)), ∃ θ : Fin (N + 1) → ℂ, ∃ c : ℂ,
      (∀ i, θ i = κ ∨ θ i = -κ) ∧ c ≠ 0 ∧
      circuitProduct N D R KR KL κ π = c • transfer N D R KR KL κ θ ∧
      ((∀ u v, Commute (transfer N D R KR KL u θ) (transfer N D R KR KL v θ)) →
        ∀ u, Commute (circuitProduct N D R KR KL κ π) (transfer N D R KR KL u θ))
theorem result : claim := by
  have circuit_labels (n : ℕ) (S : Finset ℕ) :
      (((circuit (n + 1) S).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0)) =
        ((List.range' 1 n).filter fun k => k ∈ S).reverse ++ [0] ++
          ((List.range' 1 n).filter fun k => k ∉ S) := by
    have hr : List.range' 1 (n + 1) = List.range' 1 n ++ [n + 1] := by
      simpa [Nat.add_comm] using (List.range'_1_concat (s := 1) (n := n))
    have hm (l : List ℕ) :
        ((l.map Gate.U).filter (· != Gate.KN)).map (fun | Gate.U j => j | _ => 0) = l := by
      induction l with
      | nil => simp
      | cons a l ih => simpa using congrArg (List.cons a) ih
    unfold circuit
    by_cases hs : n + 1 ∈ S <;>
      simp [hs, hr, List.filter_append, List.reverse_append, List.map_reverse,
        hm, List.append_assoc]
  have circuit_full_labels (n : ℕ) (S : Finset ℕ) (hn : 1 ≤ n) :
      ((circuit n S).reverse.map (fun | Gate.U j => j | Gate.K1 => 0 | Gate.KN => n)) =
        (((circuit (n + 1) S).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0)) := by
    rw [circuit_labels]
    have hr : List.range' 1 n = List.range' 1 (n - 1) ++ [n] := by
      simpa [show n - 1 + 1 = n by omega, show 1 + (n - 1) = n by omega]
        using (List.range'_1_concat (s := 1) (n := n - 1))
    unfold circuit
    by_cases hs : n ∈ S <;>
      simp [hs, hr, List.filter_append, List.reverse_append, List.map_reverse,
        List.map_map, Function.comp_def, List.append_assoc]
  let permOp {Sites Local : Type} (e : Equiv.Perm Sites) : Module.End ℂ ((Sites → Local) → ℂ) :=
    (LinearEquiv.piCongrLeft' ℂ (fun _ : (Sites → Local) => ℂ)
      (Equiv.arrowCongr e (Equiv.refl Local))).toLinearMap
  let swapOp {Sites Local : Type} [DecidableEq Sites] (i j : Sites) : Module.End ℂ ((Sites → Local) → ℂ) :=
    permOp (Equiv.swap i j)
  have key_injective (S : Finset ℕ) : Function.Injective (key S) := by
    intro a b hab
    unfold key at hab
    split_ifs at hab <;> omega

  have orderedInsert_prod {M : Type} [Monoid M] (A : ℕ → M)
      (k : ℕ → ℤ) (a : ℕ) (w : List ℕ)
      (h : ∀ b ∈ w, ¬ k a ≤ k b → Commute (A a) (A b)) :
      ((w.orderedInsert (fun x y => k x ≤ k y) a).map A).prod =
        A a * (w.map A).prod := by
    induction w with
    | nil => simp
    | cons b w ih =>
      by_cases hab : k a ≤ k b
      · simp [List.orderedInsert, hab]
      · simp only [List.orderedInsert, hab, if_false, List.map_cons, List.prod_cons]
        rw [ih (fun c hc => h c (List.mem_cons_of_mem b hc))]
        rw [← mul_assoc, (h b (List.mem_cons_self) hab).eq.symm, mul_assoc]

  have sorting_prod {M : Type} [Monoid M] (A : ℕ → M)
      (k : ℕ → ℤ) (w : List ℕ)
      (h : w.Pairwise (fun a b => k a ≤ k b ∨ Commute (A a) (A b))) :
      ((w.insertionSort (fun x y => k x ≤ k y)).map A).prod = (w.map A).prod := by
    induction w with
    | nil => simp
    | cons a w ih =>
      have hh := List.pairwise_cons.mp h
      rw [List.insertionSort_cons, orderedInsert_prod, ih hh.2]
      · simp
      · intro b hb hab
        exact (hh.1 b ((List.mem_insertionSort _).mp hb)).resolve_left hab

  have circuit_perm (N : ℕ) (S : Finset ℕ) :
      ((((circuit (N + 1) S).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0))).Perm (List.range (N + 1)) := by
    have hr : List.range (N + 1) = 0 :: List.range' 1 N := by
      rw [List.range_eq_range', List.range'_succ]
    rw [hr]
    rw [circuit_labels]
    simp only [List.append_assoc]
    apply List.perm_middle.trans
    apply List.Perm.cons
    apply ((List.reverse_perm _).append_right _).trans
    simpa using (List.filter_append_perm (fun k => decide (k ∈ S)) (List.range' 1 N))

  have circuit_sorted (N : ℕ) (S : Finset ℕ) :
      ((((circuit (N + 1) S).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0))).Pairwise (fun a b => key S a ≤ key S b) := by
    have hs : (List.range' 1 N).Pairwise (fun a b => a < b) := List.pairwise_lt_range'
    have hl : (((List.range' 1 N).filter fun k => k ∈ S).reverse).Pairwise
        (fun a b => key S a ≤ key S b) := by
      rw [List.pairwise_reverse, List.pairwise_filter]
      apply hs.imp_of_mem
      intro a b ha hb hab hsa hsb
      simp only [decide_eq_true_eq] at hsa hsb
      simp [key, hsa, hsb]
      omega
    have hr : ((List.range' 1 N).filter fun k => k ∉ S).Pairwise
        (fun a b => key S a ≤ key S b) := by
      rw [List.pairwise_filter]
      apply hs.imp_of_mem
      intro a b ha hb hab hsa hsb
      simp only [decide_eq_true_eq] at hsa hsb
      simp [key, hsa, hsb]
      omega
    simp only [circuit_labels, List.pairwise_append, hl, hr, List.pairwise_singleton,
      true_and, List.mem_reverse, List.mem_filter, decide_eq_true_eq,
      List.mem_append, List.mem_singleton]
    constructor
    · intro a ha b hb
      subst b
      simp [key, ha.2]
    · intro a ha b hb
      rcases ha with ha | rfl
      · simp [key, ha.2, hb.2]
      · simp [key, hb.2]

  have word_sorted_or_commute {M : Type} [Monoid M]
      (A : ℕ → M) (N : ℕ) (w : List ℕ)
      (hw : w.Perm (List.range (N + 1)))
      (hc : ∀ i ≤ N, ∀ j ≤ N, i + 2 ≤ j ∨ j + 2 ≤ i → Commute (A i) (A j)) :
      w.Pairwise (fun a b => key (inversionSet N w) a ≤ key (inversionSet N w) b ∨
        Commute (A a) (A b)) := by
    have hnd := hw.symm.nodup List.nodup_range
    have hi : w.Pairwise (fun a b => w.idxOf a < w.idxOf b) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simpa only [hnd.idxOf_getElem] using hij
    apply hi.imp_of_mem
    intro a b ha hb hab
    have haN : a ≤ N := by have := List.mem_range.mp (hw.mem_iff.mp ha); omega
    have hbN : b ≤ N := by have := List.mem_range.mp (hw.mem_iff.mp hb); omega
    by_cases hfar : a + 2 ≤ b ∨ b + 2 ≤ a
    · exact Or.inr (hc a haN b hbN hfar)
    · left
      have hne : a ≠ b := by intro he; subst b; omega
      have hadj : a + 1 = b ∨ b + 1 = a := by omega
      rcases hadj with hadj | hadj
      · have hbS : b ∉ inversionSet N w := by
          simp only [inversionSet, Finset.mem_filter, Finset.mem_Icc]
          have hpred : b - 1 = a := by omega
          rw [hpred]
          omega
        unfold key
        rw [if_neg hbS]
        split_ifs <;> omega
      · have haS : a ∈ inversionSet N w := by
          simp only [inversionSet, Finset.mem_filter, Finset.mem_Icc]
          have hpred : a - 1 = b := by omega
          rw [hpred]
          exact ⟨⟨by omega, haN⟩, hab⟩
        unfold key
        rw [if_pos haS]
        split_ifs <;> omega

  have trace_lemma {M : Type} [Monoid M] (A : ℕ → M) (N : ℕ) (w : List ℕ)
      (hw : w.Perm (List.range (N + 1)))
      (hc : ∀ i ≤ N, ∀ j ≤ N, i + 2 ≤ j ∨ j + 2 ≤ i → Commute (A i) (A j)) :
      (w.map A).prod = (((((circuit (N + 1) (inversionSet N w)).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0))).map A).prod := by
    let S := inversionSet N w
    let r : ℕ → ℕ → Prop := fun a b => key S a ≤ key S b
    letI : DecidableRel r := fun a b => inferInstanceAs (Decidable (key S a ≤ key S b))
    letI : Std.Total r := ⟨fun a b => le_total _ _⟩
    letI : IsTrans ℕ r := ⟨fun a b c => le_trans⟩
    have he : w.insertionSort r = (((circuit (N + 1) S).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0)) := by
      apply List.Perm.eq_of_pairwise
      · intro a b ha hb hab hba
        exact key_injective S (le_antisymm hab hba)
      · exact List.pairwise_insertionSort r w
      · exact circuit_sorted N S
      · exact (List.perm_insertionSort r w).trans (hw.trans (circuit_perm N S).symm)
    have hp := sorting_prod A (key S) w (word_sorted_or_commute A N w hw hc)
    change ((w.insertionSort r).map A).prod = (w.map A).prod at hp
    rw [he] at hp
    exact hp.symm

  have permOp_apply {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (e : Equiv.Perm Sites) (f : (Sites → Local) → ℂ)
      (x : (Sites → Local)) : permOp e f x = f (x ∘ e) := rfl

  have oneOp_apply {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i : Sites) (B : Matrix Local Local ℂ)
      (f : (Sites → Local) → ℂ) (x : (Sites → Local)) :
      oneOp i B f x = ∑ p, B (x i) p * f (Function.update x i p) := rfl

  have twoOp_apply {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i j : Sites) (R : Matrix (Local × Local) (Local × Local) ℂ)
      (f : (Sites → Local) → ℂ) (x : (Sites → Local)) :
      twoOp i j R f x =
        ∑ p, R (x i, x j) p * f (Function.update (Function.update x i p.1) j p.2) := rfl

  have update_permute {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (e : Equiv.Perm Sites) (x : (Sites → Local))
      (i : Sites) (p : Local) :
      Function.update (x ∘ e) i p = (Function.update x (e i) p) ∘ e := by
    ext k
    by_cases h : k = i
    · subst k; simp
    · have h' : e k ≠ e i := fun he => h (e.injective he)
      simp [permOp_apply, oneOp_apply, twoOp_apply, Function.update_of_ne h, Function.update_of_ne h']

  have permOp_mul {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (e f : Equiv.Perm Sites) :
      (permOp e : Module.End ℂ ((Sites → Local) → ℂ)) * permOp f = permOp (e * f) := by
    apply LinearMap.ext; intro v; funext x
    rfl

  have permOp_one {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] : (permOp (1 : Equiv.Perm Sites) : Module.End ℂ ((Sites → Local) → ℂ)) = 1 := by
    apply LinearMap.ext; intro v; funext x
    rfl

  have perm_one {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (e : Equiv.Perm Sites) (i : Sites) (B : Matrix Local Local ℂ) :
      permOp e * oneOp i B = oneOp (e i) B * permOp e := by
    apply LinearMap.ext; intro f; funext x
    simp only [Module.End.mul_apply, permOp_apply, oneOp_apply, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro p hp
    rw [update_permute]

  have perm_two {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (e : Equiv.Perm Sites) (i j : Sites) (R : Matrix (Local × Local) (Local × Local) ℂ) :
      permOp e * twoOp i j R = twoOp (e i) (e j) R * permOp e := by
    apply LinearMap.ext; intro f; funext x
    simp only [Module.End.mul_apply, permOp_apply, twoOp_apply, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro p hp
    rw [update_permute, update_permute]

  have p_apply {Local : Type} [DecidableEq Local] (x y : Local × Local) :
      ((Equiv.prodComm Local Local).toPEquiv.toMatrix : Matrix (Local × Local) (Local × Local) ℂ) x y =
        if (x.2, x.1) = y then 1 else 0 := by
    simp [PEquiv.toMatrix, Equiv.toPEquiv, Equiv.prodComm, Prod.swap, eq_comm]
  have localP_mul {Local : Type} [Fintype Local]  [DecidableEq Local] (R : Matrix (Local × Local) (Local × Local) ℂ)
      (x y : Local × Local) : ((((Equiv.prodComm _ _).toPEquiv.toMatrix) : Matrix (Local × Local) (Local × Local) ℂ) * R) x y = R (x.2, x.1) y := by
    simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, Matrix.mul_apply, p_apply, Prod.swap]

  have swapOp_sq {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i j : Sites) :
      (swapOp i j : Module.End ℂ ((Sites → Local) → ℂ)) * swapOp i j = 1 := by
    simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp]

  have swapOp_cancel {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i j : Sites) (B : Module.End ℂ ((Sites → Local) → ℂ)) :
      swapOp i j * (swapOp i j * B) = B := by
    rw [← mul_assoc, swapOp_sq, one_mul]

  have swap_update_two {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i j : Sites) (hij : i ≠ j)
      (x : (Sites → Local)) (p : Local × Local) :
      Function.update (Function.update (x ∘ Equiv.swap i j) i p.1) j p.2 =
        Function.update (Function.update x i p.1) j p.2 := by
    ext k
    by_cases hki : k = i
    · subst k; simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, hij]
    · by_cases hkj : k = j
      · subst k; simp
      · simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, Function.update_of_ne hki, Function.update_of_ne hkj,
          Equiv.swap_apply_of_ne_of_ne hki hkj]

  have checked_embed {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local]  [DecidableEq Local] (i j : Sites) (hij : i ≠ j)
      (R : Matrix (Local × Local) (Local × Local) ℂ) :
      twoOp i j (checkedR R) = swapOp i j * twoOp i j R := by
    apply LinearMap.ext; intro f; funext x
    simp only [Module.End.mul_apply, swapOp, permOp_apply, twoOp_apply,
      checkedR, localP_mul, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    apply Finset.sum_congr rfl
    intro p hp
    rw [swap_update_two i j hij]

  have reversed_embed {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local]  [DecidableEq Local] (i j : Sites) (hij : i ≠ j)
      (R : Matrix (Local × Local) (Local × Local) ℂ) :
      twoOp j i R = twoOp i j (checkedR R) * swapOp i j := by
    rw [checked_embed i j hij]
    unfold swapOp
    rw [perm_two]
    simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, mul_assoc, Equiv.swap_apply_left, Equiv.swap_apply_right]

  have plain_embed {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local]  [DecidableEq Local] (i j : Sites) (hij : i ≠ j)
      (R : Matrix (Local × Local) (Local × Local) ℂ) :
      twoOp i j R = swapOp i j * twoOp i j (checkedR R) := by
    rw [checked_embed i j hij, ← mul_assoc, swapOp_sq, one_mul]

  have perm_star {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (R S : Sites → Matrix (Local × Local) (Local × Local) ℂ) (K : Matrix Local Local ℂ)
      (e : Equiv.Perm Sites) (l : List Sites) (p : Sites)
      (hfix : ∀ i ∈ l, e i = i) :
      permOp e * starWord R S K l p = starWord R S K l (e p) * permOp e := by
    induction l with
    | nil => exact perm_one e p K
    | cons i l ih =>
      have hi := hfix i List.mem_cons_self
      have hl : ∀ j ∈ l, e j = j := fun j hj => hfix j (List.mem_cons_of_mem i hj)
      simp only [starWord]
      calc
        permOp e * (twoOp p i (R i) * starWord R S K l p * twoOp i p (S i)) =
            twoOp (e p) i (R i) * (permOp e * starWord R S K l p) * twoOp i p (S i) := by
          simp only [← mul_assoc, perm_two, hi]
        _ = twoOp (e p) i (R i) * (starWord R S K l (e p) * permOp e) * twoOp i p (S i) := by
          rw [ih hl]
        _ = (twoOp (e p) i (R i) * starWord R S K l (e p) * twoOp i (e p) (S i)) * permOp e := by
          simp only [mul_assoc, perm_two, hi]

  have train_identity {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local]  [DecidableEq Local] (R S : Sites → Matrix (Local × Local) (Local × Local) ℂ)
      (K : Matrix Local Local ℂ) (l : List Sites) (p : Sites)
      (hnd : l.Nodup) (hp : p ∉ l) :
      starWord R S K l p = nearestWord R S K l p := by
    induction l generalizing p with
    | nil => rfl
    | cons i l ih =>
      have hi := (List.nodup_cons.mp hnd).1
      have hl := (List.nodup_cons.mp hnd).2
      have hpi : p ≠ i := fun h => hp (by simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, h])
      have hpl : p ∉ l := fun h => hp (List.mem_cons_of_mem i h)
      have hfix : ∀ j ∈ l, Equiv.swap i p j = j := by
        intro j hj
        exact Equiv.swap_apply_of_ne_of_ne
          (fun h => hi (h ▸ hj)) (fun h => hpl (h ▸ hj))
      have hs := perm_star R S K (Equiv.swap i p) l p hfix
      simp only [Equiv.swap_apply_right] at hs
      change swapOp i p * starWord R S K l p = starWord R S K l i * swapOp i p at hs
      simp only [starWord, nearestWord]
      rw [reversed_embed i p hpi.symm (R i), plain_embed i p hpi.symm (S i)]
      calc
        twoOp i p (checkedR (R i)) * swapOp i p * starWord R S K l p *
            (swapOp i p * twoOp i p (checkedR (S i))) =
            twoOp i p (checkedR (R i)) * starWord R S K l i *
              twoOp i p (checkedR (S i)) := by
          simp only [mul_assoc]
          rw [← mul_assoc (swapOp i p) (starWord R S K l p), hs]
          simp only [mul_assoc, swapOp_cancel]
        _ = _ := by rw [ih i hl hi]

  have auxConfig_none {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (a : Local) (x : (Sites → Local)) : (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x) none = a := rfl

  have auxConfig_some {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (a : Local) (x : (Sites → Local)) (i : Sites) :
      (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x) (some i) = x i := rfl

  have auxConfig_comp_some {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (a : Local) (x : (Sites → Local)) :
      (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x) ∘ some = x := rfl

  have config_aux {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (y : (Option Sites → Local)) :
      (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm ((y none), (y ∘ some)) = y := by ext k; cases k <;> rfl

  have traceSum_apply {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (F : Module.End ℂ ((Option Sites → Local) → ℂ))
      (f : (Sites → Local) → ℂ) (x : (Sites → Local)) :
      traceSum F f x = ∑ a : Local, F (putAux a f) ((Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x)) := by
    simp [traceSum, takeAux, LinearMap.sum_apply]
  have putAux_basis {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (a : Local) (x : (Sites → Local)) :
      putAux a (Pi.single x 1) = Pi.single ((Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x)) 1 := by
    ext y
    have he : y = (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x) ↔ y none = a ∧ y ∘ some = x := by
      constructor
      · intro h
        subst y
        exact ⟨rfl,rfl⟩
      · rintro ⟨h,h'⟩
        rw [← config_aux y, h, h']
    by_cases ha : y none = a
    · by_cases hb : y ∘ some = x
      · have hy := he.mpr ⟨ha,hb⟩
        subst y
        simp [auxConfig_none, auxConfig_comp_some, putAux, Pi.single_apply]
      · have hy : y ≠ (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x) := fun h => hb (he.mp h).2
        simp [auxConfig_none, auxConfig_comp_some, putAux, Pi.single_apply, ha, hb, hy, Ne.symm hy]
    · have hy : y ≠ (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x) := fun h => ha (he.mp h).1
      simp [auxConfig_none, auxConfig_comp_some, putAux, Pi.single_apply, ha, hy, Ne.symm hy]

  have traceSum_matrix {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (F : Module.End ℂ ((Option Sites → Local) → ℂ)) :
      (LinearMap.toMatrixAlgEquiv' (R := ℂ)) (traceSum F) =
        D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft
          (Matrix.reindex (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local))
            (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local))
            ((LinearMap.toMatrixAlgEquiv' (R := ℂ)) F)) := by
    ext x y
    simp only [LinearMap.toMatrixAlgEquiv'_apply, traceSum_apply,
      putAux_basis, D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft,
      Matrix.reindex_apply, Matrix.submatrix_apply]

  have partialTrace_eq {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (F : Module.End ℂ ((Option Sites → Local) → ℂ)) :
      partialTrace F = traceSum F := by
    apply (LinearMap.toMatrixAlgEquiv' (R := ℂ)).injective
    rw [traceSum_matrix]
    exact (LinearMap.toMatrixAlgEquiv' (R := ℂ)).apply_symm_apply _
  have partialTrace_apply {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (F : Module.End ℂ ((Option Sites → Local) → ℂ))
      (f : (Sites → Local) → ℂ) (x : (Sites → Local)) :
      partialTrace F f x = ∑ a : Local, F (putAux a f) ((Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x)) := by
    rw [partialTrace_eq, traceSum_apply]
  have lift_put {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (B : Module.End ℂ ((Sites → Local) → ℂ)) (a : Local) (f : (Sites → Local) → ℂ) :
      liftPhysical B (putAux a f) = putAux a (B f) := by
    ext y
    simp only [liftPhysical, LinearMap.coe_mk, AddHom.coe_mk, putAux,
      auxConfig_none, auxConfig_comp_some]
    by_cases h : y none = a
    · simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, h]
    · simp only [h, if_false]
      change B 0 (y ∘ some) = 0
      simp

  have partialTrace_left {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (B : Module.End ℂ ((Sites → Local) → ℂ)) (F : Module.End ℂ ((Option Sites → Local) → ℂ)) :
      partialTrace (liftPhysical B * F) = B * partialTrace F := by
    apply LinearMap.ext; intro f; funext x
    simp only [partialTrace_apply, Module.End.mul_apply, liftPhysical,
      LinearMap.coe_mk, AddHom.coe_mk, auxConfig_none, auxConfig_comp_some]
    have hv : partialTrace F f = ∑ a : Local, fun z => F (putAux a f) ((Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, z)) := by
      funext z
      simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, partialTrace_apply]
    rw [hv, map_sum]
    simp

  have partialTrace_right {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (B : Module.End ℂ ((Sites → Local) → ℂ)) (F : Module.End ℂ ((Option Sites → Local) → ℂ)) :
      partialTrace (F * liftPhysical B) = partialTrace F * B := by
    apply LinearMap.ext; intro f; funext x
    simp only [partialTrace_apply, Module.End.mul_apply, lift_put]

  have partialTrace_smul {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (c : ℂ) (F : Module.End ℂ ((Option Sites → Local) → ℂ)) :
      partialTrace (c • F) = c • partialTrace F := by
    apply LinearMap.ext; intro f; funext x
    simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, partialTrace_apply, Finset.mul_sum]

  have update_aux {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (a : Local) (x : (Sites → Local)) (i : Sites) (p : Local) :
      Function.update ((Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x)) (some i) p = (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, (Function.update x i p)) := by
    ext k
    cases k with
    | none => simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, Function.update_of_ne]
    | some k => by_cases h : k = i <;> simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, h, Function.update_of_ne]

  have update_aux_none {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (a : Local) (x : (Sites → Local)) (p : Local) :
      Function.update ((Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, x)) none p = (Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (p, x) := by
    ext k
    cases k <;> simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, Function.update_of_ne]

  have lift_one {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i : Sites) (B : Matrix Local Local ℂ) :
      liftPhysical (oneOp i B) = oneOp (some i) B := by
    apply LinearMap.ext; intro f; funext y
    conv_rhs => rw [← config_aux y]
    simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, liftPhysical, oneOp_apply, update_aux]

  have lift_two {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i j : Sites) (R : Matrix (Local × Local) (Local × Local) ℂ) :
      liftPhysical (twoOp i j R) = twoOp (some i) (some j) R := by
    apply LinearMap.ext; intro f; funext y
    conv_rhs => rw [← config_aux y]
    simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, liftPhysical, twoOp_apply, update_aux]

  have lift_mul {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (A B : Module.End ℂ ((Sites → Local) → ℂ)) :
      liftPhysical (A * B) = liftPhysical A * liftPhysical B := by
    apply LinearMap.ext; intro f; funext y
    simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, liftPhysical, Module.End.mul_apply]

  have lift_star {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (R S : Sites → Matrix (Local × Local) (Local × Local) ℂ) (K : Matrix Local Local ℂ)
      (l : List Sites) (p : Sites) (R' S' : Option Sites → Matrix (Local × Local) (Local × Local) ℂ)
      (hR : ∀ i, R' (some i) = R i) (hS : ∀ i, S' (some i) = S i) :
      liftPhysical (starWord R S K l p) = starWord R' S' K (l.map some) (some p) := by
    induction l with
    | nil => exact lift_one p K
    | cons i l ih => simp only [starWord, List.map_cons, lift_mul, lift_two, ih, hR, hS]

  have auxiliary_one_commutes {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (B : Module.End ℂ ((Sites → Local) → ℂ)) (K : Matrix Local Local ℂ) :
      Commute (oneOp none K) (liftPhysical B) := by
    apply LinearMap.ext; intro f; funext y
    conv_lhs => rw [← config_aux y]
    conv_rhs => rw [← config_aux y]
    simp only [Commute, SemiconjBy, Module.End.mul_apply, oneOp_apply, liftPhysical,
      LinearMap.coe_mk, AddHom.coe_mk, auxConfig_none, auxConfig_comp_some, update_aux_none]
    have hv : (fun z => ∑ a : Local, K (y none) a * f ((Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, z))) =
        ∑ a : Local, K (y none) a • (fun z => f ((Equiv.piOptionEquivProd (β := fun _ : Option Sites => Local)).symm (a, z))) := by
      funext z
      simp
    rw [hv, map_sum]
    simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, map_smul]

  have twoOp_smul {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i j : Sites) (c : ℂ) (R : Matrix (Local × Local) (Local × Local) ℂ) :
      twoOp i j (c • R) = c • twoOp i j R := by
    apply LinearMap.ext; intro f; funext x
    simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, twoOp_apply, Matrix.smul_apply, Finset.mul_sum, mul_assoc]

  have twoOp_P {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i j : Sites) (hij : i ≠ j) :
      twoOp i j (((Equiv.prodComm _ _).toPEquiv.toMatrix) : Matrix (Local × Local) (Local × Local) ℂ) = swapOp i j := by
    apply LinearMap.ext; intro f; funext x
    simp only [twoOp_apply, p_apply]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, swapOp, permOp_apply]
    congr 1
    ext k
    by_cases hki : k = i
    · subst k
      simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, hij]
    · by_cases hkj : k = j
      · subst k
        simp
      · simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, Function.update_of_ne hki, Function.update_of_ne hkj,
          Equiv.swap_apply_of_ne_of_ne hki hkj]

  have twoOp_one {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i j : Sites) : twoOp i j (1 : Matrix (Local × Local) (Local × Local) ℂ) = 1 := by
    apply LinearMap.ext; intro f; funext x
    simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, twoOp_apply, Matrix.one_apply, Function.update_eq_self]

  have localP_sq {Local : Type} [Fintype Local] [DecidableEq Local] : (((Equiv.prodComm _ _).toPEquiv.toMatrix) : Matrix (Local × Local) (Local × Local) ℂ) * ((Equiv.prodComm _ _).toPEquiv.toMatrix) = 1 := by
    ext x y
    simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, twoOp_one, localP_mul, p_apply, Matrix.one_apply, Prod.mk.injEq, eq_comm, and_comm]

  have lemma1 {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (R S : Option Sites → Matrix (Local × Local) (Local × Local) ℂ) (KR KL : Matrix Local Local ℂ)
      (l : List Sites) (p : Sites) (g : ℂ) (C : Matrix (Local × Local) (Local × Local) ℂ)
      (hnd : l.Nodup) (hp : p ∉ l) :
      transferWord R S KR KL l p (g • (((Equiv.prodComm _ _).toPEquiv.toMatrix) : Matrix (Local × Local) (Local × Local) ℂ)) C =
        g • (nearestWord (fun i => R (some i)) (fun i => S (some i)) KR l p * leftGate KL p C) := by
    have hfix : ∀ j ∈ l.map some, Equiv.swap none (some p) j = j := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      exact Equiv.swap_apply_of_ne_of_ne (by simp)
        (fun h => hp (Option.some.inj h ▸ hi))
    have hmove := perm_star R S KR (Equiv.swap none (some p)) (l.map some) none hfix
    simp only [Equiv.swap_apply_left] at hmove
    change swapOp none (some p) * starWord R S KR (l.map some) none =
      starWord R S KR (l.map some) (some p) * swapOp none (some p) at hmove
    have hlift := lift_star (fun i => R (some i)) (fun i => S (some i)) KR l p R S
      (fun _ => rfl) (fun _ => rfl)
    have hswap : (swapOp none (some p) : Module.End ℂ ((Option Sites → Local) → ℂ)) = swapOp (some p) none := by
      simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, twoOp_one, localP_sq, swapOp, Equiv.swap_comm]
    have hcheck : swapOp none (some p) * twoOp (some p) none C =
        twoOp (some p) none (checkedR C) := by
      rw [hswap]
      exact (checked_embed (some p) none (by simp) C).symm
    unfold transferWord
    rw [twoOp_smul, twoOp_P none (some p) (by simp)]
    simp only [mul_smul_comm, smul_mul_assoc, partialTrace_smul]
    congr 1
    calc
      partialTrace (oneOp none KL * swapOp none (some p) *
          starWord R S KR (l.map some) none * twoOp (some p) none C) =
          partialTrace (oneOp none KL * starWord R S KR (l.map some) (some p) *
            twoOp (some p) none (checkedR C)) := by
        congr 1
        simp only [mul_assoc]
        rw [← mul_assoc (swapOp none (some p)) (starWord R S KR (l.map some) none), hmove]
        simp only [mul_assoc, hcheck]
      _ = partialTrace (liftPhysical (starWord (fun i => R (some i))
          (fun i => S (some i)) KR l p) *
          (oneOp none KL * twoOp (some p) none (checkedR C))) := by
        rw [← hlift, (auxiliary_one_commutes _ KL).eq]
        rw [mul_assoc]
      _ = starWord (fun i => R (some i)) (fun i => S (some i)) KR l p * leftGate KL p C := by
        rw [partialTrace_left]
        rfl
      _ = _ := by rw [train_identity _ _ KR l p hnd hp]

  have lemma2 {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (R S : Option Sites → Matrix (Local × Local) (Local × Local) ℂ) (KR KL : Matrix Local Local ℂ)
      (l : List Sites) (p : Sites) (g : ℂ) (C : Matrix (Local × Local) (Local × Local) ℂ)
      (hnd : l.Nodup) (hp : p ∉ l) :
      transferWord R S KR KL l p C (g • (((Equiv.prodComm _ _).toPEquiv.toMatrix) : Matrix (Local × Local) (Local × Local) ℂ)) =
        g • (leftGate KL p C * nearestWord (fun i => R (some i))
          (fun i => S (some i)) KR l p) := by
    have hfix : ∀ j ∈ l.map some, Equiv.swap none (some p) j = j := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      exact Equiv.swap_apply_of_ne_of_ne (by simp)
        (fun h => hp (Option.some.inj h ▸ hi))
    have hmove := perm_star R S KR (Equiv.swap none (some p)) (l.map some) (some p) hfix
    simp only [Equiv.swap_apply_right] at hmove
    change swapOp none (some p) * starWord R S KR (l.map some) (some p) =
      starWord R S KR (l.map some) none * swapOp none (some p) at hmove
    have hlift := lift_star (fun i => R (some i)) (fun i => S (some i)) KR l p R S
      (fun _ => rfl) (fun _ => rfl)
    have hswap : (swapOp none (some p) : Module.End ℂ ((Option Sites → Local) → ℂ)) = swapOp (some p) none := by
      simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, twoOp_one, localP_sq, swapOp, Equiv.swap_comm]
    have hcheck : twoOp none (some p) C * swapOp none (some p) =
        twoOp (some p) none (checkedR C) := by
      rw [hswap, reversed_embed (some p) none (by simp) C]
      simp [permOp_apply, oneOp_apply, twoOp_apply, permOp_mul, permOp_one, swapOp_sq, swapOp_cancel, partialTrace_apply, auxConfig_none, auxConfig_some, auxConfig_comp_some, twoOp_one, localP_sq, mul_assoc, swapOp_cancel]
    unfold transferWord
    rw [twoOp_smul, twoOp_P (some p) none (by simp)]
    simp only [mul_smul_comm, smul_mul_assoc, partialTrace_smul]
    congr 1
    rw [← hswap]
    calc
      partialTrace (oneOp none KL * twoOp none (some p) C *
          starWord R S KR (l.map some) none * swapOp none (some p)) =
          partialTrace ((oneOp none KL * twoOp (some p) none (checkedR C)) *
            starWord R S KR (l.map some) (some p)) := by
        congr 1
        rw [mul_assoc, hmove.symm, ← mul_assoc]
        rw [mul_assoc (oneOp none KL) (twoOp none (some p) C) (swapOp none (some p)), hcheck]
      _ = partialTrace ((oneOp none KL * twoOp (some p) none (checkedR C)) *
          liftPhysical (starWord (fun i => R (some i)) (fun i => S (some i)) KR l p)) := by
        rw [hlift]
      _ = leftGate KL p C * starWord (fun i => R (some i)) (fun i => S (some i)) KR l p := by
        rw [partialTrace_right]
        rfl
      _ = _ := by rw [train_identity _ _ KR l p hnd hp]


  have star_product {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (R S : Sites → Matrix (Local × Local) (Local × Local) ℂ)
      (K : Matrix Local Local ℂ) (l : List Sites) (p : Sites) :
      starWord R S K l p = (l.map fun i => twoOp p i (R i)).prod * oneOp p K *
        (l.reverse.map fun i => twoOp i p (S i)).prod := by
    induction l with
    | nil => simp [starWord]
    | cons i l ih => simp [starWord, ih, List.reverse_cons, List.map_append, mul_assoc]
  have circuit_step (n : ℕ) (S : Finset ℕ) :
      (((circuit ((n + 1) + 1) S).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0)) = if n + 1 ∈ S then (n + 1) :: (((circuit (n + 1) S).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0))
        else (((circuit (n + 1) S).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0)) ++ [n + 1] := by
    rw [circuit_labels, List.range'_concat]
    by_cases hs : n + 1 ∈ S <;> simp [hs, Nat.add_comm, circuit_labels, List.filter_append, List.reverse_append,
      List.append_assoc]

  have one_two {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i j k : Sites) (hij : i ≠ j) (hik : i ≠ k)
      (B : Matrix Local Local ℂ) (C : Matrix (Local × Local) (Local × Local) ℂ) : Commute (oneOp i B) (twoOp j k C) := by
    apply LinearMap.ext; intro f; funext x
    simp only [Module.End.mul_apply, oneOp_apply, twoOp_apply]
    simp only [Function.update_of_ne hij, Function.update_of_ne hij.symm,
      Function.update_of_ne hik, Function.update_of_ne hik.symm,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p hp
    apply Finset.sum_congr rfl; intro q hq
    rw [Function.update_comm hij, Function.update_comm hik]
    ring
  have two_two {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i j k l : Sites)
      (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
      (B C : Matrix (Local × Local) (Local × Local) ℂ) : Commute (twoOp i j B) (twoOp k l C) := by
    apply LinearMap.ext; intro f; funext x
    simp only [Module.End.mul_apply, twoOp_apply]
    simp only [Function.update_of_ne hik, Function.update_of_ne hik.symm,
      Function.update_of_ne hil, Function.update_of_ne hil.symm,
      Function.update_of_ne hjk, Function.update_of_ne hjk.symm,
      Function.update_of_ne hjl, Function.update_of_ne hjl.symm,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p hp
    apply Finset.sum_congr rfl; intro q hq
    rw [Function.update_comm hjk, Function.update_comm hik,
      Function.update_comm hjl, Function.update_comm hil]
    ring
  have left_comm_one {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i p : Sites) (hip : i ≠ p)
      (B KL : Matrix Local Local ℂ) (C : Matrix (Local × Local) (Local × Local) ℂ) :
      Commute (oneOp i B) (leftGate KL p C) := by
    have hc : Commute (liftPhysical (oneOp i B))
        (oneOp none KL * twoOp (some p) none (checkedR C)) := by
      apply ((auxiliary_one_commutes (oneOp i B) KL).symm).mul_right
      rw [lift_one]
      exact one_two (some i) (some p) none (fun h => hip (Option.some.inj h)) (by simp) B _
    change oneOp i B * partialTrace _ = partialTrace _ * oneOp i B
    rw [← partialTrace_left, ← partialTrace_right, hc.eq]
  have left_comm_two {Sites Local : Type} [Fintype Sites] [DecidableEq Sites]
      [Fintype Local] [DecidableEq Local] (i j p : Sites) (hip : i ≠ p) (hjp : j ≠ p)
      (B : Matrix (Local × Local) (Local × Local) ℂ) (KL : Matrix Local Local ℂ) (C : Matrix (Local × Local) (Local × Local) ℂ) :
      Commute (twoOp i j B) (leftGate KL p C) := by
    have hc : Commute (liftPhysical (twoOp i j B))
        (oneOp none KL * twoOp (some p) none (checkedR C)) := by
      apply ((auxiliary_one_commutes (twoOp i j B) KL).symm).mul_right
      rw [lift_two]
      exact two_two (some i) (some j) (some p) none
        (fun h => hip (Option.some.inj h)) (by simp)
        (fun h => hjp (Option.some.inj h)) (by simp) B _
    change twoOp i j B * partialTrace _ = partialTrace _ * twoOp i j B
    rw [← partialTrace_left, ← partialTrace_right, hc.eq]

  intro N D R KR KL g κ hN hreg hgplus hgminus π
  let e : ℕ → Fin (N + 1) := Fin.ofNat (N + 1)
  let A := gate N D R KR KL κ
  let w := List.ofFn fun i : Fin (N + 2) => (π i).val
  have heval (i : ℕ) (hi : i ≤ N) : (e i).val = i := by
    simp [e, Fin.val_ofNat, Nat.mod_eq_of_lt (show i < N + 1 by omega)]
  have hene (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) (hne : i ≠ j) : e i ≠ e j := by
    intro h; apply hne; simpa only [heval i hi, heval j hj] using congrArg Fin.val h
  have hezero : e 0 = 0 := by apply Fin.ext; simp [heval 0 (by omega)]
  have helast : e N = Fin.last N := Fin.ext (heval N (le_refl N))
  have hbase : (List.ofFn fun i : Fin (N + 2) => i.val) = List.range (N + 2) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_range]
    · intro i hi hi'; simp only [List.getElem_ofFn, List.getElem_range]
  have hw : w.Perm (List.range (N + 2)) := by
    simpa only [w, Function.comp_def, hbase] using π.ofFn_comp_perm (fun i => i.val)
  let S := inversionSet (N + 1) w
  let θ : Fin (N + 1) → ℂ := fun i => if i.val + 1 ∈ S then -κ else κ
  let r : Fin (N + 1) → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun i => R κ (θ i)
  let s : Fin (N + 1) → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun i => R (θ i) (-κ)
  have hchecked (u : ℂ) : checkedR (R u u) = g u • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := by
    rw [hreg]; simp [checkedR, localP_sq]
  have hcollapse : ∀ n : ℕ, n ≤ N → ∃ c : ℂ, c ≠ 0 ∧
      nearestWord r s (KR κ) ((List.range n).reverse.map e) (e n) =
        c • (((((circuit (n + 1) S).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0))).map A).prod := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨1, one_ne_zero, ?_⟩
      simp [nearestWord, circuit_labels, A, gate, hezero]
    | succ n ih =>
      intro hn
      obtain ⟨c, hc, he⟩ := ih (by omega)
      have hstep : ((List.range (n + 1)).reverse.map e) = e n :: ((List.range n).reverse.map e) := by
        simp [List.range_succ, List.reverse_append]
      have hagate : A (n + 1) = twoOp (e n) (e (n + 1)) (checkedR (R κ (-κ))) := by
        simp [A, gate, show n ≠ N by omega, e]
      rw [hstep, nearestWord, he]
      by_cases hs : n + 1 ∈ S
      · have hθ : θ (e n) = -κ := by simp [θ, heval n (by omega), hs]
        refine ⟨g (-κ) * c, mul_ne_zero hgminus hc, ?_⟩
        simp only [r, s, hθ, hchecked, twoOp_smul, twoOp_one,
          mul_smul_comm, smul_mul_assoc, mul_one, smul_smul]
        rw [circuit_step, if_pos hs, List.map_cons, List.prod_cons, hagate]
      · have hθ : θ (e n) = κ := by simp [θ, heval n (by omega), hs]
        refine ⟨g κ * c, mul_ne_zero hgplus hc, ?_⟩
        simp only [r, s, hθ, hchecked, twoOp_smul, twoOp_one,
          mul_smul_comm, smul_mul_assoc, one_mul, smul_smul]
        rw [circuit_step, if_neg hs, List.map_append, List.prod_append,
          List.map_singleton, List.prod_singleton, hagate]
        congr 1
        ring
  let l := (List.range N).reverse.map e
  have hlnd : l.Nodup := by
    apply (List.nodup_map_iff_inj_on (List.nodup_reverse.mpr List.nodup_range)).mpr
    intro i hi j hj he
    have hiN : i ≤ N := by have := List.mem_range.mp (List.mem_reverse.mp hi); omega
    have hjN : j ≤ N := by have := List.mem_range.mp (List.mem_reverse.mp hj); omega
    simpa only [heval i hiN, heval j hjN] using congrArg Fin.val he
  have hp : e N ∉ l := by
    intro h
    obtain ⟨i, hi, he⟩ := List.mem_map.mp h
    have hiN : i < N := List.mem_range.mp (List.mem_reverse.mp hi)
    have hv := congrArg Fin.val he
    rw [heval i (by omega), heval N (by omega)] at hv
    omega
  let r' : Option (Fin (N + 1)) → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun i => r (i.getD 0)
  let s' : Option (Fin (N + 1)) → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun i => s (i.getD 0)
  have ht : transfer N D R KR KL κ θ =
      transferWord r' s' (KR κ) (KL κ) l (e N) (r (e N)) (s (e N)) := by
    simp only [transfer, transferWord, star_product, List.range_succ,
      List.reverse_append, List.reverse_singleton, List.map_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, List.prod_append, List.map_map,
      List.map_reverse, List.reverse_reverse, Function.comp_def, r', s', r, s, l, e,
      Option.getD_some, mul_one, one_mul, mul_assoc]
  obtain ⟨b, hb, hinner⟩ := hcollapse N (le_refl N)
  have htotal : ∃ a : ℂ, a ≠ 0 ∧ transfer N D R KR KL κ θ =
      a • (((circuit (N + 1) S).reverse.map (fun | Gate.U j => j | Gate.K1 => 0 | Gate.KN => N + 1)).map A).prod := by
    rw [circuit_full_labels (N + 1) S (by omega)]
    rw [ht]
    by_cases hs : N + 1 ∈ S
    · have hθ : θ (e N) = -κ := by simp [θ, heval N (le_refl N), hs]
      have hend : s (e N) = g (-κ) • ((Equiv.prodComm _ _).toPEquiv.toMatrix) := by simp only [s, hθ, hreg]
      have hU : r (e N) = R κ (-κ) := by simp only [r, hθ]
      rw [hend, hU, lemma2 r' s' (KR κ) (KL κ) l (e N) (g (-κ)) (R κ (-κ)) hlnd hp]
      have heq : nearestWord (fun i => r' (some i)) (fun i => s' (some i)) (KR κ) l (e N) =
          b • (((((circuit (N + 1) S).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0))).map A).prod := by simpa only [r', s', Option.getD_some] using hinner
      rw [heq, mul_smul_comm, smul_smul]
      refine ⟨g (-κ) * b, mul_ne_zero hgminus hb, ?_⟩
      rw [circuit_step, if_pos hs, List.map_cons, List.prod_cons]
      congr 2
      simp [A, gate, helast]
    · have hθ : θ (e N) = κ := by simp [θ, heval N (le_refl N), hs]
      have hend : r (e N) = g κ • ((Equiv.prodComm _ _).toPEquiv.toMatrix) := by simp only [r, hθ, hreg]
      have hU : s (e N) = R κ (-κ) := by simp only [s, hθ]
      rw [hend, hU, lemma1 r' s' (KR κ) (KL κ) l (e N) (g κ) (R κ (-κ)) hlnd hp]
      have heq : nearestWord (fun i => r' (some i)) (fun i => s' (some i)) (KR κ) l (e N) =
          b • (((((circuit (N + 1) S).filter (· != Gate.KN)).reverse.map (fun | Gate.U j => j | _ => 0))).map A).prod := by simpa only [r', s', Option.getD_some] using hinner
      rw [heq, smul_mul_assoc, smul_smul]
      refine ⟨g κ * b, mul_ne_zero hgplus hb, ?_⟩
      rw [circuit_step, if_neg hs, List.map_append, List.prod_append,
        List.map_singleton, List.prod_singleton]
      congr 2
      simp [A, gate, helast]
  have hzero : A 0 = oneOp (e 0) (KR κ) := by simp [A, gate, hezero]
  have hleft : A (N + 1) = leftGate (KL κ) (e N) (R κ (-κ)) := by simp [A, gate, helast]
  have hbulk (i : ℕ) (hi : i < N) :
      A (i + 1) = twoOp (e i) (e (i + 1)) (checkedR (R κ (-κ))) := by
    simp [A, gate, ne_of_lt hi, e]
  have hsep : ∀ i ≤ N + 1, ∀ j ≤ N + 1, i + 2 ≤ j → Commute (A i) (A j) := by
    intro i hi j hj hfar
    cases i with
    | zero =>
      rw [hzero]
      by_cases hjend : j = N + 1
      · subst j; rw [hleft]
        exact left_comm_one (e 0) (e N) (hene 0 N (by omega) (by omega) (by omega)) _ _ _
      · cases j with
        | zero => omega
        | succ b =>
          rw [hbulk b (by omega)]
          exact one_two (e 0) (e b) (e (b + 1))
            (hene 0 b (by omega) (by omega) (by omega))
            (hene 0 (b + 1) (by omega) (by omega) (by omega)) _ _
    | succ a =>
      rw [hbulk a (by omega)]
      by_cases hjend : j = N + 1
      · subst j; rw [hleft]
        exact left_comm_two (e a) (e (a + 1)) (e N)
          (hene a N (by omega) (by omega) (by omega))
          (hene (a + 1) N (by omega) (by omega) (by omega)) _ _ _
      · cases j with
        | zero => omega
        | succ b =>
          rw [hbulk b (by omega)]
          exact two_two (e a) (e (a + 1)) (e b) (e (b + 1))
            (hene a b (by omega) (by omega) (by omega))
            (hene a (b + 1) (by omega) (by omega) (by omega))
            (hene (a + 1) b (by omega) (by omega) (by omega))
            (hene (a + 1) (b + 1) (by omega) (by omega) (by omega)) _ _
  have hcomm : ∀ i ≤ N + 1, ∀ j ≤ N + 1,
      i + 2 ≤ j ∨ j + 2 ≤ i → Commute (A i) (A j) := by
    intro i hi j hj h
    exact h.elim (hsep i hi j hj) (fun h => (hsep j hj i hi h).symm)
  have hword : circuitProduct N D R KR KL κ π = (((circuit (N + 1) S).reverse.map (fun | Gate.U j => j | Gate.K1 => 0 | Gate.KN => N + 1)).map A).prod := by
    rw [circuit_full_labels (N + 1) S (by omega)]
    simpa only [circuitProduct, w, List.map_ofFn, Function.comp_def] using
      trace_lemma A (N + 1) w hw hcomm
  obtain ⟨a, ha, htvalue⟩ := htotal
  have hidentity : circuitProduct N D R KR KL κ π = a⁻¹ • transfer N D R KR KL κ θ := by
    rw [hword, htvalue, smul_smul, inv_mul_cancel₀ ha, one_smul]
  refine ⟨θ, a⁻¹, ?_, inv_ne_zero ha, hidentity, ?_⟩
  · intro i; dsimp [θ]; split_ifs <;> simp
  · intro htcomm u
    rw [hidentity]
    change (a⁻¹ • transfer N D R KR KL κ θ) * transfer N D R KR KL u θ =
      transfer N D R KR KL u θ * (a⁻¹ • transfer N D R KR KL κ θ)
    rw [smul_mul_assoc, mul_smul_comm, (htcomm κ u).eq]

end D5.S3.Quantum.Dynamics.OpenIntegrableCircuitIntegrability
