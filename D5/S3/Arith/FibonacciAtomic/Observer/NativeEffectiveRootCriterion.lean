/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Effective attained root chart, complete-row target, finite coloring certificates, and stationary installation through NativeFullRootFeasibility. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveRootCriterion

open GenealogicalFiberTransport (Source substitution)
open ActualCutPartitionRecovery (LiteralRow CutSet CutPrefixFree canonicalRow rowAt holeAddresses)
open NativeCutFibers (Classes labels)
open NativeClassRootImage
open NativeClassRootPadding
open NativeClassRootSimulation (Chart RootTree rootRun rootDepth)
open NativeFullRootFeasibility
open NativeCutFibers (extend)
open ActualCutPartitionRecovery (evaluateRow)
open ActualTreeReadoutAcquisition (readout)
open NativeClassRootSimulation (nativeRun nativeDepth)
open NativeSerialMachine (Run answers)
open NativePassiveServiceRealization (Dialogue)

open NativeFiniteRootMinimax

private theorem chartList_complete (C : LiteralRow) (θ : Chart C) : θ ∈ chartList C :=
  (finite_root_minimax C []).2.2.2.2.1 θ

private theorem computedTarget_spec (C : LiteralRow) (θ : NativeCutFibers.Classes C → Option Bool) :
    computedTarget C θ = target C θ := (finite_root_minimax C []).2.2.2.2.2 θ

private theorem minimax_attains (C : LiteralRow) (fallback : LiteralRow) (W : List (TableRow C)) :
    (∀ row ∈ W, (rootRun row.type (minimaxTree C fallback W)).1 = row.target) ∧
      rootDepth (minimaxTree C fallback W) = minimaxValue C W :=
  (finite_root_minimax C W).2.1 fallback

private theorem minimax_lower_bound (C : LiteralRow) (W : List (TableRow C))
    (T : RootTree C LiteralRow)
    (correct : ∀ row ∈ W, (rootRun row.type T).1 = row.target) :
    minimaxValue C W ≤ rootDepth T := (finite_root_minimax C W).2.2.1 T correct

/-! A certificate is the exact finite coloring output.  Empty cells carry no
 depth obligation.  The target equation is retained for every chart row. -/

noncomputable instance chartFintype (C : LiteralRow) : Fintype (Chart C) :=
  Fintype.ofFinite _

noncomputable def colorCell {C : LiteralRow} {r : Nat} (c : Chart C → Fin r) (i : Fin r) :
    Finset (Chart C) := Finset.univ.filter (fun θ => c θ = i)

structure EffectiveCertificate (C : LiteralRow) (r q : Nat) where
  color : Chart C → Fin r
  tree : Fin r → RootTree C LiteralRow
  depth : ∀ i, (colorCell color i).Nonempty → rootDepth (tree i) ≤ q
  correct : ∀ θ, (rootRun θ.val (tree (color θ))).1 = computedTarget C θ.val

def EffectiveRootCriterion (C : LiteralRow) (r q : Nat) : Prop :=
  Nonempty (EffectiveCertificate C r q)

def coloredRows {C : LiteralRow} {r : Nat} (c : Chart C → Fin r) (i : Fin r) :
    List (TableRow C) :=
  (tableRows C).filter (fun row => c ⟨row.type,row.admissible⟩ = i)

private theorem tableRows_mem (C : LiteralRow) (θ : Chart C) :
    (⟨θ.val,θ.property,computedTarget C θ.val,rfl⟩ : TableRow C) ∈ tableRows C :=
  List.mem_map.mpr ⟨θ, chartList_complete C θ,rfl⟩

private theorem coloredRows_mem {C : LiteralRow} {r : Nat} (c : Chart C → Fin r)
    (θ : Chart C) :
    (⟨θ.val,θ.property,computedTarget C θ.val,rfl⟩ : TableRow C) ∈ coloredRows c (c θ) := by
  simp [coloredRows, tableRows_mem]

def colorings (C : LiteralRow) (r : Nat) : List (Chart C → Fin r) :=
  ((chartList C).pi (fun _ => List.finRange r)).map
    (fun f θ => f θ (chartList_complete C θ))

private theorem colorings_complete (C : LiteralRow) (r : Nat) (c : Chart C → Fin r) :
    c ∈ colorings C r := by
  apply List.mem_map.mpr
  refine ⟨fun θ _ => c θ, (List.mem_pi _ _).mpr (fun θ _ => by simp), rfl⟩

def colorPasses (C : LiteralRow) (r q : Nat) (c : Chart C → Fin r) : Bool :=
  (List.finRange r).all (fun i => (coloredRows c i).isEmpty ||
    decide (minimaxValue C (coloredRows c i) ≤ q))

private theorem colorPasses_spec {C : LiteralRow} {r q : Nat} (c : Chart C → Fin r) :
    colorPasses C r q c = true ↔
      ∀ i, coloredRows c i ≠ [] → minimaxValue C (coloredRows c i) ≤ q := by
  constructor
  · intro h i hi
    have ht := List.all_eq_true.mp h i (by simp)
    have ho : coloredRows c i = [] ∨ minimaxValue C (coloredRows c i) ≤ q := by
      simpa using ht
    exact ho.resolve_left hi
  · intro h
    apply List.all_eq_true.mpr
    intro i hi
    by_cases he : coloredRows c i = []
    · simp [he]
    · simp [he,h i he]

structure RootPackage (C : LiteralRow) (r : Nat) where
  color : Chart C → Fin r
  tree : Fin r → RootTree C LiteralRow

def packageFor (C : LiteralRow) (r : Nat) (c : Chart C → Fin r) : RootPackage C r :=
  { color := c, tree := fun i => minimaxTree C (.of (.inl true)) (coloredRows c i) }

/-- Finite input only: the nonempty actual-origin premise is absent from the program. -/
def decideNative (C : LiteralRow) (r q : Nat) : Option (RootPackage C r) :=
  ((colorings C r).find? (colorPasses C r q)).map (packageFor C r)

private theorem packageFor_correct {C : LiteralRow} {r q : Nat}
    (c : Chart C → Fin r) (h : colorPasses C r q c = true) :
    ∃ cert : EffectiveCertificate C r q,
      cert.color = (packageFor C r c).color ∧ cert.tree = (packageFor C r c).tree := by
  refine ⟨⟨c, (packageFor C r c).tree, ?_, ?_⟩, rfl,rfl⟩
  · intro i hi
    obtain ⟨θ,hθ⟩ := hi
    have hcθ : c θ = i := (Finset.mem_filter.mp hθ).2
    have hm := coloredRows_mem c θ
    rw [hcθ] at hm
    have hn : coloredRows c i ≠ [] := by intro he; rw [he] at hm; simp at hm
    change rootDepth (minimaxTree C (.of (.inl true)) (coloredRows c i)) ≤ q
    rw [(minimax_attains _ _ _).2]
    exact (colorPasses_spec c).mp h i hn
  · intro θ
    exact (minimax_attains C (.of (.inl true)) (coloredRows c (c θ))).1
      _ (coloredRows_mem c θ)

private theorem certificate_passes {C : LiteralRow} {r q : Nat}
    (cert : EffectiveCertificate C r q) : colorPasses C r q cert.color = true := by
  apply (colorPasses_spec _).mpr
  intro i hi
  obtain ⟨row, hr⟩ := List.exists_mem_of_ne_nil _ hi
  have hrc := (List.mem_filter.mp hr).2
  have hcolor : cert.color ⟨row.type,row.admissible⟩ = i := of_decide_eq_true hrc
  have hcell : (colorCell cert.color i).Nonempty := by
    refine ⟨⟨row.type,row.admissible⟩, ?_⟩
    simp [colorCell,hcolor]
  apply (minimax_lower_bound C (coloredRows cert.color i) (cert.tree i) ?_).trans
    (cert.depth i hcell)
  intro row hr
  have hr' := (List.mem_filter.mp hr).2
  have hi' : cert.color ⟨row.type,row.admissible⟩ = i := of_decide_eq_true hr'
  have hc := cert.correct ⟨row.type,row.admissible⟩
  simpa [hi', row.target_eq] using hc

private theorem effective_coloring_criterion (C : LiteralRow) (r q : Nat) :
    EffectiveRootCriterion C r q ↔
      ∃ c : Chart C → Fin r, ∀ i, coloredRows c i ≠ [] →
        minimaxValue C (coloredRows c i) ≤ q := by
  constructor
  · rintro ⟨cert⟩
    exact ⟨cert.color, (colorPasses_spec _).mp (certificate_passes cert)⟩
  · rintro ⟨c,hc⟩
    obtain ⟨cert,_,_⟩ := packageFor_correct c ((colorPasses_spec _).mpr hc)
    exact ⟨cert⟩

private theorem findColor_spec (C : LiteralRow) (r q : Nat) :
    ((colorings C r).find? (colorPasses C r q)).isSome = true ↔
      EffectiveRootCriterion C r q := by
  rw [List.find?_isSome]
  constructor
  · rintro ⟨c,hc,hp⟩
    obtain ⟨cert,_,_⟩ := packageFor_correct c hp
    exact ⟨cert⟩
  · rintro ⟨cert⟩
    exact ⟨cert.color,colorings_complete C r cert.color,certificate_passes cert⟩

private theorem decideNative_spec (C : LiteralRow) (r q : Nat) :
    (decideNative C r q).isSome = true ↔ EffectiveRootCriterion C r q := by
  simpa [decideNative] using findColor_spec C r q

private theorem effective_certificate_rootFeas
    (C : LiteralRow) (r q : Nat) (hr : 1 ≤ r)
    (h : EffectiveRootCriterion C r q) : RootFeas C r q := by
  rcases h with ⟨h⟩
  refine ⟨Fin r, inferInstance, h.color, h.tree, ?_, ?_, ?_⟩
  · simpa using hr
  · simpa using (Nat.le_refl r)
  · intro θ
    exact ⟨(h.correct θ).trans (computedTarget_spec C θ.val), h.depth (h.color θ) ⟨θ, by simp [colorCell]⟩⟩

private theorem rootFeas_effective_certificate
    (C : LiteralRow) (r q : Nat) (hr : 1 ≤ r)
    (h : RootFeas C r q) : EffectiveRootCriterion C r q := by
  classical
  rcases h with ⟨S, fs, c, E, hpos, hcap, hc⟩
  letI := fs
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let c' : Chart C → Fin r := fun θ =>
    ⟨(e (c θ)).val, by
      have hi := (e (c θ)).isLt
      exact lt_of_lt_of_le hi hcap⟩
  let tree' : Fin r → RootTree C LiteralRow := fun i =>
    if hi : ∃ s : S, (e s).val = i then E hi.choose else .stop (.of (.inl true))
  refine ⟨⟨c', tree', ?_, ?_⟩⟩
  · intro i hi
    obtain ⟨θ,hθ⟩ := hi
    have hci : c' θ = i := (Finset.mem_filter.mp hθ).2
    have hci' : (e (c θ)).val = i := by simpa [c'] using congrArg Fin.val hci
    have hs : ∃ s : S, (e s).val = i := ⟨c θ, hci'⟩
    have heq : hs.choose = c θ := by
      apply e.injective
      apply Fin.ext
      exact hs.choose_spec.trans hci'.symm
    have ht : tree' i = E (c θ) := by simp [tree', hs, heq]
    rw [ht]
    exact (hc θ).2
  · intro θ
    have hs : ∃ s : S, (e s).val = c' θ := ⟨c θ, by rfl⟩
    have heq : hs.choose = c θ := by
      apply e.injective
      apply Fin.ext
      exact hs.choose_spec
    have ht : tree' (c' θ) = E (c θ) := by simp [tree', hs, heq]
    rw [ht]
    simpa [computedTarget_spec] using (hc θ).1

private theorem effective_root_criterion_iff_rootFeas
    (C : LiteralRow) (r q : Nat) (hr : 1 ≤ r) :
    EffectiveRootCriterion C r q ↔ RootFeas C r q := by
  exact ⟨effective_certificate_rootFeas C r q hr,
    rootFeas_effective_certificate C r q hr⟩

/-! The complete same-r,q native result.  Its second equivalence is exactly
 the retained full-fiber theorem; acquisition, authentication, export, common
 entry, installation, and isolation remain supplied paid premises. -/

private theorem returned_certificate {C : LiteralRow} {r q : Nat}
    (pkg : RootPackage C r) (hp : decideNative C r q = some pkg) :
    ∃ cert : EffectiveCertificate C r q, cert.color = pkg.color ∧ cert.tree = pkg.tree := by
  unfold decideNative at hp
  cases hf : (colorings C r).find? (colorPasses C r q) with
  | none => simp [hf] at hp
  | some c =>
      have hc : colorPasses C r q c = true := List.find?_some hf
      have he : packageFor C r c = pkg := by simpa [hf] using hp
      simpa [he] using packageFor_correct c hc

/-- The whole original criterion, for a supplied complete row with nonempty actual image fiber. -/
theorem effective_native_birth_provenance
    (P : CutSet) (hP : CutPrefixFree P) (C : LiteralRow)
    (actual : Nonempty (OriginFiber P C)) (r q : Nat) (hr : 1 ≤ r) :
    ((decideNative C r q).isSome = true ↔ InvFeas P C r q) ∧
    (InvFeas P C r q ↔ ∃ c : Chart C → Fin r, ∀ i, coloredRows c i ≠ [] →
      minimaxValue C (coloredRows c i) ≤ q) := by
  obtain ⟨u₀,hu₀⟩ := actual
  have hv := native_full_root_feasibility P hP u₀ r q hr
  rw [hu₀] at hv
  have he := effective_root_criterion_iff_rootFeas C r q hr
  exact ⟨(decideNative_spec C r q).trans (he.trans hv.2.2.2.symm),
    (hv.2.2.2.trans he.symm).trans (effective_coloring_criterion C r q)⟩

private theorem actual_admissible (P : CutSet) (hP : CutPrefixFree P) (C : LiteralRow)
    (actual : Nonempty (OriginFiber P C)) (v : ImageValues C) : Admissible C (types C v.val.val) := by
  obtain ⟨u₀,hu₀⟩ := actual
  subst C
  exact actual_type P hP (substitution u₀) v

/-- All mathematical validity premises are proof arguments and erase at code generation.
The encoder's data arguments are the finite row, returned coloring, and acquired values. -/
def acquiredEncoder (P : CutSet) (hP : CutPrefixFree P) (C : LiteralRow)
    (actual : Nonempty (OriginFiber P C)) {r : Nat} (pkg : RootPackage C r)
    (v : ImageValues C) : Fin r :=
  pkg.color ⟨types C v.val.val, actual_admissible P hP C actual v⟩

/-- The selected package is installed at row-determined representative addresses. -/
def nativeEntry (C : LiteralRow) {r : Nat} (pkg : RootPackage C r)
    (i : Fin r) : Dialogue LiteralRow :=
  install C (.of (.inl true)) (pkg.tree i)

/-- Correctness of the particular returned encoder and stationary reader on every actual filling. -/
theorem returned_native_reader (P : CutSet) (hP : CutPrefixFree P)
    (C : LiteralRow) (actual : Nonempty (OriginFiber P C)) (r q : Nat) (hr : 1 ≤ r)
    (pkg : RootPackage C r) (hp : decideNative C r q = some pkg) :
    (Set.range (acquiredEncoder P hP C actual pkg)).Finite ∧
    (Set.range (acquiredEncoder P hP C actual pkg)).ncard ≤ r ∧
    ∀ (v : ImageValues C) (u : OriginFiber P C),
      substitution u.val = evaluateRow (extend C v.val.val) C →
      ∃ tr, Run controller (nativeEntry C pkg (acquiredEncoder P hP C actual pkg v))
          0 (substitution u.val) tr (canonicalRow P u.val) ∧
        Stationary tr ∧ (answers tr).length ≤ q := by
  classical
  obtain ⟨cert,hcolor,htrees⟩ := returned_certificate pkg hp
  have fiber := actual
  obtain ⟨u₀,hu₀⟩ := actual
  have full := native_full_root_feasibility P hP u₀ r q hr
  rw [hu₀] at full
  refine ⟨Set.toFinite _, ?_, ?_⟩
  · exact (Set.ncard_le_card _).trans (by simp)
  · intro v u image
    let θ : Chart C := ⟨types C v.val.val, actual_admissible P hP C fiber v⟩
    have budget : rootDepth (pkg.tree (pkg.color θ)) ≤ q := by
      rw [← hcolor, ← htrees]
      apply cert.depth
      exact ⟨θ, by simp [colorCell]⟩
    have output : (rootRun θ.val (pkg.tree (pkg.color θ))).1 = target C θ.val := by
      rw [← hcolor, ← htrees]
      exact (cert.correct θ).trans (computedTarget_spec C θ.val)
    have bridge := install_correct C (.of (.inl true)) (pkg.tree (pkg.color θ)) v.val.val
    have targetRow : target C θ.val = canonicalRow P u.val :=
      (full.1 v u image).2.2
    let entry := nativeEntry C pkg (acquiredEncoder P hP C fiber pkg v)
    have sim : nativeRun (fun a => readout a (substitution u.val)) entry =
        rootRun θ.val (pkg.tree (pkg.color θ)) := by
      simpa only [entry,nativeEntry,acquiredEncoder,θ,image] using bridge.1
    obtain ⟨tr,htr,hstationary,hcalls⟩ := dialogue_run entry (substitution u.val)
    refine ⟨tr, ?_, hstationary, ?_⟩
    · have he : (nativeRun (fun a => readout a (substitution u.val)) entry).1 =
          canonicalRow P u.val := (congrArg Prod.fst sim).trans (output.trans targetRow)
      simpa only [he] using htr
    · rw [hcalls]
      have hn := native_calls entry (substitution u.val)
      have depth : nativeDepth entry = rootDepth (pkg.tree (pkg.color θ)) := bridge.2
      exact hn.trans (depth ▸ budget)

#print axioms effective_native_birth_provenance
#print axioms returned_native_reader
end D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveRootCriterion
