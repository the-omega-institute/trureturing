/- GID: D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Nested right-comb compensation with literal raw routing and complete-leaf certification. -/

import D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum
import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale38NestedCompensation

open GenealogicalFiberTransport (Source substitution composition)
open ActualTreeReadoutAcquisition
open ActualJointResponseCostCore (Controller controllerPolicy controllerOutcome verifyController)
open ActualImageSevenLeafSeparation (thirdImage leafAddresses Nonconflict A C E)
open FourExitRawEndpointSpectrum (comb comb_slot_readout comb_tail_readout)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)
open scoped BigOperators ENNReal

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)
local notation "B" => FourExitRawEndpointSpectrum.B
local notation "H" => fun r : Nat => comb r (fun _ => A) C
local notation "h" => fun r : Nat => comb r (fun _ => FreeMagma.of true) (FreeMagma.of false)

/-- The baseline, the single enlarged slot, and the contracted left comb. -/
def family (k : Nat) : Index k → Source
  | .inl _ => .mul (H k) B
  | .inr (.inl j) => .mul (comb k (fun l => if l = j then B else A) C) A
  | .inr (.inr i) => .mul (H i.val) (.mul (H (k - i.val)) A)

/-- Complete ordered preimages, with the same root compensation position. -/
def preFamily (k : Nat) : Index k → Source
  | .inl _ => .mul (h k) E
  | .inr (.inl j) => .mul (comb k (fun l => if l = j then E else .of true) (.of false))
      (.of true)
  | .inr (.inr i) => .mul (h i.val) (.mul (h (k - i.val)) (.of true))

/-- Zero-based index: this is the literal address q_(t+1). -/
def query (t : Nat) : Address := false :: (List.replicate t true ++ [false,false,true])

/-- A branch and an absent report select different complete prototypes. -/
def choice (k t : Nat) (y : Reply) : Option (Index k) :=
  match y with
  | .branch => if ht : t < k then some (.inr (.inl ⟨t,ht⟩)) else none
  | .absent => if ht : 0 < t ∧ t ≤ k then
      some (.inr (.inr ⟨t-1,by omega⟩)) else none
  | _ => none

/-- Each selected prototype starts its complete labelled-leaf test. -/
noncomputable def scan (k : Nat) : List Nat → Controller
  | [] => verifyController (family k (.inl ())) (leaves (family k (.inl ())))
  | t :: ts => .query (query t) (fun y =>
      if y = .alpha then scan k ts else
        match choice k t y with
        | some i => verifyController (family k i) (leaves (family k i))
        | none => .fallback)

/-- The complete input-independent scan, with true same-address billing. -/
noncomputable def controller (k : Nat) : Controller := scan k (List.range (k+1))

/-- The first exceptional report position; the baseline scans every address. -/
def stop (k : Nat) : Index k → Nat
  | .inl _ => k
  | .inr (.inl j) => j.val
  | .inr (.inr i) => i.val + 1

/-- Prefix addresses only; no unreached suffix contributes to the bill. -/
def route (k : Nat) (i : Index k) : List Address :=
  (List.range (stop k i + 1)).map query

/-- The sole nonleaf routing address on each exceptional row. -/
def extra (k : Nat) (i : Index k) : Finset Address :=
  if i = .inl () then ∅ else {query (stop k i)}

/-- Compatibility with precisely the all-alpha routing prefix. -/
def compatible (k t : Nat) (i : Index k) : Prop :=
  ∀ s < t, readout (query s) (family k i) = .alpha

/-- Literal nested sources and their actual routing reports. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    Function.Injective (family k) ∧
    (∀ i : Index k, (∃! Q : Source, thirdImage Q = family k i) ∧
      thirdImage (preFamily k i) = family k i ∧
      composition (preFamily k i) = (k+1,2) ∧
      composition (family k i) = (k+5,2*k+8) ∧
      (family k i).length = 3*k+13 ∧ (leafAddresses (family k i)).card = 3*k+13) ∧
    Fintype.card (Index k) = 2*k+1 ∧
    (∀ i j : Index k, Nonconflict (family k i) (family k j)) ∧
    (∀ t ≤ k, readout (query t) (family k (.inl ())) = .alpha) ∧
    (∀ j : Fin k, (∀ t < j.val, readout (query t) (family k (.inr (.inl j))) = .alpha) ∧
      readout (query j.val) (family k (.inr (.inl j))) = .branch) ∧
    (∀ i : Fin k, (∀ t ≤ i.val, readout (query t) (family k (.inr (.inr i))) = .alpha) ∧
      readout (query (i.val+1)) (family k (.inr (.inr i))) = .absent) ∧
    (∀ t ≤ k+1, ∀ i : Index k,
      compatible k t i ↔ i = .inl () ∨ t ≤ stop k i) ∧
    (∃ pi : Strategy, pi.policy = controllerPolicy (controller k) ∧
      (∀ U : Source, terminal pi U = controllerOutcome (controller k) U) ∧
      (∀ i : Index k,
        controllerOutcome (controller k) (family k i) =
          ((route k i).map (fun q => ⟨q,readout q (family k i)⟩) ++
            (leaves (family k i)).map (fun q => ⟨q,readout q (family k i)⟩), true) ∧
        paid (terminal pi (family k i)).1 = leafAddresses (family k i) ∪ extra k i ∧
        cost pi (family k i) = 3*k+13 + if i = .inl () then 0 else 1) ∧
      (∀ i : Index k, i ≠ .inl () → query (stop k i) ∉ leafAddresses (family k i))) := by
  classical
  have hom (s t : Source) : thirdImage (.mul s t) = .mul (thirdImage s) (thirdImage t) :=
    Function.Semiconj₂.iterate
      (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
        substitution.map_mul) 3 s t
  have fold_image : ∀ (n : Nat) (f : Fin n → Source) (q : Source),
      thirdImage (comb n f q) = comb n (fun i => thirdImage (f i)) (thirdImage q) := by
    intro n
    induction n with
    | zero => intro f q; rfl
    | succ n ih => intro f q; rw [comb, hom, ih]; rfl
  have fold_comp : ∀ (n : Nat) (f : Fin n → Source) (q : Source),
      composition (comb n f q) = (∑ i, composition (f i)) + composition q := by
    intro n
    induction n with
    | zero => intro f q; simp [comb]
    | succ n ih =>
      intro f q
      simp only [comb, composition, ih, Fin.sum_univ_succ, add_assoc]
  have fold_len : ∀ (n : Nat) (f : Fin n → Source) (q : Source),
      (comb n f q).length = (∑ i, (f i).length) + q.length := by
    intro n
    induction n with
    | zero => intro f q; simp [comb]
    | succ n ih =>
      intro f q
      simp only [comb, FreeMagma.length, ih, Fin.sum_univ_succ, Nat.add_assoc]
  have images (i : Index k) : thirdImage (preFamily k i) = family k i := by
    cases i with
    | inl u => cases u; simp only [preFamily, family, hom, fold_image]; rfl
    | inr p =>
      cases p with
      | inl j =>
        simp only [preFamily, family, hom, fold_image]
        congr 2
        funext l
        split_ifs <;> rfl
      | inr i => simp only [preFamily, family, hom, fold_image]; rfl
  have precomp (i : Index k) : composition (preFamily k i) = (k+1,2) := by
    cases i with
    | inl u =>
      simp [preFamily, composition, fold_comp, E, Prod.ext_iff]
    | inr p =>
      cases p with
      | inl j =>
        have hs : (∑ l : Fin k, composition (if l = j then E else .of true)) =
            (k,1) := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
          have unchanged (l : Fin k) (hl : l ∈ (Finset.univ : Finset (Fin k)).erase j) :
              composition (if l = j then E else .of true) = (1,0) := by
            rw [if_neg (Finset.mem_erase.mp hl).1]; rfl
          rw [Finset.sum_congr rfl unchanged]
          simp [Finset.card_erase_of_mem (Finset.mem_univ j), E, composition, Prod.ext_iff]
          omega
        simp only [preFamily, composition, fold_comp, hs]
        rfl
      | inr i =>
        simp [preFamily, composition, fold_comp, Prod.ext_iff]
        omega
  have comp (i : Index k) : composition (family k i) = (k+5,2*k+8) := by
    have tr := (GenealogicalFiberTransport.fiberMap (k+1,2) 3
      ⟨preFamily k i,precomp i⟩).property
    change composition (thirdImage (preFamily k i)) = _ at tr
    rw [images] at tr
    simp only [GraftAffineClosure.step, Function.iterate_succ_apply', Function.iterate_zero_apply] at tr
    convert tr using 1 <;> ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  have comp_length (U : Source) : (composition U).1 + (composition U).2 = U.length := by
    induction U with
    | of b => cases b <;> rfl
    | mul s t hs ht =>
      simp only [composition, Prod.fst_add, Prod.snd_add, FreeMagma.length]
      omega
  have size (i : Index k) : (family k i).length = 3*k+13 := by
    have hc := comp_length (family k i)
    rw [comp] at hc
    omega
  have raw_H (n t : Nat) (ht : t ≤ n) :
      readout (List.replicate t true ++ [false,false,true]) (H n) = .alpha := by
    by_cases hlt : t < n
    · have hs := comb_slot_readout n (fun _ => A) C ⟨t,hlt⟩ [false,true]
      simpa only [Fin.val_mk] using hs.trans (show readout [false,true] A = .alpha from rfl)
    · have he : t = n := by omega
      subst t
      exact (comb_tail_readout n (fun _ => A) C [false,false,true]).trans rfl
  have raw_base (t : Nat) (ht : t ≤ k) :
      readout (query t) (family k (.inl ())) = .alpha := raw_H k t ht
  have raw_X (j : Fin k) :
      (∀ t < j.val, readout (query t) (family k (.inr (.inl j))) = .alpha) ∧
      readout (query j.val) (family k (.inr (.inl j))) = .branch := by
    constructor
    · intro t ht
      have hs := comb_slot_readout k (fun l => if l = j then B else A) C
        ⟨t,lt_trans ht j.isLt⟩ [false,true]
      have hn : (⟨t,lt_trans ht j.isLt⟩ : Fin k) ≠ j := by intro he; have hh : t = j.val := congrArg Fin.val he; omega
      rw [if_neg hn] at hs
      simpa only [family, query, readout, Fin.val_mk] using hs.trans (show readout [false,true] A = .alpha from rfl)
    · have hs := comb_slot_readout k (fun l => if l = j then B else A) C j [false,true]
      simp only [ite_true] at hs
      simpa only [family, query, readout] using hs.trans (show readout [false,true] B = .branch from rfl)
  have raw_Y (i : Fin k) :
      (∀ t ≤ i.val, readout (query t) (family k (.inr (.inr i))) = .alpha) ∧
      readout (query (i.val+1)) (family k (.inr (.inr i))) = .absent := by
    refine ⟨fun t ht => raw_H i.val t ht, ?_⟩
    have hs := comb_tail_readout i.val (fun _ => A) C [true,false,false,true]
    change readout (List.replicate (i.val+1) true ++ [false,false,true]) (H i.val) = .absent
    rw [List.replicate_add]
    simpa only [List.replicate_one, List.append_assoc, List.singleton_append] using
      hs.trans (show readout [true,false,false,true] C = .absent from rfl)
  have block_lengths : A.length = 3 ∧ (B).length = 8 ∧ C.length = 5 := ⟨rfl,rfl,rfl⟩
  have injective : Function.Injective (family k) := by
    have left_size : ∀ i : Index k,
        (match family k i with | .of _ => 0 | .mul l _ => l.length) =
          (match i with
            | .inl _ => 3*k+5
            | .inr (.inl _) => 3*k+10
            | .inr (.inr i) => 3*i.val+5) := by
      intro i
      cases i with
      | inl u => simp [family, fold_len, block_lengths.1, block_lengths.2.2, Nat.mul_comm]
      | inr p =>
        cases p with
        | inl j =>
          simp only [family]
          rw [fold_len, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
          have unchanged (l : Fin k) (hl : l ∈ (Finset.univ : Finset (Fin k)).erase j) :
              (if l = j then B else A).length = 3 := by
            rw [if_neg (Finset.mem_erase.mp hl).1]; rfl
          rw [Finset.sum_congr rfl unchanged]
          simp [Finset.card_erase_of_mem (Finset.mem_univ j), block_lengths.2.1, block_lengths.2.2]
          omega
        | inr i => simp [family, fold_len, block_lengths.1, block_lengths.2.2, Nat.mul_comm]
    intro i j he
    have hl := congrArg (fun U : Source => match U with | .of _ => 0 | .mul l _ => l.length) he
    rw [left_size, left_size] at hl
    cases i with
    | inl u => cases j with
      | inl v => congr
      | inr p => cases p <;> dsimp at hl <;> have hlt := ‹Fin k›.isLt <;> omega
    | inr p => cases j with
      | inl u => cases p <;> dsimp at hl <;> have hlt := ‹Fin k›.isLt <;> omega
      | inr q =>
        cases p with
        | inl a => cases q with
          | inr b => dsimp at hl; have := b.isLt; omega
          | inl b =>
            by_cases same : a = b
            · subst b; rfl
            · have reads := congrArg (readout (query (min a.val b.val))) he
              rcases lt_or_gt_of_ne (Fin.val_ne_of_ne same) with hab | hba
              · rw [min_eq_left (le_of_lt hab), (raw_X a).2, (raw_X b).1 _ hab] at reads
                contradiction
              · rw [min_eq_right (le_of_lt hba), (raw_X a).1 _ hba, (raw_X b).2] at reads
                contradiction
        | inr a => cases q with
          | inl b => dsimp at hl; have := a.isLt; omega
          | inr b => have hv : a = b := Fin.ext (by dsimp at hl; omega); subst b; rfl
  have symmetric (P Q : Source) (hn : Nonconflict P Q) : Nonconflict Q P :=
    (ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 Q P).2.2.mpr
      (fun u a b ha hb => ((ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 P Q).2.2.mp hn u b a hb ha).symm)
  have E_comb : ∀ (n : Nat) (f : Fin n → Source), (∀ i, f i = A ∨ f i = B) →
      Nonconflict E (comb n f C) := by
    intro n f hf
    cases n with
    | zero => trivial
    | succ n =>
      change Nonconflict (.of false) (f 0) ∧
        Nonconflict (.of true) (comb n (fun i => f i.succ) C)
      constructor
      · rcases hf 0 with h0 | h0 <;> rw [h0] <;> trivial
      · cases n <;> trivial
  have C_comb : ∀ (n : Nat) (f : Fin n → Source), (∀ i, f i = A ∨ f i = B) →
      Nonconflict C (comb n f C) := by
    intro n f hf
    cases n with
    | zero => simp [A,C,E,Nonconflict,show B = .mul C A from rfl]
    | succ n =>
      change Nonconflict A (f 0) ∧ Nonconflict E (comb n (fun i => f i.succ) C)
      refine ⟨?_, E_comb n _ (fun i => hf i.succ)⟩
      rcases hf 0 with h0 | h0 <;> rw [h0] <;> simp [A,C,E,Nonconflict,show B = .mul C A from rfl]
  have comb_nc : ∀ (n m : Nat) (f : Fin n → Source) (g : Fin m → Source),
      (∀ i, f i = A ∨ f i = B) → (∀ i, g i = A ∨ g i = B) →
      Nonconflict (comb n f C) (comb m g C) := by
    intro n
    induction n with
    | zero => intro m f g hf hg; exact C_comb m g hg
    | succ n ih =>
      intro m f g hf hg
      cases m with
      | zero => exact symmetric _ _ (C_comb (n+1) f hf)
      | succ m =>
        refine ⟨?_, ih m _ _ (fun i => hf i.succ) (fun i => hg i.succ)⟩
        rcases hf 0 with ha | ha <;> rcases hg 0 with hb | hb <;> rw [ha,hb] <;> simp [A,C,E,Nonconflict,show B = .mul C A from rfl]
  have A_N (n : Nat) : Nonconflict A (.mul (H n) A) := by
    change Nonconflict E (H n) ∧ True
    exact ⟨E_comb n _ (fun _ => Or.inl rfl), trivial⟩
  have nc (i j : Index k) : Nonconflict (family k i) (family k j) := by
    have hnc (n m : Nat) : Nonconflict (H n) (H m) :=
      comb_nc n m _ _ (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)
    have mixed (n : Nat) (j : Fin k) :
        Nonconflict (H n) (comb k (fun l => if l = j then B else A) C) :=
      comb_nc n k _ _ (fun _ => Or.inl rfl) (fun l => by split_ifs <;> simp)
    have xx (i j : Fin k) : Nonconflict
        (comb k (fun l => if l = i then B else A) C)
        (comb k (fun l => if l = j then B else A) C) :=
      comb_nc k k _ _ (fun l => by split_ifs <;> simp) (fun l => by split_ifs <;> simp)
    have bn (n : Nat) : Nonconflict B (.mul (H n) A) := by
      change Nonconflict C (H n) ∧ Nonconflict A A
      exact ⟨C_comb n _ (fun _ => Or.inl rfl), by simp [A,C,E,Nonconflict,show B = .mul C A from rfl]⟩
    cases i with
    | inl u => cases j with
      | inl v => exact ⟨hnc k k, by simp [A,C,E,Nonconflict,show B = .mul C A from rfl]⟩
      | inr q => cases q with
        | inl j => exact ⟨mixed k j, symmetric _ _ (A_N 0)⟩
        | inr j => exact ⟨hnc k j.val, bn (k-j.val)⟩
    | inr p => cases p with
      | inl i => cases j with
        | inl u => exact ⟨symmetric _ _ (mixed k i), A_N 0⟩
        | inr q => cases q with
          | inl j => exact ⟨xx i j, by simp [A,C,E,Nonconflict,show B = .mul C A from rfl]⟩
          | inr j => exact ⟨symmetric _ _ (mixed j.val i), A_N (k-j.val)⟩
      | inr i => cases j with
        | inl u => exact ⟨hnc i.val k, symmetric _ _ (bn (k-i.val))⟩
        | inr q => cases q with
          | inl j => exact ⟨mixed i.val j, symmetric _ _ (A_N (k-i.val))⟩
          | inr j => exact ⟨hnc i.val j.val, hnc (k-i.val) (k-j.val), by simp [A,C,E,Nonconflict,show B = .mul C A from rfl]⟩
  have rho_inj : Function.Injective thirdImage := by
    exact (SourceTransportCentralizer.source_transport_centralizer.2.2.1 substitution
      ⟨substitution.map_mul, fun _ => rfl⟩).iterate 3
  have positive (i : Index k) : Positive (family k i) := ⟨preFamily k i, images i⟩
  have survivors (t : Nat) (ht : t ≤ k+1) (i : Index k) :
      compatible k t i ↔ i = .inl () ∨ t ≤ stop k i := by
    cases i with
    | inl u =>
      cases u
      simp only [or_true, true_or, iff_true]
      intro s hs
      exact raw_base s (by omega)
    | inr p =>
      cases p with
      | inl j =>
        simp only [Sum.inr_ne_inl, false_or, stop]
        constructor
        · intro h
          by_contra hn
          have hh := h j.val (by omega)
          rw [(raw_X j).2] at hh
          contradiction
        · intro h s hs; exact (raw_X j).1 s (by omega)
      | inr i =>
        simp only [Sum.inr_ne_inl, false_or, stop]
        constructor
        · intro h
          by_contra hn
          have hh := h (i.val+1) (by omega)
          rw [(raw_Y i).2] at hh
          contradiction
        · intro h s hs; exact (raw_Y i).1 s (by omega)
  have correct_scan (ts : List Nat) (U : Source) :
      (controllerOutcome (scan k ts) U).2 = true ↔ Positive U := by
    induction ts with
    | nil => exact ActualJointResponseCostCore.phase_foundation.2.1 _ (positive (.inl ())) U
    | cons t ts ih =>
      by_cases hy : readout (query t) U = .alpha
      · simpa only [scan, controllerOutcome, hy, ↓reduceIte] using ih
      · simp only [scan, controllerOutcome, hy, ↓reduceIte]
        cases choice k t (readout (query t) U) with
        | none => exact acquisition_foundation.1 U
        | some i => exact ActualJointResponseCostCore.phase_foundation.2.1 _ (positive i) U
  have scan_prefix (qs ts : List Nat) (U : Source)
      (ha : ∀ t ∈ qs, readout (query t) U = .alpha) :
      controllerOutcome (scan k (qs ++ ts)) U =
        ((qs.map (fun t => ⟨query t,readout (query t) U⟩)) ++
          (controllerOutcome (scan k ts) U).1, (controllerOutcome (scan k ts) U).2) := by
    induction qs with
    | nil => rfl
    | cons t qs ih =>
      have ht := ha t (List.mem_cons_self)
      have rest := ih (fun s hs => ha s (List.mem_cons_of_mem _ hs))
      simp only [List.cons_append, scan, controllerOutcome, ht, ↓reduceIte, rest,
        List.map_cons, List.cons_append]
  have divide (t : Nat) (ht : t ≤ k) :
      List.range (k+1) = List.range t ++ t :: List.range' (t+1) (k-t) := by
    rw [List.range_eq_range', ← show t + (k-t+1) = k+1 by omega,
      ← List.range'_append_1]
    simp only [Nat.zero_add, List.range'_succ, Nat.add_zero, Nat.add_one]
    rw [← List.range_eq_range']
  have outcomes (i : Index k) :
      controllerOutcome (controller k) (family k i) =
        ((route k i).map (fun q => ⟨q,readout q (family k i)⟩) ++
          (leaves (family k i)).map (fun q => ⟨q,readout q (family k i)⟩), true) := by
    cases i with
    | inl u =>
      cases u
      have hp := scan_prefix (List.range (k+1)) [] (family k (.inl ()))
        (fun t ht => raw_base t (by have := List.mem_range.mp ht; omega))
      simp only [List.append_nil] at hp
      rw [controller, hp, scan, ActualJointResponseCostCore.phase_foundation.2.2.1]
      rfl
    | inr p =>
      cases p with
      | inl j =>
        rw [controller, divide j.val (le_of_lt j.isLt),
          scan_prefix _ _ _ (fun t ht => (raw_X j).1 t (List.mem_range.mp ht))]
        simp only [scan, controllerOutcome, (raw_X j).2, Reply.noConfusion,
          ↓reduceIte, choice, dif_pos j.isLt,
          ActualJointResponseCostCore.phase_foundation.2.2.1, route, stop,
          List.range_succ, List.map_append, List.map_cons, List.map_nil,
          List.singleton_append, List.map_map, Function.comp_def, List.append_assoc]
      | inr i =>
        have hi : 0 < i.val+1 ∧ i.val+1 ≤ k := ⟨by omega, by have := i.isLt; omega⟩
        rw [controller, divide (i.val+1) hi.2,
          scan_prefix _ _ _ (fun t ht => (raw_Y i).1 t (by have := List.mem_range.mp ht; omega))]
        have he : (⟨i.val+1-1,by omega⟩ : Fin k) = i := Fin.ext (by omega)
        simp only [scan, controllerOutcome, (raw_Y i).2, Reply.noConfusion,
          ↓reduceIte, choice, dif_pos hi, he,
          ActualJointResponseCostCore.phase_foundation.2.2.1, route, stop,
          List.range_succ, List.map_append, List.map_cons, List.map_nil,
          List.singleton_append, List.map_map, Function.comp_def, List.append_assoc]
  let pi : Strategy := {
    policy := controllerPolicy (controller k)
    correct := fun U => ⟨(controllerOutcome (controller k) U).1.length+1,
      controllerOutcome (controller k) U,
      ActualJointResponseCostCore.phase_foundation.1 _ U,
      correct_scan (List.range (k+1)) U⟩ }
  have terminal_outcome (U : Source) : terminal pi U = controllerOutcome (controller k) U := by
    have ht := (Classical.choose_spec (Classical.choose_spec (pi.correct U))).1
    exact source_foundation.2.2.2.2.2.2.2 pi.policy _ _ [] U _ _ ht
      (ActualJointResponseCostCore.phase_foundation.1 _ U)
  have leaf_mem (U : Source) (q : Address) :
      q ∈ leafAddresses U ↔ readout q U = .alpha ∨ readout q U = .beta := by
    rw [(ActualImageSevenLeafSeparation.seven_leaf_separation.1 U).2 q]
    cases hy : readout q U <;> simp [ActualImageSevenLeafSeparation.leafLabel,hy]
  have before_leaf (i : Index k) (t : Nat) (ht : t < stop k i) :
      query t ∈ leafAddresses (family k i) := by
    apply (leaf_mem _ _).mpr
    left
    cases i with
    | inl u => cases u; exact raw_base t (by simpa only [stop] using le_of_lt ht)
    | inr p => cases p with
      | inl j => exact (raw_X j).1 t ht
      | inr i => exact (raw_Y i).1 t (by simpa only [stop, Nat.lt_succ_iff] using ht)
  have extra_out (i : Index k) (hi : i ≠ .inl ()) :
      query (stop k i) ∉ leafAddresses (family k i) := by
    rw [leaf_mem]
    cases i with
    | inl u => cases u; exact False.elim (hi rfl)
    | inr p => cases p with
      | inl j => simp only [stop, (raw_X j).2]; simp
      | inr i => simp only [stop, (raw_Y i).2]; simp
  have bill (i : Index k) : paid (terminal pi (family k i)).1 =
      leafAddresses (family k i) ∪ extra k i := by
    rw [terminal_outcome, outcomes]
    simp only [paid, List.map_append, List.toFinset_append, List.map_map, Function.comp_def]
    change (route k i).toFinset ∪ leafAddresses (family k i) = _
    apply Finset.Subset.antisymm
    · intro q hq
      rcases Finset.mem_union.mp hq with hr | hl
      · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
        have bound : t ≤ stop k i := by have := List.mem_range.mp ht; omega
        by_cases hb : i = .inl ()
        · subst i
          exact Finset.mem_union_left _ ((leaf_mem _ _).mpr (Or.inl (raw_base t bound)))
        · by_cases hs : t < stop k i
          · exact Finset.mem_union_left _ (before_leaf i t hs)
          · have he : t = stop k i := by omega
            subst t
            exact Finset.mem_union_right _ (by simp [extra,hb])
      · exact Finset.mem_union_left _ hl
    · intro q hq
      rcases Finset.mem_union.mp hq with hl | he
      · exact Finset.mem_union_right _ hl
      · by_cases hb : i = .inl ()
        · simp [extra,hb] at he
        · have hq : q = query (stop k i) := by simpa [extra,hb] using he
          subst q
          apply Finset.mem_union_left
          apply List.mem_toFinset.mpr
          exact List.mem_map.mpr ⟨stop k i, List.mem_range.mpr (by omega), rfl⟩
  have costs (i : Index k) : cost pi (family k i) =
      3*k+13 + if i = .inl () then 0 else 1 := by
    change (paid (terminal pi (family k i)).1).card = _
    rw [bill]
    have disjoint : Disjoint (leafAddresses (family k i)) (extra k i) := by
      by_cases hb : i = .inl ()
      · simp [extra,hb]
      · simpa [extra,hb] using extra_out i hb
    rw [Finset.card_union_of_disjoint disjoint,
      (ActualImageSevenLeafSeparation.seven_leaf_separation.1 _).1, size]
    by_cases hb : i = .inl () <;> simp [extra,hb]
  refine ⟨injective, ?_, ?_, nc, raw_base, raw_X, raw_Y, survivors, ?_⟩
  · intro i
    refine ⟨⟨preFamily k i, images i, fun Q hQ => rho_inj (hQ.trans (images i).symm)⟩,
      images i, precomp i, comp i, size i, ?_⟩
    exact (ActualImageSevenLeafSeparation.seven_leaf_separation.1 _).1.trans (size i)
  · simp [Fintype.card_sum]; omega
  · exact ⟨pi, rfl, terminal_outcome, fun i => ⟨outcomes i, bill i, costs i⟩, extra_out⟩

end D5.S3.Arith.FibonacciAtomic.Scale38NestedCompensation
