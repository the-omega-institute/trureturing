/- GID: D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fixed scalar source fibers and sharp deterministic discovery costs. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
import D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FixedScalarFiberDiscovery

open GenealogicalFiberTransport (Source substitution composition Fiber)
open ActualTreeReadoutAcquisition (Address Reply readout leaves flip Positive Policy paid extendedCost)
open ActualImageAddressCertificate (ActualImage Within Sound alphaAddresses)
open ActualImageSevenLeafSeparation (leafAddresses)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)
open scoped ENNReal

/-- The entire scalar fiber, without a composition or source-image promise. -/
def scalarFiber (L : ℕ) : Set Source :=
  {U | PrimeGcdHorizon.observation (3 * L) (composition U).1 (composition U).2 =
    PrimeGcdHorizon.observation (3 * L) 3 5}

/-- The two ordered third images use the existing literal alpha and beta blocks. -/
def P : Source := .mul ActualImageSevenLeafSeparation.A ActualImageSevenLeafSeparation.C
def Q : Source := .mul ActualImageSevenLeafSeparation.C ActualImageSevenLeafSeparation.A

/-- The optimal certificate size on a positive input. -/
def certificateSize (L : ℕ) : ℕ := if L = 0 then 5 else 3

/-- Correctness and finite termination are required only on the entire fixed fiber. -/
def CorrectOn (L : ℕ) (policy : Policy) : Prop :=
  ∀ U ∈ scalarFiber L, ∃ fuel hb,
    execute readout policy fuel [] U = some hb ∧ (hb.2 = true ↔ Positive U)

/-- Every address in a terminating run on a fiber input obeys the window. -/
def WindowOn (L h : ℕ) (policy : Policy) : Prop :=
  ∀ U ∈ scalarFiber L, ∀ fuel hb,
    execute readout policy fuel [] U = some hb → Within h (paid hb.1)

/-- Repeated reports are excluded on actual terminating paths. -/
def NoRepeatOn (L : ℕ) (policy : Policy) : Prop :=
  ∀ U ∈ scalarFiber L, ∀ fuel hb,
    execute readout policy fuel [] U = some hb → (hb.1.map Sigma.fst).Nodup

/-- The infimum is over the frozen history-only policies, and infinity charges divergence. -/
noncomputable def discoveryCost (L h : ℕ) : ℝ≥0∞ :=
  ⨅ policy : Policy, ⨅ (_ : CorrectOn L policy ∧ WindowOn L h policy),
    ⨆ U : scalarFiber L, extendedCost policy U.val


/-- The unique minimum positive certificate on the fixed scalar fiber. -/
def certificate (L : ℕ) (V : Source) : Finset Address :=
  if L = 0 then (leafAddresses V).filter (fun u => readout u V = .beta)
  else alphaAddresses V

/-- A certificate is sound against every complete source in the fixed scalar fiber. -/
def FiberSound (L : ℕ) (V : Source) (J : Finset Address) : Prop :=
  ∀ U ∈ scalarFiber L, (∀ u ∈ J, readout u U = readout u V) → Positive U

/-- A finite endpoint test, with all nonmatching replies rejected immediately. -/
def testNext (label : Reply) : List Address → Hist (fun _ : Address => Reply) → Sum Address Bool
  | [], [] => .inr true
  | [], _ :: _ => .inr false
  | u :: _, [] => .inl u
  | u :: us, p :: ps =>
      if p.1 = u ∧ p.2 = label then testNext label us ps else .inr false

/-- The four-response tables, with each remaining test in left-right lexicographic order. -/
def strategy (L : ℕ) (favorP : Bool) (history : Hist (fun _ : Address => Reply)) :
    Sum Address Bool :=
  let first : Address :=
    if L = 0 then (if favorP then [false,true] else [true,true])
    else (if favorP then [false,false,true] else [true,false,true])
  match history with
  | [] => .inl first
  | p :: rest =>
    if p.1 ≠ first then .inr false else
    if L = 0 then
      if favorP then
        match p.2 with
        | .beta => testNext .beta [[false,false,false],[true,false,false,false],
            [true,false,true],[true,true,false]] rest
        | .branch => testNext .beta [[false,false,false,false],[false,false,true],
            [false,true,false],[true,false,false],[true,true]] rest
        | .alpha | .absent => .inr false
      else
        match p.2 with
        | .beta => testNext .beta [[false,false,false,false],[false,false,true],
            [false,true,false],[true,false,false]] rest
        | .branch => testNext .beta [[false,false,false],[false,true],
            [true,false,false,false],[true,false,true],[true,true,false]] rest
        | .alpha | .absent => .inr false
    else
      if favorP then
        match p.2 with
        | .alpha => testNext .alpha [[true,false,false,true],[true,true,true]] rest
        | .beta => testNext .alpha [[false,false,false,true],[false,true,true],[true,false,true]] rest
        | .branch | .absent => .inr false
      else
        match p.2 with
        | .alpha => testNext .alpha [[false,false,false,true],[false,true,true]] rest
        | .beta => testNext .alpha [[false,false,true],[true,false,false,true],[true,true,true]] rest
        | .branch | .absent => .inr false

/-- Classification of the entire scalar fiber and exact deterministic discovery cost. -/
theorem result (L h : ℕ) :
    (scalarFiber L).Finite ∧
    Set.image composition (scalarFiber L) =
      (if L = 0 then {(0,7),(3,5),(6,3),(9,1)} else {(3,5)}) ∧
    scalarFiber L ∩ ActualImage 3 = {P,Q} ∧ P ≠ Q ∧
    P = substitution^[3] (.mul (.of true) (.of false)) ∧
    Q = substitution^[3] (.mul (.of false) (.of true)) ∧
    (h < 4 → ¬ ∃ policy : Policy, CorrectOn L policy ∧ WindowOn L h policy) ∧
    (4 ≤ h →
      (∀ policy : Policy, CorrectOn L policy → WindowOn L h policy →
        (certificateSize L : ℝ≥0∞) ≤ extendedCost policy P ∧
        (certificateSize L : ℝ≥0∞) ≤ extendedCost policy Q ∧
        ((2 * certificateSize L + 1 : ℕ) : ℝ≥0∞) ≤
          extendedCost policy P + extendedCost policy Q) ∧
      CorrectOn L (strategy L true) ∧ CorrectOn L (strategy L false) ∧
      WindowOn L 4 (strategy L true) ∧ WindowOn L 4 (strategy L false) ∧
      NoRepeatOn L (strategy L true) ∧ NoRepeatOn L (strategy L false) ∧
      (∀ U ∈ scalarFiber L,
        extendedCost (strategy L true) U ≤ ((certificateSize L + 1 : ℕ) : ℝ≥0∞) ∧
        extendedCost (strategy L false) U ≤ ((certificateSize L + 1 : ℕ) : ℝ≥0∞)) ∧
      extendedCost (strategy L true) P = (certificateSize L : ℝ≥0∞) ∧
      extendedCost (strategy L true) Q = ((certificateSize L + 1 : ℕ) : ℝ≥0∞) ∧
      extendedCost (strategy L false) P = ((certificateSize L + 1 : ℕ) : ℝ≥0∞) ∧
      extendedCost (strategy L false) Q = (certificateSize L : ℝ≥0∞)) ∧
    discoveryCost L h = (if h < 4 then ∞ else if L = 0 then 6 else 4) := by
  classical
  have scalar : ∀ a b : ℕ,
      PrimeGcdHorizon.observation (3 * L) a b = PrimeGcdHorizon.observation (3 * L) 3 5 ↔
        if L = 0 then (a,b) ∈ ({(0,7),(3,5),(6,3),(9,1)} : Finset (ℕ × ℕ))
        else (a,b) = (3,5) := by
    classical
    by_cases hL : L = 0
    · subst L
      intro a b
      change 2 * a + 3 * b = 21 ↔
        (a,b) ∈ ({(0,7),(3,5),(6,3),(9,1)} : Finset (ℕ × ℕ))
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      omega
    · let f := Nat.fib (3 * L + 3)
      let g := Nat.fib (3 * L + 4)
      have hf : 8 ≤ f := by
        exact (by norm_num : 8 = Nat.fib 6).le.trans (Nat.fib_mono (by omega))
      have hfg : f < g := by
        dsimp only [f,g]
        exact Nat.fib_lt_fib_succ (by omega)
      have cop : IsCoprime (f : ℤ) (g : ℤ) :=
        (Nat.fib_coprime_fib_succ (3 * L + 3)).isCoprime
      intro a b
      simp only [if_neg hL]
      constructor
      · intro he
        change f * a + g * b = f * 3 + g * 5 at he
        have hb : b < 8 := by nlinarith [Nat.zero_le (f * a)]
        have hz : (g : ℤ) * ((b : ℤ) - 5) = (f : ℤ) * (3 - (a : ℤ)) := by
          have he' : (f : ℤ) * a + (g : ℤ) * b = (f : ℤ) * 3 + (g : ℤ) * 5 := by
            exact_mod_cast he
          linarith
        have hd : (f : ℤ) ∣ (b : ℤ) - 5 :=
          cop.dvd_of_dvd_mul_left (hz ▸ dvd_mul_right (f : ℤ) (3 - (a : ℤ)))
        have hb5 : b = 5 := by
          have he0 := Int.eq_zero_of_abs_lt_dvd hd (by
            rw [abs_lt]
            constructor <;> omega)
          omega
        subst b
        have ha3 : a = 3 := by nlinarith
        exact Prod.ext ha3 rfl
      · intro he
        have ha : a = 3 := congrArg Prod.fst he
        have hb : b = 5 := congrArg Prod.snd he
        subst a; subst b; rfl
  have positive_count (t : Source) : 0 < (composition t).1 + (composition t).2 := by
    induction t with
    | of b => cases b <;> decide
    | mul s t hs ht =>
      simp only [composition, Prod.fst_add, Prod.snd_add]
      omega
  have single (t : Source) (ht : (composition t).1 + (composition t).2 = 1) :
      ∃ b : Bool, t = .of b := by
    cases t with
    | of b => exact ⟨b,rfl⟩
    | mul s t =>
      have hs := positive_count s
      have ht' := positive_count t
      simp only [composition, Prod.fst_add, Prod.snd_add] at ht
      omega
  have two (t : Source) (ht : composition t = (1,1)) :
      t = .mul (.of true) (.of false) ∨ t = .mul (.of false) (.of true) := by
    cases t with
    | of b => cases b <;> simp [composition] at ht
    | mul s t =>
      have hs := positive_count s
      have ht' := positive_count t
      have ha := congrArg Prod.fst ht
      have hb := congrArg Prod.snd ht
      simp only [composition, Prod.fst_add, Prod.snd_add] at ha hb
      obtain ⟨b,rfl⟩ := single s (by omega)
      obtain ⟨c,rfl⟩ := single t (by omega)
      cases b <;> cases c <;> simp_all [composition]
  have cp : composition P = (3,5) := rfl
  have cq : composition Q = (3,5) := rfl
  have pp : P = substitution^[3] (.mul (.of true) (.of false)) := rfl
  have pq : Q = substitution^[3] (.mul (.of false) (.of true)) := rfl
  have memP : P ∈ scalarFiber L := by simp [scalarFiber, cp]
  have memQ : Q ∈ scalarFiber L := by simp [scalarFiber, cq]
  have classification : ∀ U ∈ scalarFiber L, Positive U ↔ U = P ∨ U = Q := by
    intro U hU
    constructor
    · rintro ⟨T,rfl⟩
      have ht := (GenealogicalFiberTransport.fiberMap (composition T) 3 ⟨T,rfl⟩).property
      change composition (substitution^[3] T) = GraftAffineClosure.step^[3] (composition T) at ht
      have hc := (scalar _ _).mp hU
      rw [ht] at hc
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
        GraftAffineClosure.step] at hc
      have hT : composition T = (1,1) := by
        by_cases hL : L = 0
        · rw [if_pos hL] at hc
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hc
          apply Prod.ext <;> omega
        · rw [if_neg hL] at hc
          have ha := congrArg Prod.fst hc
          have hb := congrArg Prod.snd hc
          apply Prod.ext <;> dsimp only [Prod.fst, Prod.snd] at ha hb ⊢ <;> omega
      rcases two T hT with rfl | rfl
      · exact Or.inl pp.symm
      · exact Or.inr pq.symm
    · rintro (rfl | rfl)
      · exact ⟨_,pp.symm⟩
      · exact ⟨_,pq.symm⟩
  have finite_fiber (v : ℕ × ℕ) : {t : Source | composition t = v}.Finite := by
    have hf := Set.finite_range (fun t : Fiber v => t.val)
    convert hf using 1
    ext t
    simp [Fiber]
  have finite : (scalarFiber L).Finite := by
    have hf := ((finite_fiber (0,7)).union (finite_fiber (3,5))).union
      ((finite_fiber (6,3)).union (finite_fiber (9,1)))
    apply hf.subset
    intro U hU
    have hc := (scalar _ _).mp hU
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_cases hL : L = 0
    · rw [if_pos hL] at hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      tauto
    · rw [if_neg hL] at hc
      exact Or.inl (Or.inr hc)
  have weight_min (t : Source) : 2 ≤ GraftAffineClosure.quantity (composition t) := by
    have hp := positive_count t
    simp only [GraftAffineClosure.quantity]
    omega
  have weight_two (t : Source) (ht : GraftAffineClosure.quantity (composition t) = 2) :
      t = .of true := by
    have hp := positive_count t
    simp only [GraftAffineClosure.quantity] at ht
    obtain ⟨b,rfl⟩ := single t (by omega)
    cases b <;> simp_all [composition]
  have beta_root (t : Source) (ht : readout [] t = .beta) : t = .of false := by
    cases t with
    | of b => cases b <;> cases ht <;> rfl
    | mul s t => cases ht
  have beta_P : ∀ U ∈ scalarFiber 0,
      (∀ u ∈ certificate 0 P, readout u U = readout u P) → U = P := by
    intro U hU hm
    have h1 : readout [false,false,false] U = .beta := hm _ (by decide)
    have h2 : readout [false,true] U = .beta := hm _ (by decide)
    have h3 : readout [true,false,false,false] U = .beta := hm _ (by decide)
    have h4 : readout [true,false,true] U = .beta := hm _ (by decide)
    have h5 : readout [true,true,false] U = .beta := hm _ (by decide)
    cases U with
    | of b => simp [readout] at h1
    | mul s t =>
      cases s with
      | of b => simp [readout] at h1
      | mul s r =>
        have hr : r = .of false := beta_root r h2
        subst r
        cases s with
        | of b => simp [readout] at h1
        | mul s x =>
          have hs : s = .of false := beta_root s h1
          subst s
          cases t with
          | of b => simp [readout] at h3
          | mul t r =>
            cases t with
            | of b => simp [readout] at h3
            | mul t s =>
              have hs : s = .of false := beta_root s h4
              subst s
              cases t with
              | of b => simp [readout] at h3
              | mul s y =>
                have hs : s = .of false := beta_root s h3
                subst s
                cases r with
                | of b => simp [readout] at h5
                | mul s z =>
                  have hs : s = .of false := beta_root s h5
                  subst s
                  change 2 * (composition _).1 + 3 * (composition _).2 = 21 at hU
                  simp only [composition, Prod.fst_add, Prod.snd_add] at hU
                  have hx := weight_min x
                  have hy := weight_min y
                  have hz := weight_min z
                  have ex : x = .of true := weight_two x (by
                    dsimp only [GraftAffineClosure.quantity] at hx hy hz ⊢; omega)
                  have ey : y = .of true := weight_two y (by
                    dsimp only [GraftAffineClosure.quantity] at hx hy hz ⊢; omega)
                  have ez : z = .of true := weight_two z (by
                    dsimp only [GraftAffineClosure.quantity] at hx hy hz ⊢; omega)
                  subst x; subst y; subst z; rfl
  have beta_Q : ∀ U ∈ scalarFiber 0,
      (∀ u ∈ certificate 0 Q, readout u U = readout u Q) → U = Q := by
    intro U hU hm
    have hR : readout [true,true] U = .beta := hm _ (by decide)
    cases U with
    | of b => simp [readout] at hR
    | mul s t =>
      have hS : .mul t s ∈ scalarFiber 0 := by
        simpa [scalarFiber, composition, add_comm] using hU
      have he := beta_P (.mul t s) hS (by
        intro u hu
        change u ∈ ({[false,false,false],[false,true],[true,false,false,false],
          [true,false,true],[true,true,false]} : Finset Address) at hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact hm [true,false,false] (by decide)
        · exact hm [true,true] (by decide)
        · exact hm [false,false,false,false] (by decide)
        · exact hm [false,false,true] (by decide)
        · exact hm [false,true,false] (by decide))
      change (FreeMagma.mul t s : Source) = .mul ActualImageSevenLeafSeparation.A
        ActualImageSevenLeafSeparation.C at he
      injection he with ht hs
      rw [ht,hs]
      rfl
  let block (u : Address) : Finset Address := {u,u ++ [false],u ++ [true]}
  have literal_data : ∀ V : Source, V = P ∨ V = Q →
      (alphaAddresses V).card = 3 ∧ (certificate 0 V).card = 5 ∧
      (∀ u ∈ certificate 0 V, Disjoint (block u) (alphaAddresses V)) ∧
      (∀ u ∈ certificate 0 V, ∀ v ∈ certificate 0 V, u ≠ v →
        Disjoint (block u) (block v)) ∧
      (∀ a ∈ alphaAddresses V, ∀ b ∈ certificate 0 V,
        composition (flip (flip V a) b) = (3,5) ∧
        ActualTreeReadoutAcquisition.sourceLaw (flip (flip V a) b) = false ∧
        a ∈ leaves V ∧ b ∈ leaves (flip V a)) ∧
      (∀ a ∈ certificate 0 V, ∀ b ∈ certificate 0 V, a ≠ b →
        composition (flip (ActualImageAddressCertificate.replace V a
          (.mul (.of true) (.of true))) b) = (6,3) ∧
        ActualTreeReadoutAcquisition.sourceLaw (flip
          (ActualImageAddressCertificate.replace V a (.mul (.of true) (.of true))) b) = false ∧
        b ∈ leaves (ActualImageAddressCertificate.replace V a (.mul (.of true) (.of true)))) := by
    intro V hV
    rcases hV with rfl | rfl <;> decide
  have graft_read : ∀ V : Source, V = P ∨ V = Q → ∀ a ∈ certificate 0 V,
      ∀ u : Address, u ∉ block a →
        readout u (ActualImageAddressCertificate.replace V a (.mul (.of true) (.of true))) =
          readout u V := by
    intro V hV a ha u hu
    clear literal_data beta_Q beta_P weight_two weight_min beta_root finite finite_fiber
      classification memQ memP pq pp cq cp two single positive_count scalar
    clear L
    rcases hV with rfl | rfl
    all_goals first
      | change a ∈ ({[false,false,false],[false,true],[true,false,false,false],
          [true,false,true],[true,true,false]} : Finset Address) at ha
      | change a ∈ ({[false,false,false,false],[false,false,true],[false,true,false],
          [true,false,false],[true,true]} : Finset Address) at ha
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [ActualImageAddressCertificate.replace, P, Q,
        ActualImageSevenLeafSeparation.A, ActualImageSevenLeafSeparation.C,
        ActualImageSevenLeafSeparation.E]
      simp only [block, Finset.mem_insert, Finset.mem_singleton, List.append] at hu
      iterate 6 (all_goals first
        | rfl
        | exact (hu (Or.inl rfl)).elim
        | exact (hu (Or.inr (Or.inl rfl))).elim
        | exact (hu (Or.inr (Or.inr rfl))).elim
        | (simp_all [readout]; done)
        | (cases u
           case' cons b u => cases b))
      all_goals simp_all [readout, List.append]
  have obstruct (t : Source) (ht : ActualTreeReadoutAcquisition.sourceLaw t = false) :
      ¬ Positive t := by
    rintro ⟨S,hS⟩
    have hx := ActualTreeReadoutAcquisition.source_foundation.1 S
    rw [hS,ht] at hx
    contradiction
  have beta_minimum : ∀ V : Source, V = P ∨ V = Q → ∀ J : Finset Address,
      FiberSound 0 V J → J.card ≤ 5 → J = certificate 0 V := by
    intro V hV J hsound hcard
    obtain ⟨hAcard,hBcard,hdisj,hpair,hswap,hgraft⟩ := literal_data V hV
    by_cases hB : certificate 0 V ⊆ J
    · exact (Finset.eq_of_subset_of_card_le hB (by omega)).symm
    · obtain ⟨b,hb,hbj⟩ : ∃ b ∈ certificate 0 V, b ∉ J := by
        exact Finset.not_subset.mp hB
      have hA : alphaAddresses V ⊆ J := by
        intro a ha
        by_contra haj
        obtain ⟨hc,hn,hal,hbl⟩ := hswap a ha b hb
        apply obstruct _ hn
        apply hsound (flip (flip V a) b)
        · simp only [scalarFiber, Set.mem_setOf_eq, hc]
        · intro u hu
          exact (ActualTreeReadoutAcquisition.source_foundation.2.2.2.1
            (flip V a) b hbl u (fun he => hbj (he ▸ hu))).trans
            (ActualTreeReadoutAcquisition.source_foundation.2.2.2.1
              V a hal u (fun he => haj (he ▸ hu)))
      let hit := (certificate 0 V).filter (fun u => ¬ Disjoint (block u) J)
      let pick : Address → Address := fun u =>
        if hh : u ∈ hit then Classical.choose (Finset.not_disjoint_iff.mp
          (Finset.mem_filter.mp hh).2) else []
      have picks (u : Address) (hu : u ∈ hit) : pick u ∈ block u ∧ pick u ∈ J := by
        simp only [pick, dif_pos hu]
        exact Classical.choose_spec (Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hu).2)
      have hc : hit.card ≤ (J \ alphaAddresses V).card := by
        apply Finset.card_le_card_of_injOn pick
        · intro u hu
          have hh := picks u hu
          exact Finset.mem_sdiff.mpr ⟨hh.2,
            (hdisj u (Finset.mem_filter.mp hu).1).notMem_of_mem_left_finset hh.1⟩
        · intro u hu v hv he
          by_contra hne
          have hd := hpair u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 hne
          exact hd.notMem_of_mem_left_finset (picks u hu).1 (he ▸ (picks v hv).1)
      have hj : (J \ alphaAddresses V).card ≤ 2 := by
        rw [Finset.card_sdiff_of_subset hA,hAcard]
        omega
      let clear := (certificate 0 V).filter (fun u => Disjoint (block u) J)
      have hsum : hit.card + clear.card = 5 := by
        have he := Finset.card_filter_add_card_filter_not (s := certificate 0 V)
          (fun u => ¬ Disjoint (block u) J)
        simpa only [not_not,hBcard] using he
      obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < clear.card by omega)
      have haB := (Finset.mem_filter.mp ha).1
      have hbB := (Finset.mem_filter.mp hb).1
      have haD := (Finset.mem_filter.mp ha).2
      have hbD := (Finset.mem_filter.mp hb).2
      obtain ⟨hcomp,hneg,hbl⟩ := hgraft a haB b hbB hab
      let W := flip (ActualImageAddressCertificate.replace V a (.mul (.of true) (.of true))) b
      exfalso
      apply obstruct W hneg
      apply hsound W
      · change 2 * (composition W).1 + 3 * (composition W).2 = 21
        rw [hcomp]
        rfl
      · intro u hu
        exact (ActualTreeReadoutAcquisition.source_foundation.2.2.2.1 _ b hbl u (by
          intro he
          exact hbD.notMem_of_mem_left_finset (by simp [block]) (he ▸ hu))).trans
          (graft_read V hV a haB u (haD.notMem_of_mem_right_finset hu))
  have run_cost (policy : Policy) (U : Source) (n : ℕ)
      (hb : Hist (fun _ : Address => Reply) × Bool)
      (he : execute readout policy n [] U = some hb) :
      extendedCost policy U = ((paid hb.1).card : ℝ≥0∞) := by
    let h : ∃ n hb, execute readout policy n [] U = some hb := ⟨n,hb,he⟩
    unfold extendedCost
    rw [dif_pos h]
    exact congrArg (fun t : Hist (fun _ : Address => Reply) × Bool =>
      ((paid t.1).card : ℝ≥0∞))
      (ActualTreeReadoutAcquisition.source_foundation.2.2.2.2.2.2.2 policy
        (Classical.choose h) n [] U _ hb (Classical.choose_spec (Classical.choose_spec h)) he)
  have run_transfer (policy : Policy) : ∀ n (hist : Hist (fun _ : Address => Reply))
      (V U : Source) (hb : Hist (fun _ : Address => Reply) × Bool),
      execute readout policy n hist V = some hb →
      (∀ u ∈ paid hb.1, readout u U = readout u V) →
      execute readout policy n hist U = some hb := by
    intro n
    induction n with
    | zero => simp [execute]
    | succ n ih =>
      intro hist V U hb he hm
      cases hp : policy hist with
      | inr b => simpa [execute,hp] using he
      | inl q =>
        cases hr : execute readout policy n (hist ++ [⟨q,readout q V⟩]) V with
        | none => simp [execute,hp,hr] at he
        | some x =>
          have hx : (⟨q,readout q V⟩ :: x.1,x.2) = hb := by simpa [execute,hp,hr] using he
          subst hb
          have hq : readout q U = readout q V := hm q (by simp [paid])
          have hm' : ∀ u ∈ paid x.1, readout u U = readout u V := by
            intro u hu
            exact hm u (by simpa [paid] using Or.inr hu)
          have hs := ih _ V U x hr hm'
          simp [execute,hp,hq,hs]
  have same_composition_member (V U : Source) (hV : V ∈ scalarFiber L)
      (hc : composition U = composition V) : U ∈ scalarFiber L := by
    simpa [scalarFiber,hc] using hV
  have path_sound (policy : Policy) (hc : CorrectOn L policy) (V : Source)
      (n : ℕ) (hb : Hist (fun _ : Address => Reply) × Bool)
      (he : execute readout policy n [] V = some hb) (ht : hb.2 = true) :
      FiberSound L V (paid hb.1) := by
    intro U hU hm
    have hre := run_transfer policy n [] V U hb he hm
    obtain ⟨m,x,hx,hlabel⟩ := hc U hU
    have hh := ActualTreeReadoutAcquisition.source_foundation.2.2.2.2.2.2.2
      policy n m [] U hb x hre hx
    exact hlabel.mp (by rw [← hh]; exact ht)
  have positive_V (V : Source) (hV : V = P ∨ V = Q) : Positive V := by
    rcases hV with rfl | rfl
    · exact ⟨_,pp.symm⟩
    · exact ⟨_,pq.symm⟩
  have member_V (V : Source) (hV : V = P ∨ V = Q) : V ∈ scalarFiber L := by
    rcases hV with rfl | rfl <;> assumption
  have height_V (V : Source) (hV : V = P ∨ V = Q) :
      ActualImageAddressCertificate.height V = 4 := by
    rcases hV with rfl | rfl <;> rfl
  have path_composition_sound (V : Source) (hV : V = P ∨ V = Q) (h : ℕ)
      (J : Finset Address) (hw : Within h J) (hs : FiberSound L V J) : Sound 3 V h J := by
    refine ⟨hw,?_⟩
    intro U hc hm
    exact hs U (same_composition_member V U (member_V V hV) hc) hm
  have depth_obstruction (h : ℕ) (hh : h < 4) :
      ¬ ∃ policy : Policy, CorrectOn L policy ∧ WindowOn L h policy := by
    rintro ⟨policy,hc,hw⟩
    obtain ⟨n,hb,he,hl⟩ := hc P memP
    have ht : hb.2 = true := hl.mpr (positive_V P (Or.inl rfl))
    have hs := path_composition_sound P (Or.inl rfl) h (paid hb.1)
      (hw P memP n hb he) (path_sound policy hc P n hb he ht)
    have hn := (ActualImageAddressCertificate.result 1 (by omega) P
      (positive_V P (Or.inl rfl)) h).1
    exact hn (by rw [height_V P (Or.inl rfl)]; exact hh) ⟨paid hb.1,hs⟩
  have cert_geometry (V : Source) (hV : V = P ∨ V = Q) :
      (certificate L V).card = certificateSize L ∧ Within 4 (certificate L V) := by
    rcases hV with rfl | rfl <;> by_cases hL : L = 0 <;>
      simp only [certificate,certificateSize,hL,ite_true,ite_false] <;>
      dsimp only [Within] <;> decide
  have cert_disjoint : Disjoint (certificate L P) (certificate L Q) := by
    by_cases hL : L = 0 <;> simp only [certificate,hL,ite_true,ite_false] <;> decide
  have cert_sound (V : Source) (hV : V = P ∨ V = Q) :
      FiberSound L V (certificate L V) := by
    by_cases hL : L = 0
    · subst L
      intro U hU hm
      rcases hV with rfl | rfl
      · rw [beta_P U hU hm]; exact ⟨_,pp.symm⟩
      · rw [beta_Q U hU hm]; exact ⟨_,pq.symm⟩
    · have hw := (cert_geometry V hV).2
      rw [certificate,if_neg hL] at hw
      have hs := ((ActualImageAddressCertificate.rigidity 1 (by omega) V
        (positive_V V hV)).1 4 (by rw [height_V V hV]) (alphaAddresses V) hw).mpr rfl
      intro U hU hm
      have hc := (scalar _ _).mp hU
      rw [if_neg hL] at hc
      have cv : composition V = (3,5) := by rcases hV with rfl | rfl <;> rfl
      exact hs.1.2 U (hc.trans cv.symm) (by simpa [certificate,hL] using hm)
  have cert_min (V : Source) (hV : V = P ∨ V = Q) (h : ℕ) (hh : 4 ≤ h)
      (J : Finset Address) (hw : Within h J) (hs : FiberSound L V J) :
      certificateSize L ≤ J.card ∧ (J.card = certificateSize L → J = certificate L V) := by
    by_cases hL : L = 0
    · subst L
      have lower : 5 ≤ J.card := by
        by_contra hn
        have he := beta_minimum V hV J hs (by omega)
        have hc := (literal_data V hV).2.1
        rw [he,hc] at hn
        omega
      exact ⟨lower,fun he => beta_minimum V hV J hs
        (show J.card = 5 from by simpa [certificateSize] using he).le⟩
    · have cs := path_composition_sound V hV h J hw hs
      have cv : (composition V).1 = 3 := by rcases hV with rfl | rfl <;> rfl
      have lo := (ActualImageAddressCertificate.result 1 (by omega) V
        (positive_V V hV) h).2.2 J cs
      have un := (ActualImageAddressCertificate.rigidity 1 (by omega) V
        (positive_V V hV)).1 h (by rw [height_V V hV]; exact hh) J hw
      refine ⟨by simpa [certificateSize,hL,cv] using lo,?_⟩
      intro he
      have eqJ := un.mp ⟨cs,by simpa [certificateSize,hL,cv] using he⟩
      simpa [certificate,hL] using eqJ
  have path_min (policy : Policy) (hc : CorrectOn L policy) (h : ℕ)
      (hh : 4 ≤ h) (hw : WindowOn L h policy) (V : Source) (hV : V = P ∨ V = Q)
      (n : ℕ) (hb : Hist (fun _ : Address => Reply) × Bool)
      (he : execute readout policy n [] V = some hb) :
      certificateSize L ≤ (paid hb.1).card ∧
        ((paid hb.1).card = certificateSize L → paid hb.1 = certificate L V) := by
    obtain ⟨m,x,hx,hl⟩ := hc V (member_V V hV)
    have eqh := ActualTreeReadoutAcquisition.source_foundation.2.2.2.2.2.2.2
      policy n m [] V hb x he hx
    have ht : hb.2 = true := by rw [eqh]; exact hl.mpr (positive_V V hV)
    exact cert_min V hV h hh (paid hb.1) (hw V (member_V V hV) n hb he)
      (path_sound policy hc V n hb he ht)
  have first_paid (policy : Policy) (u : Address) (hp : policy [] = .inl u)
      (V : Source) (n : ℕ) (hb : Hist (fun _ : Address => Reply) × Bool)
      (he : execute readout policy n [] V = some hb) : u ∈ paid hb.1 := by
    cases n with
    | zero => simp [execute] at he
    | succ n =>
      simp only [execute,hp,Option.map_eq_some_iff] at he
      obtain ⟨x,hx,he⟩ := he
      rw [← he]
      simp [paid]
  have coupled (policy : Policy) (h : ℕ) (hh : 4 ≤ h)
      (hc : CorrectOn L policy) (hw : WindowOn L h policy) :
      (certificateSize L : ℝ≥0∞) ≤ extendedCost policy P ∧
      (certificateSize L : ℝ≥0∞) ≤ extendedCost policy Q ∧
      ((2 * certificateSize L + 1 : ℕ) : ℝ≥0∞) ≤
        extendedCost policy P + extendedCost policy Q ∧
      ((certificateSize L + 1 : ℕ) : ℝ≥0∞) ≤
        ⨆ U : scalarFiber L, extendedCost policy U.val := by
    obtain ⟨n,x,hx,_⟩ := hc P memP
    obtain ⟨m,y,hy,_⟩ := hc Q memQ
    have hpx := path_min policy hc h hh hw P (Or.inl rfl) n x hx
    have hqy := path_min policy hc h hh hw Q (Or.inr rfl) m y hy
    have unequal : ¬ ((paid x.1).card = certificateSize L ∧
        (paid y.1).card = certificateSize L) := by
      rintro ⟨ex,ey⟩
      have jx := hpx.2 ex
      have jy := hqy.2 ey
      cases hp : policy [] with
      | inr b =>
        cases n with
        | zero => simp [execute] at hx
        | succ n =>
          have he : ([],b) = x := by simpa [execute,hp] using hx
          rw [← he] at ex
          have hk : 0 < certificateSize L := by unfold certificateSize; split_ifs <;> omega
          simp [paid] at ex
          omega
      | inl u =>
        have hux : u ∈ certificate L P := jx ▸ first_paid policy u hp P n x hx
        have huy : u ∈ certificate L Q := jy ▸ first_paid policy u hp Q m y hy
        exact cert_disjoint.notMem_of_mem_left_finset hux huy
    have hs : 2 * certificateSize L + 1 ≤ (paid x.1).card + (paid y.1).card := by omega
    have worst : certificateSize L + 1 ≤ (paid x.1).card ∨
        certificateSize L + 1 ≤ (paid y.1).card := by omega
    rw [run_cost policy P n x hx,run_cost policy Q m y hy]
    refine ⟨by exact_mod_cast hpx.1,by exact_mod_cast hqy.1,?_,?_⟩
    · exact_mod_cast hs
    · rcases worst with hwx | hwy
      · refine (show ((certificateSize L + 1 : ℕ) : ℝ≥0∞) ≤
          ((paid x.1).card : ℝ≥0∞) from by exact_mod_cast hwx).trans ?_
        rw [← run_cost policy P n x hx]
        exact le_iSup (fun U : scalarFiber L => extendedCost policy U.val) ⟨P,memP⟩
      · refine (show ((certificateSize L + 1 : ℕ) : ℝ≥0∞) ≤
          ((paid y.1).card : ℝ≥0∞) from by exact_mod_cast hwy).trans ?_
        rw [← run_cost policy Q m y hy]
        exact le_iSup (fun U : scalarFiber L => extendedCost policy U.val) ⟨Q,memQ⟩
  have table (favorP : Bool) (U : Source) :
      ∃ hb : Hist (fun _ : Address => Reply) × Bool,
        execute readout (strategy L favorP) 7 [] U = some hb ∧
        Within 4 (paid hb.1) ∧ (hb.1.map Sigma.fst).Nodup ∧
        (paid hb.1).card ≤ certificateSize L + 1 ∧
        (hb.2 = true →
          (∀ u ∈ certificate L P, readout u U = readout u P) ∨
          (∀ u ∈ certificate L Q, readout u U = readout u Q)) := by
    clear coupled first_paid path_min cert_min cert_sound cert_disjoint cert_geometry
      depth_obstruction path_composition_sound height_V member_V positive_V path_sound
      same_composition_member run_transfer run_cost beta_minimum obstruct graft_read literal_data
      beta_Q beta_P weight_two weight_min beta_root finite finite_fiber classification memQ memP
      pq pp cq cp two single positive_count scalar block
    have test_run (label : Reply) (qs : List Address) :
        ∀ (policy : Policy) (U : Source) (baseHist : Hist (fun _ : Address => Reply)) (fuel : ℕ),
        qs.length + 1 ≤ fuel →
        (∀ hist, policy (baseHist ++ hist) = testNext label qs hist) →
        ∃ hb : Hist (fun _ : Address => Reply) × Bool,
          execute readout policy fuel baseHist U = some hb ∧
          hb.1.map Sigma.fst <+: qs ∧
          (hb.2 = true → ∀ u ∈ qs, readout u U = label) := by
      induction qs with
      | nil =>
        intro policy U baseHist fuel hf hp
        cases fuel with
        | zero => simp at hf
        | succ n =>
          have hp0 : policy baseHist = .inr true := by
            simpa only [List.append_nil, testNext] using hp []
          refine ⟨([],true), ?_, ⟨[],rfl⟩, ?_⟩
          · simp only [execute,hp0]
          · simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]
      | cons u qs ih =>
        intro policy U baseHist fuel hf hp
        cases fuel with
        | zero => simp at hf
        | succ n =>
          have hp0 : policy baseHist = .inl u := by
            simpa only [List.append_nil,testNext] using hp []
          by_cases hr : readout u U = label
          · have hp1 : ∀ hist,
                policy ((baseHist ++ [⟨u,readout u U⟩]) ++ hist) = testNext label qs hist := by
              intro hist
              rw [List.append_assoc,hp]
              simp only [List.singleton_append,testNext,hr,eq_self_iff_true,ite_true,and_self]
            obtain ⟨hb,he,hpre,hacc⟩ := ih policy U (baseHist ++ [⟨u,readout u U⟩]) n
              (by simp only [List.length_cons] at hf; omega) hp1
            refine ⟨(⟨u,readout u U⟩ :: hb.1,hb.2), ?_, ?_, ?_⟩
            · simp only [execute,hp0,he,Option.map_some]
            · simpa only [List.map_cons] using List.cons_prefix_cons.mpr ⟨rfl,hpre⟩
            · intro ht v hv
              rcases List.mem_cons.mp hv with rfl | hv
              · exact hr
              · exact hacc ht v hv
          · have hp1 : policy (baseHist ++ [⟨u,readout u U⟩]) = .inr false := by
              rw [hp]
              simp only [testNext,hr,and_false,ite_false]
            cases n with
            | zero => simp at hf
            | succ n =>
              refine ⟨([⟨u,readout u U⟩],false), ?_, ⟨qs,rfl⟩, ?_⟩
              · simp only [execute,hp0,hp1,Option.map_some]
              · simp only [Bool.false_eq_true,IsEmpty.forall_iff]
    let first : Address := if L = 0 then
      (if favorP then [false,true] else [true,true])
      else (if favorP then [false,false,true] else [true,false,true])
    have at_nil : strategy L favorP [] = .inl first := rfl
    have at_cons (p : Σ _ : Address, Reply) (rest : Hist (fun _ : Address => Reply)) :
        strategy L favorP (p :: rest) =
      if p.1 ≠ first then .inr false else
      if L = 0 then
        if favorP then
          match p.2 with
          | .beta => testNext .beta [[false,false,false],[true,false,false,false],
              [true,false,true],[true,true,false]] rest
          | .branch => testNext .beta [[false,false,false,false],[false,false,true],
              [false,true,false],[true,false,false],[true,true]] rest
          | .alpha | .absent => .inr false
        else
          match p.2 with
          | .beta => testNext .beta [[false,false,false,false],[false,false,true],
              [false,true,false],[true,false,false]] rest
          | .branch => testNext .beta [[false,false,false],[false,true],
              [true,false,false,false],[true,false,true],[true,true,false]] rest
          | .alpha | .absent => .inr false
      else
        if favorP then
          match p.2 with
          | .alpha => testNext .alpha [[true,false,false,true],[true,true,true]] rest
          | .beta => testNext .alpha [[false,false,false,true],[false,true,true],[true,false,true]] rest
          | .branch | .absent => .inr false
        else
          match p.2 with
          | .alpha => testNext .alpha [[false,false,false,true],[false,true,true]] rest
          | .beta => testNext .alpha [[false,false,true],[true,false,false,true],[true,true,true]] rest
          | .branch | .absent => .inr false := rfl
    have branch (label : Reply) (qs : List Address)
        (hp : ∀ hist, strategy L favorP ([⟨first,readout first U⟩] ++ hist) =
          testNext label qs hist)
        (hf : qs.length + 1 ≤ 6)
        (hw : ∀ u ∈ first :: qs, u.length ≤ 4)
        (hn : (first :: qs).Nodup)
        (hc : (first :: qs).length ≤ certificateSize L + 1)
        (hs : (∀ u ∈ qs, readout u U = label) →
          (∀ u ∈ certificate L P, readout u U = readout u P) ∨
          (∀ u ∈ certificate L Q, readout u U = readout u Q)) :
        ∃ hb : Hist (fun _ : Address => Reply) × Bool,
          execute readout (strategy L favorP) 7 [] U = some hb ∧
          Within 4 (paid hb.1) ∧ (hb.1.map Sigma.fst).Nodup ∧
          (paid hb.1).card ≤ certificateSize L + 1 ∧
          (hb.2 = true →
            (∀ u ∈ certificate L P, readout u U = readout u P) ∨
            (∀ u ∈ certificate L Q, readout u U = readout u Q)) := by
      obtain ⟨hb,he,hpre,hacc⟩ := test_run label qs (strategy L favorP) U
        [⟨first,readout first U⟩] 6 hf hp
      have hpre' : first :: hb.1.map Sigma.fst <+: first :: qs :=
        List.cons_prefix_cons.mpr ⟨rfl,hpre⟩
      refine ⟨(⟨first,readout first U⟩ :: hb.1,hb.2), ?_, ?_, ?_, ?_, ?_⟩
      · rw [execute,at_nil]
        simp only [List.nil_append]
        rw [he]
        rfl
      · intro u hu
        exact hw u (hpre'.subset (List.mem_toFinset.mp hu))
      · exact hpre'.nodup hn
      · exact (List.toFinset_card_le _).trans (hpre'.length_le.trans hc)
      · exact fun ht => hs (hacc ht)
    have reject (hp : strategy L favorP [⟨first,readout first U⟩] = .inr false)
        (hf : first.length ≤ 4) :
        ∃ hb : Hist (fun _ : Address => Reply) × Bool,
          execute readout (strategy L favorP) 7 [] U = some hb ∧
          Within 4 (paid hb.1) ∧ (hb.1.map Sigma.fst).Nodup ∧
          (paid hb.1).card ≤ certificateSize L + 1 ∧
          (hb.2 = true →
            (∀ u ∈ certificate L P, readout u U = readout u P) ∨
            (∀ u ∈ certificate L Q, readout u U = readout u Q)) := by
      refine ⟨([⟨first,readout first U⟩],false), ?_, ?_, ?_, ?_, ?_⟩
      · simp only [execute,at_nil,List.nil_append,hp,Option.map_some]
      · simpa only [Within,paid,List.map_cons,List.map_nil,List.toFinset_cons,
          List.toFinset_nil,Finset.mem_insert,Finset.notMem_empty,or_false,forall_eq] using hf
      · simp only [List.map_cons,List.map_nil,List.nodup_singleton]
      · simp only [paid,List.map_cons,List.map_nil,List.toFinset_cons,List.toFinset_nil,
          Finset.insert_empty,Finset.card_singleton]; omega
      · simp only [Bool.false_eq_true,IsEmpty.forall_iff]
    clear test_run at_nil
    cases hr : readout first U
    all_goals by_cases hL : L = 0
    all_goals cases favorP
    all_goals
      have tail := at_cons ⟨first,readout first U⟩
      conv at tail =>
        intro rest
        rhs
        simp only [hL,hr,ne_eq,eq_self_iff_true,not_true_eq_false,
          ite_false,ite_true,Bool.false_eq_true]
    all_goals first
      | (apply reject
         · exact tail []
         · simp only [first,hL,ite_true,ite_false,Bool.false_eq_true]; decide)
      | (refine branch _ _ tail ?_ ?_ ?_ ?_ ?_
         · decide
         · simp only [first,hL,ite_true,ite_false,Bool.false_eq_true]; decide
         · simp only [first,hL,ite_true,ite_false,Bool.false_eq_true]; decide
         · simp only [first,hL,certificateSize,ite_true,ite_false,Bool.false_eq_true]; decide
         · intro hm
           simp only [first,hL,ite_true,ite_false,Bool.false_eq_true] at hr
           clear at_cons tail branch reject
           simp only [certificate,hL,ite_true,ite_false]
           clear first
           simp only [List.forall_mem_cons,List.forall_mem_nil,and_true] at hm
           first
             | change
                 ((∀ u ∈ ({[false,false,false],[false,true],[true,false,false,false],
                     [true,false,true],[true,true,false]} : Finset Address),
                   readout u U = readout u P) ∨
                  (∀ u ∈ ({[false,false,false,false],[false,false,true],[false,true,false],
                     [true,false,false],[true,true]} : Finset Address),
                   readout u U = readout u Q))
             | change
                 ((∀ u ∈ ({[false,false,true],[true,false,false,true],
                     [true,true,true]} : Finset Address), readout u U = readout u P) ∨
                  (∀ u ∈ ({[false,false,false,true],[false,true,true],
                     [true,false,true]} : Finset Address), readout u U = readout u Q))
           simp only [Finset.forall_mem_insert,Finset.mem_singleton,forall_eq,
             readout,P,Q,ActualImageSevenLeafSeparation.A,
             ActualImageSevenLeafSeparation.C,ActualImageSevenLeafSeparation.E]
           simp only [hr]
           tauto)
  have positive_details (favorP : Bool) :
      ∃ x y : Hist (fun _ : Address => Reply) × Bool,
        execute readout (strategy L favorP) 7 [] P = some x ∧
        execute readout (strategy L favorP) 7 [] Q = some y ∧
        x.2 = true ∧ y.2 = true ∧
        (paid x.1).card = (if favorP then certificateSize L else certificateSize L + 1) ∧
        (paid y.1).card = (if favorP then certificateSize L + 1 else certificateSize L) := by
    have model : strategy L favorP = strategy (if L = 0 then 0 else 1) favorP := by
      by_cases hL : L = 0
      · subst L; rfl
      · funext hist
        simp only [strategy,if_neg hL,show (1 : ℕ) ≠ 0 from by decide,ite_false]
    rw [model]
    by_cases hL : L = 0
    all_goals cases favorP
    all_goals simp only [certificateSize,hL,ite_true,ite_false]
    all_goals refine ⟨_,_,rfl,rfl,rfl,rfl,?_,?_⟩ <;> decide
  have upper (favorP : Bool) :
      CorrectOn L (strategy L favorP) ∧ WindowOn L 4 (strategy L favorP) ∧
      NoRepeatOn L (strategy L favorP) ∧
      (∀ U ∈ scalarFiber L, extendedCost (strategy L favorP) U ≤
        ((certificateSize L + 1 : ℕ) : ℝ≥0∞)) ∧
      extendedCost (strategy L favorP) P =
        ((if favorP then certificateSize L else certificateSize L + 1 : ℕ) : ℝ≥0∞) ∧
      extendedCost (strategy L favorP) Q =
        ((if favorP then certificateSize L + 1 else certificateSize L : ℕ) : ℝ≥0∞) := by
    obtain ⟨x,y,hx,hy,xt,yt,xc,yc⟩ := positive_details favorP
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro U hU
      obtain ⟨hb,he,hw,hn,hcard,hs⟩ := table favorP U
      refine ⟨7,hb,he,?_⟩
      constructor
      · intro ht
        rcases hs ht with hm | hm
        · exact cert_sound P (Or.inl rfl) U hU hm
        · exact cert_sound Q (Or.inr rfl) U hU hm
      · intro hp
        rcases (classification U hU).mp hp with rfl | rfl
        · have heq : hb = x := Option.some.inj (he.symm.trans hx)
          rw [heq]; exact xt
        · have heq : hb = y := Option.some.inj (he.symm.trans hy)
          rw [heq]; exact yt
    · intro U hU n hb he
      obtain ⟨z,hz,hw,_,_,_⟩ := table favorP U
      have heq := ActualTreeReadoutAcquisition.source_foundation.2.2.2.2.2.2.2
        (strategy L favorP) 7 n [] U z hb hz he
      rw [← heq]; exact hw
    · intro U hU n hb he
      obtain ⟨z,hz,_,hn,_,_⟩ := table favorP U
      have heq := ActualTreeReadoutAcquisition.source_foundation.2.2.2.2.2.2.2
        (strategy L favorP) 7 n [] U z hb hz he
      rw [← heq]; exact hn
    · intro U hU
      obtain ⟨z,hz,_,_,hc,_⟩ := table favorP U
      rw [run_cost _ U 7 z hz]
      exact_mod_cast hc
    · rw [run_cost _ P 7 x hx,xc]
    · rw [run_cost _ Q 7 y hy,yc]
  have window_mono (policy : Policy) (h : ℕ) (hh : 4 ≤ h)
      (hw : WindowOn L 4 policy) : WindowOn L h policy := by
    intro U hU n hb he u hu
    exact (hw U hU n hb he u hu).trans hh
  have exact_discovery (h : ℕ) : discoveryCost L h =
      if h < 4 then ∞ else ((certificateSize L + 1 : ℕ) : ℝ≥0∞) := by
    by_cases hh : h < 4
    · rw [if_pos hh]
      apply le_antisymm le_top
      unfold discoveryCost
      apply le_iInf
      intro policy
      apply le_iInf
      intro hp
      exact False.elim (depth_obstruction h hh ⟨policy,hp⟩)
    · rw [if_neg hh]
      have hh' : 4 ≤ h := by omega
      obtain ⟨hc,hw,hn,hbound,hp,hq⟩ := upper true
      apply le_antisymm
      · unfold discoveryCost
        exact iInf_le_of_le (strategy L true) (iInf_le_of_le
          ⟨hc,window_mono _ h hh' hw⟩ (iSup_le fun U => hbound U.val U.property))
      · unfold discoveryCost
        apply le_iInf
        intro policy
        apply le_iInf
        intro hp
        exact (coupled policy h hh' hp.1 hp.2).2.2.2
  have compositions : Set.image composition (scalarFiber L) =
      if L = 0 then {(0,7),(3,5),(6,3),(9,1)} else {(3,5)} := by
    ext v
    rcases v with ⟨a,b⟩
    constructor
    · rintro ⟨U,hU,he⟩
      have hc := (scalar _ _).mp hU
      rw [he] at hc
      by_cases hL : L = 0 <;> simpa [hL] using hc
    · intro hv
      have hc : PrimeGcdHorizon.observation (3 * L) a b =
          PrimeGcdHorizon.observation (3 * L) 3 5 := by
        apply (scalar a b).mpr
        by_cases hL : L = 0 <;> simpa [hL] using hv
      have hab : 1 ≤ a + b := by
        by_cases hL : L = 0 <;> simp [hL,Prod.mk.injEq] at hv <;> omega
      obtain ⟨T⟩ := (GenealogicalFiberTransport.result.1 a b hab).2.2.1
      exact ⟨T.val,by simpa [scalarFiber,T.property] using hc,T.property⟩
  have positives : scalarFiber L ∩ ActualImage 3 = {P,Q} := by
    ext U
    constructor
    · intro hu
      exact (classification U hu.1).mp hu.2
    · intro hu
      rcases hu with rfl | rfl
      · exact ⟨memP,positive_V P (Or.inl rfl)⟩
      · exact ⟨memQ,positive_V Q (Or.inr rfl)⟩
  refine ⟨finite,compositions,positives,by decide,pp,pq,depth_obstruction h,?_,?_⟩
  · intro hh
    have upP := upper true
    have upQ := upper false
    refine ⟨?_,upP.1,upQ.1,upP.2.1,upQ.2.1,upP.2.2.1,upQ.2.2.1,
      ?_,?_,?_,?_,?_⟩
    · intro policy hc hw
      exact ⟨(coupled policy h hh hc hw).1,(coupled policy h hh hc hw).2.1,
        (coupled policy h hh hc hw).2.2.1⟩
    · intro U hU
      exact ⟨upP.2.2.2.1 U hU,upQ.2.2.2.1 U hU⟩
    · simpa using upP.2.2.2.2.1
    · simpa using upP.2.2.2.2.2
    · simpa using upQ.2.2.2.2.1
    · simpa using upQ.2.2.2.2.2
  · rw [exact_discovery h]
    by_cases hh : h < 4 <;> by_cases hL : L = 0 <;>
      simp only [hh,certificateSize,hL,ite_true,ite_false]
    all_goals norm_num



end D5.S3.Arith.FibonacciAtomic.FixedScalarFiberDiscovery
