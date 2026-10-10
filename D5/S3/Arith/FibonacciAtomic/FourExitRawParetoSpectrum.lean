/- GID: D5/S3/Arith/FibonacciAtomic/FourExitRawParetoSpectrum
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The complete raw four-exit family has exactly six k plus one actual Pareto endpoints. -/

import D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum
import D5.S3.Arith.FibonacciAtomic.FourExitRawDomination
import D5.S3.Arith.FibonacciAtomic.FourExitScanExtension
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Minimal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FourExitRawParetoSpectrum

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition ActualJointResponseCostCore FourExitRawEndpointSpectrum
local notation "Index" => fun k : Nat => Unit ⊕ (Fin k × Fin 4)

/-- The menu dominates all original correct strategies, is simultaneously attained
on every family row, and is precisely the set of minimal actual excess vectors. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    (∀ pi : Strategy, ∃ v ∈ menu k,
      ∀ i : Index k, 8 * k + 16 + v i ≤ cost pi (family k i)) ∧
    (∀ v ∈ menu k, ∃ pi : Strategy,
      ∀ i : Index k, cost pi (family k i) = 8 * k + 16 + v i) ∧
    (∀ v : Index k → Nat,
      Minimal (fun w => ∃ pi : Strategy,
        ∀ i : Index k, w i = cost pi (family k i) - (8 * k + 16)) v ↔ v ∈ menu k) ∧
    Nat.card (menu k) = 6 * k + 1 := by
  classical
  have facts := FourExitRawDomination.result k hk
  have cast_gain {m : Nat} {G : Fin m → Source} {U V : Finset (Fin m)}
      (h : U = V) (r : Recipe G U) (i : Fin m) :
      gain (h ▸ r) i = gain r i := by cases h; rfl
  have lift {l m : Nat} (F : Fin l → Source) (G : Fin m → Source)
      (f : Fin l → Fin m) (hFG : ∀ i, G (f i) = F i) :
      ∀ {S : Finset (Fin l)} (r : Recipe F S),
        ∃ R : Recipe G (S.image f), ∀ i ∈ S, gain R (f i) = gain r i := by
    classical
    intro S r
    have same_child (U : Finset (Fin l)) (a : Fin l → Reply)
        (next : ∀ y, (survivors U a y).Nonempty → Recipe F (survivors U a y))
        (y z : Reply) (hy : (survivors U a y).Nonempty)
        (hz : (survivors U a z).Nonempty) (he : y = z) (i : Fin l) :
        gain (next y hy) i = gain (next z hz) i := by cases he; rfl
    induction r with
    | singleton i =>
      refine ⟨(Finset.image_singleton f i).symm ▸ Recipe.singleton (f i), ?_⟩
      intro j hj
      exact (cast_gain (Finset.image_singleton f i).symm
        (Recipe.singleton (f i)) (f j)).trans rfl
    | split S a hs next ih =>
      obtain ⟨u, hu⟩ := a.property
      let b : actualVectors G := ⟨vector G u, u, rfl⟩
      have hb (i : Fin l) : b.val (f i) = a.val i := by
        change readout u (G (f i)) = a.val i
        rw [hFG]
        exact congrFun hu i
      have responses : (S.image f).image b.val = S.image a.val := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro i _
        exact hb i
      have children (y : Reply) :
          (survivors S a.val y).image f = survivors (S.image f) b.val y := by
        ext z
        simp only [survivors, Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨i, ⟨hi, ha⟩, rfl⟩
          exact ⟨⟨i, hi, rfl⟩, (hb i).trans ha⟩
        · rintro ⟨⟨i, hi, rfl⟩, ha⟩
          exact ⟨i, ⟨hi, (hb i).symm.trans ha⟩, rfl⟩
      have nonempty (y : Reply) (hy : (survivors (S.image f) b.val y).Nonempty) :
          (survivors S a.val y).Nonempty := by
        rw [← children] at hy
        exact Finset.image_nonempty.mp hy
      let nextG := fun y hy => children y ▸ (ih y (nonempty y hy)).choose
      let R : Recipe G (S.image f) := .split (S.image f) b (by rw [responses]; exact hs) nextG
      refine ⟨R, ?_⟩
      intro i hi
      have hfi : f i ∈ S.image f := Finset.mem_image.mpr ⟨i,hi,rfl⟩
      have hci : i ∈ survivors S a.val (b.val (f i)) := by simp [survivors,hi,hb]
      have hbig : (survivors (S.image f) b.val (b.val (f i))).Nonempty :=
        ⟨f i, by simp [survivors,hfi]⟩
      have child_gain : gain (nextG (b.val (f i)) hbig) (f i) =
          gain (next (a.val i) ⟨i, by simp [survivors,hi]⟩) i := by
        calc
          _ = gain ((ih (b.val (f i)) (nonempty _ hbig)).choose) (f i) :=
            cast_gain (children _) _ _
          _ = gain (next (b.val (f i)) (nonempty _ hbig)) i :=
            (ih (b.val (f i)) (nonempty _ hbig)).choose_spec i hci
          _ = _ := same_child S a.val next _ _ _ _ (hb i) i
      change gain (.split (S.image f) b _ nextG) (f i) = _
      simp only [gain, dif_pos hi, dif_pos hfi]
      exact congrArg₂ (· + ·) (congrArg chi (hb i)) child_gain
  let Label := Unit ⊕ ((Fin k × Fin 3) ⊕ (Fin k × Fin 3))
  let encode : Label → Index k → Nat := fun x => match x with
    | .inl u => endpoint k (.inl u)
    | .inr (.inl p) => endpoint k (.inr (p.1,p.2.succ))
    | .inr (.inr p) => endpointWith k p.1 p.2.succ
  let zero : Label → Index k := fun x => match x with
    | .inl u => .inl u
    | .inr (.inl p) => .inr (p.1,p.2.succ)
    | .inr (.inr p) => .inr (p.1,0)
  have zero_iff (x : Label) (i : Index k) : encode x i = 0 ↔ i = zero x := by
    rcases x with u | (p | p)
    · simp [encode, zero, endpoint]
    · simp [encode, zero, endpoint]
    · simp only [encode,zero,endpointWith]
      split_ifs <;> simp_all
  have below (x y : Label) (hxy : encode x ≤ encode y) : x = y := by
    have hz : zero x = zero y := by
      have h := hxy (zero y)
      rw [(zero_iff y _).2 rfl] at h
      exact ((zero_iff x _).1 (Nat.eq_zero_of_le_zero h)).symm
    rcases x with u | (⟨j,b⟩ | ⟨j,b⟩)
    · rcases y with v | (p | p)
      · exact congrArg Sum.inl (Subsingleton.elim u v)
      · simp [zero] at hz
      · simp [zero] at hz
    · rcases y with v | (⟨l,c⟩ | ⟨l,c⟩)
      · simp [zero] at hz
      · have hc : j = l ∧ b = c := by simpa [zero] using hz
        rcases hc with ⟨rfl,rfl⟩
        rfl
      · simp [zero] at hz
    · rcases y with v | (⟨l,c⟩ | ⟨l,c⟩)
      · simp [zero] at hz
      · have hc : j = l ∧ (0 : Fin 4) = c.succ := by
          simpa only [zero, Sum.inr.injEq, Prod.mk.injEq] using hz
        have h := congrArg Fin.val hc.2
        simp only [Fin.val_zero, Fin.val_succ] at h
        omega
      · have hj : j = l := by simpa [zero] using hz
        subst l
        have h := hxy (.inr (j,b.succ))
        have bc : b = c := by
          by_contra hn
          simp [encode, endpointWith, hn] at h
        subst c
        rfl
  have injective : Function.Injective encode := fun x y h => below x y (le_of_eq h)
  have range_eq : menu k = Set.range encode := by
    ext v
    simp only [menu, Set.mem_union, Set.mem_range]
    constructor
    · rintro ((⟨u,rfl⟩ | ⟨p,rfl⟩) | ⟨p,rfl⟩)
      · exact ⟨.inl u,rfl⟩
      · exact ⟨.inr (.inl p),rfl⟩
      · exact ⟨.inr (.inr p),rfl⟩
    · rintro ⟨x,rfl⟩
      rcases x with u | (p | p)
      · exact Or.inl (Or.inl ⟨u,rfl⟩)
      · exact Or.inl (Or.inr ⟨p,rfl⟩)
      · exact Or.inr ⟨p,rfl⟩
  have antichain : ∀ v ∈ menu k, ∀ w ∈ menu k, w ≤ v → w = v := by
    intro v hv w hw h
    rw [range_eq] at hv hw
    obtain ⟨x,rfl⟩ := hw
    obtain ⟨y,rfl⟩ := hv
    exact congrArg encode (below x y h)
  have cardinality : Nat.card (menu k) = 6 * k + 1 := by
    rw [range_eq, Nat.card_range_of_injective injective]
    simp only [Label, Nat.card_eq_fintype_card, Fintype.card_sum,
      Fintype.card_prod, Fintype.card_unit, Fintype.card_fin]
    omega
  let e : Fin (4 * k + 1) ≃ Index k :=
    (Fintype.equivFinOfCardEq (show Fintype.card (Index k) = 4 * k + 1 by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit, Fintype.card_fin]
      omega)).symm
  let F := fun i => family k (e i)
  let S := fun J : Finset (Fin k) => Finset.univ.filter (fun i => match e i with
    | .inl _ => True
    | .inr p => p.1 ∈ J)
  have actualize (r : Recipe F Finset.univ) (v : Index k → Nat)
      (hr : ∀ i, gain r (e.symm i) = v i) :
      ∃ pi : Strategy, ∀ i, cost pi (family k i) = 8 * k + 16 + v i := by
    have supply := ActualJointResponseCostCore.result (4 * k + 1) (by omega) F
      (fun i => (facts.1 (e i)).1)
      (fun i j h => e.injective (facts.2.1 h))
    let C := fun i => (leaves (F i)).length + gain r i
    have hC : C ∈ core F := ⟨r, fun _ => rfl⟩
    obtain ⟨q, pi, _, hp⟩ := supply.2.2.1 C hC
    refine ⟨pi, ?_⟩
    intro i
    have h := (hp (e.symm i)).1
    simpa only [C, F, Equiv.apply_symm_apply, (facts.1 i).2.2, hr] using h
  have baseline_recipe :
      ∃ r : Recipe F Finset.univ, ∀ i, gain r (e.symm i) = endpoint k (.inl ()) i := by
    let i0 := e.symm (.inl ())
    have empty_set : {i0} = S ∅ := by
      ext i
      simp only [Finset.mem_singleton, S, Finset.mem_filter, Finset.mem_univ, true_and]
      cases he : e i with
      | inl u =>
        cases u
        have eq : i = i0 := e.injective (by simp [i0,he])
        simp [eq]
      | inr p =>
        have ne : i ≠ i0 := fun h => by simpa [i0,he] using congrArg e h
        simp [ne]
    let r0 : Recipe F (S ∅) := empty_set ▸ Recipe.singleton i0
    obtain ⟨r, hr, ho⟩ := FourExitScanExtension.ordinary_scan_completion k hk e ∅ r0
    refine ⟨r, ?_⟩
    intro i
    cases i with
    | inl u =>
      cases u
      rw [hr (e.symm (.inl ())) (by simp)]
      rw [show gain r0 (e.symm (.inl ())) = 0 from
        (cast_gain empty_set (Recipe.singleton i0) _).trans rfl]
      simp [endpoint]
    | inr p =>
      rcases p with ⟨j,b⟩
      rw [ho j (by simp) b]
      simp [endpoint]
  let small := fun (j : Fin k) (i : Fin 5) => match i.val with
    | 0 => (Sum.inl () : Index k)
    | 1 => .inr (j,0)
    | 2 => .inr (j,1)
    | 3 => .inr (j,2)
    | _ => .inr (j,3)
  let V := fun (m : Fin 6) (i : Fin 5) =>
    (match m.val with
      | 0 => [1,1,0,1,1]
      | 1 => [1,1,1,0,1]
      | 2 => [1,1,1,1,0]
      | 3 => [1,0,1,2,1]
      | 4 => [1,0,2,1,1]
      | _ => [1,0,1,1,2]).getD i.val 0
  have small_succ (j : Fin k) (b : Fin 4) : small j b.succ = .inr (j,b) := by
    fin_cases b <;> rfl
  have local_recipes (j : Fin k) (m : Fin 6) :
      ∃ r : Recipe F (S {j}), ∀ i, gain r (e.symm (small j i)) = V m i := by
    let L := fun i : Fin 5 => match i.val with
      | 0 => family k (.inl ())
      | 1 => family k (.inr (j,0))
      | 2 => family k (.inr (j,1))
      | 3 => family k (.inr (j,2))
      | _ => family k (.inr (j,3))
    let f := fun i => e.symm (small j i)
    have hFL : ∀ i, F (f i) = L i := by
      intro i
      fin_cases i <;> simp [F,f,small,L]
    have image_full : Finset.univ.image f = S {j} := by
      ext i
      constructor
      · intro hi
        obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        change (match e (e.symm (small j a)) with
          | .inl _ => True | .inr p => p.1 ∈ ({j} : Finset (Fin k)))
        rw [Equiv.apply_symm_apply]
        fin_cases a <;> simp [small]
      · intro hi
        have h : match e i with
            | .inl _ => True | .inr p => p.1 = j := by simpa [S] using hi
        apply Finset.mem_image.mpr
        cases he : e i with
        | inl u =>
          cases u
          refine ⟨0, Finset.mem_univ _, ?_⟩
          apply e.injective
          simp [f,small,he]
        | inr p =>
          rcases p with ⟨l,b⟩
          have hl : l = j := by simpa [he] using h
          subst l
          refine ⟨b.succ, Finset.mem_univ _, ?_⟩
          apply e.injective
          simp [f,small_succ,he]
    obtain ⟨r,hr,_⟩ := local_tail_attainment k j m
    obtain ⟨R,hR⟩ := lift L F f hFL r
    refine ⟨image_full ▸ R, ?_⟩
    intro i
    exact (cast_gain image_full R _).trans ((hR i (Finset.mem_univ i)).trans (hr i))
  have completed (j : Fin k) (m : Fin 6) :
      ∃ r : Recipe F Finset.univ,
        (∀ i, gain r (e.symm (small j i)) = V m i) ∧
        (∀ l : Fin k, l ≠ j → ∀ b : Fin 4, gain r (e.symm (.inr (l,b))) = 1) := by
    obtain ⟨q,hq⟩ := local_recipes j m
    obtain ⟨r,hr,ho⟩ := FourExitScanExtension.ordinary_scan_completion k hk e {j} q
    refine ⟨r, ?_, ?_⟩
    · intro i
      rw [hr (e.symm (small j i))]
      · exact hq i
      · rw [Equiv.apply_symm_apply]
        fin_cases i <;> simp [small]
    · intro l hl b
      exact ho l (by simpa using hl) b
  have attain : ∀ v ∈ menu k, ∃ pi : Strategy,
      ∀ i, cost pi (family k i) = 8 * k + 16 + v i := by
    intro v hv
    rcases hv with ((⟨u,rfl⟩ | ⟨⟨j,b⟩,rfl⟩) | ⟨⟨j,b⟩,rfl⟩)
    · cases u
      obtain ⟨r,hr⟩ := baseline_recipe
      exact actualize r _ hr
    · obtain ⟨r,hr,ho⟩ := completed j (Fin.castAdd 3 b)
      apply actualize r
      intro i
      cases i with
      | inl u =>
        cases u
        have h := hr 0
        fin_cases b <;> simpa [small,V,endpoint] using h
      | inr p =>
        rcases p with ⟨l,c⟩
        by_cases hl : l = j
        · subst l
          have h := hr c.succ
          rw [small_succ] at h
          fin_cases b <;> fin_cases c <;> simpa [V,endpoint] using h
        · rw [ho l hl c]
          simp [endpoint,hl]
    · let tail : Fin 6 := match b.val with | 0 => 4 | 1 => 3 | _ => 5
      obtain ⟨r,hr,ho⟩ := completed j tail
      apply actualize r
      intro i
      cases i with
      | inl u =>
        cases u
        have h := hr 0
        fin_cases b <;> simpa [V,small,tail,endpointWith] using h
      | inr p =>
        rcases p with ⟨l,c⟩
        by_cases hl : l = j
        · subst l
          have h := hr c.succ
          rw [small_succ] at h
          fin_cases b <;> fin_cases c <;> simpa [V,tail,endpointWith] using h
        · rw [ho l hl c]
          simp [endpointWith,hl]
  refine ⟨fun pi => (facts.2.2.2 pi).2.2, attain, ?_, cardinality⟩
  intro v
  constructor
  · rintro ⟨⟨pi,hpi⟩,hmin⟩
    obtain ⟨w,hw,hdom⟩ := (facts.2.2.2 pi).2.2
    obtain ⟨sigma,hsigma⟩ := attain w hw
    have actual_w : ∃ sigma : Strategy,
        ∀ i, w i = cost sigma (family k i) - (8 * k + 16) := by
      exact ⟨sigma, fun i => by rw [hsigma i]; omega⟩
    have le : w ≤ v := by
      intro i
      have hd := hdom i
      rw [hpi i]
      exact Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hd)
    have eq : v = w := le_antisymm (hmin actual_w le) le
    exact eq ▸ hw
  · intro hv
    obtain ⟨pi,hpi⟩ := attain v hv
    refine ⟨⟨pi, fun i => by rw [hpi i]; omega⟩, ?_⟩
    rintro w ⟨sigma,hsigma⟩ hle
    obtain ⟨u,hu,hdom⟩ := (facts.2.2.2 sigma).2.2
    have huw : u ≤ w := by
      intro i
      have hd := hdom i
      rw [hsigma i]
      exact Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hd)
    have eq : u = v := antichain v hv u hu (le_trans huw hle)
    exact eq ▸ huw

end D5.S3.Arith.FibonacciAtomic.FourExitRawParetoSpectrum
