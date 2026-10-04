/- GID: D5/S3/Arith/FibonacciAtomic/FourExitRawDomination
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Full four-exit family structure, unique zero cost, and raw endpoint domination. -/

import D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FourExitRawDomination

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition
open ActualImageSevenLeafSeparation (thirdImage Nonconflict leafLabel A)
open FourExitRawEndpointSpectrum
open ActualJointResponseCostCore (routeTrace)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)
open scoped BigOperators

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k × Fin 4)

/-- Every original strategy lies above an endpoint of the full literal family;
its compulsory leaf cost can be attained on at most one member. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    (∀ i : Index k, Positive (family k i) ∧
      (family k i).length = 8 * k + 16 ∧ (leaves (family k i)).length = 8 * k + 16) ∧
    Function.Injective (family k) ∧
    (∀ i j : Index k, Nonconflict (family k i) (family k j)) ∧
    (∀ pi : Strategy,
      (∀ i : Index k, 8 * k + 16 ≤ cost pi (family k i)) ∧
      (∀ i j : Index k, cost pi (family k i) = 8 * k + 16 →
        cost pi (family k j) = 8 * k + 16 → i = j) ∧
      ∃ v ∈ menu k, ∀ i : Index k, 8 * k + 16 + v i ≤ cost pi (family k i)) := by
  classical
  have fold_facts : ∀ (n : Nat) (f g : Fin n → Source) (q t : Source),
      thirdImage (comb n f q) = comb n (fun i => thirdImage (f i)) (thirdImage q) ∧
      (comb n f q).length = (∑ i, (f i).length) + q.length ∧
      (comb n f q = comb n g t ↔ f = g ∧ q = t) ∧
      (Nonconflict (comb n f q) (comb n g t) ↔
        (∀ i, Nonconflict (f i) (g i)) ∧ Nonconflict q t) := by
    intro n
    induction n with
    | zero =>
      intro f g q t
      simp [comb, funext_iff]
    | succ n ih =>
      intro f g q t
      have left := ih (fun i => f i.succ) (fun i => g i.succ) q t
      have hom := Function.Semiconj₂.iterate
        (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
          substitution.map_mul) 3 (f 0) (comb n (fun i => f i.succ) q)
      refine ⟨?_, ?_, ?_, ?_⟩
      · change thirdImage (.mul _ _) = _
        change thirdImage (.mul (f 0) (comb n (fun i => f i.succ) q)) =
          .mul (thirdImage (f 0)) (thirdImage (comb n (fun i => f i.succ) q)) at hom
        rw [hom, left.1]
        rfl
      · simpa only [comb, FreeMagma.length, Fin.sum_univ_succ, Nat.add_assoc] using
          congrArg ((f 0).length + ·) left.2.1
      · constructor
        · intro he
          change FreeMagma.mul _ _ = FreeMagma.mul _ _ at he
          injection he with heads rest
          have tail := left.2.2.1.mp rest
          refine ⟨?_, tail.2⟩
          funext i
          exact Fin.cases heads (fun i => congrFun tail.1 i) i
        · rintro ⟨rfl, rfl⟩; rfl
      · change (Nonconflict (f 0) (g 0) ∧
          Nonconflict (comb n (fun i => f i.succ) q)
            (comb n (fun i => g i.succ) t)) ↔ _
        rw [left.2.2.2]
        constructor
        · rintro ⟨h0, hs, ht⟩
          exact ⟨fun i => Fin.cases h0 hs i, ht⟩
        · rintro ⟨hs, ht⟩
          exact ⟨hs 0, (fun i => hs i.succ), ht⟩
  let slot : Index k → Fin k → Source := fun i l => match i with
    | .inl _ => B
    | .inr (j,r) => if l = j then active r else B
  let tail : Index k → Source := fun i => match i with
    | .inl _ => R₀
    | .inr (_,r) => comp r
  have unfold_family (i : Index k) : family k i = comb k (slot i) (tail i) := by
    cases i <;> rfl
  have images (i : Index k) : thirdImage (preFamily k i) = family k i := by
    cases i with
    | inl u => exact (fold_facts k (fun _ => ActualImageSevenLeafSeparation.E)
        (fun _ => B) r₀ R₀).1
    | inr p =>
      rcases p with ⟨j,r⟩
      have blocks : ∀ l : Fin k,
          thirdImage (if l = j then preActive k j r else ActualImageSevenLeafSeparation.E) =
            (if l = j then active r else B) := by
        intro l
        split_ifs <;> first | (fin_cases r <;> rfl) | rfl
      have compensation : thirdImage (preComp r) = comp r := by fin_cases r <;> rfl
      change thirdImage (comb k _ _) = comb k _ _
      rw [(fold_facts k
        (fun l => if l = j then preActive k j r else ActualImageSevenLeafSeparation.E)
        (fun l => if l = j then preActive k j r else ActualImageSevenLeafSeparation.E)
        (preComp r) (preComp r)).1, compensation]
      exact congrArg (fun f => comb k f (comp r)) (funext blocks)
  have positive (i : Index k) : Positive (family k i) := ⟨preFamily k i, images i⟩
  have sizes (i : Index k) : (family k i).length = 8 * k + 16 := by
    rw [unfold_family, (fold_facts k (slot i) (slot i) (tail i) (tail i)).2.1]
    cases i with
    | inl u => simp [slot, tail, show B.length = 8 from rfl,
        show R₀.length = 16 from rfl, Nat.mul_comm]
    | inr p =>
      rcases p with ⟨j,r⟩
      have total : (active r).length + (comp r).length = 24 := by fin_cases r <;> rfl
      have blockSum : (∑ l : Fin k, (slot (.inr (j,r)) l).length) =
          (k - 1) * 8 + (active r).length := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
        have other (l : Fin k) (hl : l ∈ (Finset.univ : Finset (Fin k)).erase j) :
            (slot (.inr (j,r)) l).length = 8 := by
          simp [slot, (Finset.mem_erase.mp hl).1, show B.length = 8 from rfl]
        rw [Finset.sum_congr rfl other]
        simp [slot, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j)]
      rw [blockSum]
      change (k - 1) * 8 + (active r).length + (comp r).length = _
      omega
  have injective : Function.Injective (family k) := by
    have active_distinct : Function.Injective active := by
      intro r s h
      fin_cases r <;> fin_cases s <;> first | rfl | contradiction
    have exceptional (r : Fin 4) : active r ≠ B := by fin_cases r <;> decide
    intro i j he
    rw [unfold_family, unfold_family] at he
    have slots := (fold_facts k _ _ _ _).2.2.1.mp he |>.1
    cases i with
    | inl u =>
      cases j with
      | inl v => congr
      | inr p =>
        have h := congrFun slots p.1
        exact False.elim (exceptional p.2 (by simpa [slot] using h.symm))
    | inr p =>
      cases j with
      | inl u =>
        have h := congrFun slots p.1
        exact False.elim (exceptional p.2 (by simpa [slot] using h))
      | inr q =>
        have hj : p.1 = q.1 := by
          by_contra hne
          have h := congrFun slots p.1
          exact exceptional p.2 (by simpa [slot, hne] using h)
        have hr : p.2 = q.2 := active_distinct (by simpa [slot, hj] using congrFun slots p.1)
        exact congrArg Sum.inr (Prod.ext hj hr)
  have nonconflict (i j : Index k) : Nonconflict (family k i) (family k j) := by
    have block_nc : ∀ P ∈ ({B, A, Y, H, Z} : Finset Source),
        ∀ Q ∈ ({B, A, Y, H, Z} : Finset Source), Nonconflict P Q := by
      intro P hP Q hQ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hP hQ
      rcases hP with rfl | rfl | rfl | rfl | rfl <;>
        rcases hQ with rfl | rfl | rfl | rfl | rfl <;>
          simp only [B, H, Y, Z, A, thirdImage, t, w, h, y, z,
            ActualImageSevenLeafSeparation.E, Nonconflict]
      all_goals trivial
    have tail_nc : ∀ P ∈ ({R₀, Rₐ, B, Z, H} : Finset Source),
        ∀ Q ∈ ({R₀, Rₐ, B, Z, H} : Finset Source), Nonconflict P Q := by
      intro P hP Q hQ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hP hQ
      rcases hP with rfl | rfl | rfl | rfl | rfl <;>
        rcases hQ with rfl | rfl | rfl | rfl | rfl <;>
          simp only [B, H, Z, R₀, Rₐ, A, thirdImage, r₀, rₐ,
            t, h, z, ActualImageSevenLeafSeparation.E, Nonconflict]
      all_goals trivial
    have slot_mem (i : Index k) (l : Fin k) : slot i l ∈ ({B, A, Y, H, Z} : Finset Source) := by
      cases i with
      | inl u => simp [slot]
      | inr p =>
        rcases p with ⟨j,r⟩
        simp only [slot]
        split_ifs <;> first | (fin_cases r <;> simp [active]) | simp
    have tail_mem (i : Index k) : tail i ∈ ({R₀, Rₐ, B, Z, H} : Finset Source) := by
      cases i with
      | inl u => simp [tail]
      | inr p =>
        rcases p with ⟨j,r⟩
        fin_cases r <;> simp [tail, comp]
    rw [unfold_family, unfold_family, (fold_facts k _ _ _ _).2.2.2]
    exact ⟨fun l => block_nc _ (slot_mem i l) _ (slot_mem j l),
      tail_nc _ (tail_mem i) _ (tail_mem j)⟩
  have leaflength (i : Index k) : (leaves (family k i)).length = 8 * k + 16 := by
    have one := ActualJointResponseCostCore.result 1 (by decide) (fun _ => family k i)
      (fun _ => positive i) (fun a b _ => Subsingleton.elim a b)
    obtain ⟨v,hv⟩ := one.2.1
    obtain ⟨r,pi,_,facts⟩ := one.2.2.1 v hv
    obtain ⟨_,hp,_,_,hr,_,_,ht⟩ := facts 0
    have empty_route : routeTrace r 0 = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [empty_route] at hp ht
    simp only [paid, List.map_nil, List.toFinset_nil, Finset.empty_union,
      Finset.empty_sdiff, Finset.card_empty, Nat.add_zero] at hp ht
    exact ht.symm.trans ((congrArg Finset.card hp).trans
      ((ActualImageSevenLeafSeparation.seven_leaf_separation.1 _).1.trans (sizes i)))
  have baseline (pi : Strategy) (i : Index k) : 8 * k + 16 ≤ cost pi (family k i) := by
    have incl := source_foundation.2.2.2.2.1 pi (family k i) (positive i)
    have card := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 (family k i)).1
    exact (sizes i).symm ▸ (card ▸ Finset.card_le_card incl)
  have leaf_agreement (i j : Index k) (u : Address)
      (hi : u ∈ (leaves (family k i)).toFinset)
      (hj : u ∈ (leaves (family k j)).toFinset) :
      readout u (family k i) = readout u (family k j) := by
    obtain ⟨a,ha⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 _).2 u |>.mp hi
    obtain ⟨b,hb⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 _).2 u |>.mp hj
    have labels := (ActualImageSevenLeafSeparation.seven_leaf_separation.2.1
      (family k i) (family k j)).2.2.mp (nonconflict i j) u a b ha hb
    have he : leafLabel (family k i) u = leafLabel (family k j) u :=
      ha.trans ((congrArg some labels).trans hb.symm)
    cases hri : readout u (family k i) <;> cases hrj : readout u (family k j) <;>
      simp only [leafLabel, hri, hrj, reduceCtorEq] at ha hb he
    all_goals first | rfl | contradiction
  have unique_zero (pi : Strategy) (i j : Index k)
      (hi : cost pi (family k i) = 8 * k + 16)
      (hj : cost pi (family k j) = 8 * k + 16) : i = j := by
    have paid_eq (l : Index k) (hl : cost pi (family k l) = 8 * k + 16) :
        paid (terminal pi (family k l)).1 = (leaves (family k l)).toFinset := by
      apply Eq.symm
      apply Finset.eq_of_subset_of_card_le
      · exact source_foundation.2.2.2.2.1 pi _ (positive l)
      · change cost pi (family k l) ≤ (ActualImageSevenLeafSeparation.leafAddresses (family k l)).card
        rw [hl, (ActualImageSevenLeafSeparation.seven_leaf_separation.1 (family k l)).1, sizes l]
    have paired : ∀ (n m : Nat) (h : Hist (fun _ : Address => Reply))
        (x y : Hist (fun _ : Address => Reply) × Bool),
        execute readout pi.policy n h (family k i) = some x →
        execute readout pi.policy m h (family k j) = some y →
        paid x.1 ⊆ (leaves (family k i)).toFinset →
        paid y.1 ⊆ (leaves (family k j)).toFinset → x = y := by
      intro n
      induction n with
      | zero => intro m h x y hx; simp [execute] at hx
      | succ n ih =>
        intro m h x y hx hy hxi hyj
        cases m with
        | zero => simp [execute] at hy
        | succ m =>
          cases hp : pi.policy h with
          | inr b =>
            simp only [execute, hp, Option.some.injEq] at hx hy
            exact hx.symm.trans hy
          | inl u =>
            simp only [execute, hp, Option.map_eq_some_iff] at hx hy
            obtain ⟨x', hx', rfl⟩ := hx
            obtain ⟨y', hy', rfl⟩ := hy
            have memi : u ∈ (leaves (family k i)).toFinset := hxi (by simp [paid])
            have memj : u ∈ (leaves (family k j)).toFinset := hyj (by simp [paid])
            have eqRead := leaf_agreement i j u memi memj
            rw [← eqRead] at hy'
            have children := ih m (h ++ [⟨u, readout u (family k i)⟩]) x' y' hx' hy'
              (fun q hq => hxi (by simpa [paid] using Or.inr hq))
              (fun q hq => hyj (by simpa [paid] using Or.inr hq))
            rw [children, eqRead]
    have runi := Classical.choose_spec (Classical.choose_spec (pi.correct (family k i)))
    have runj := Classical.choose_spec (Classical.choose_spec (pi.correct (family k j)))
    have histories : terminal pi (family k i) = terminal pi (family k j) :=
      paired _ _ [] _ _ runi.1 runj.1 (paid_eq i hi ▸ Finset.Subset.refl _)
        (paid_eq j hj ▸ Finset.Subset.refl _)
    have same_leaves : (leaves (family k i)).toFinset = (leaves (family k j)).toFinset := by
      rw [← paid_eq i hi, ← paid_eq j hj, histories]
    apply injective
    apply source_foundation.2.2.1 (family k j) (family k i)
    intro u hu
    have hiu : u ∈ (leaves (family k i)).toFinset := by
      rw [same_leaves]; exact List.mem_toFinset.mpr hu
    have hju : u ∈ (leaves (family k j)).toFinset := List.mem_toFinset.mpr hu
    exact leaf_agreement i j u hiu hju
  refine ⟨fun i => ⟨positive i, sizes i, leaflength i⟩,
    injective, nonconflict, ?_⟩
  intro pi
  refine ⟨baseline pi, unique_zero pi, ?_⟩
  have positive_other (i : Index k) (hz : cost pi (family k i) = 8 * k + 16)
      (j : Index k) (hne : j ≠ i) : 8 * k + 17 ≤ cost pi (family k j) := by
    have hb := baseline pi j
    have hn : cost pi (family k j) ≠ 8 * k + 16 := fun hj => hne (unique_zero pi j i hj hz)
    omega
  by_cases exists_zero : ∃ i, cost pi (family k i) = 8 * k + 16
  · obtain ⟨i,hi⟩ := exists_zero
    cases i with
    | inl u =>
      refine ⟨endpoint k (.inl u), Or.inl (Or.inl ⟨u,rfl⟩), ?_⟩
      intro j
      by_cases h : j = .inl u
      · simpa [endpoint, h] using baseline pi j
      · simpa only [endpoint, if_neg h, Nat.add_assoc] using positive_other (.inl u) hi j h
    | inr p =>
      rcases p with ⟨j,r⟩
      refine Fin.cases ?_ (fun b => ?_) r hi
      · intro hz
        obtain ⟨b,hb⟩ := local_two_excess k j pi hz
        refine ⟨endpointWith k j b.succ, Or.inr ⟨(j,b),rfl⟩, ?_⟩
        intro i
        by_cases h0 : i = .inr (j,0)
        · simpa [endpointWith, h0] using baseline pi i
        · by_cases h2 : i = .inr (j,b.succ)
          · simpa [endpointWith, h0, h2] using hb
          · simpa only [endpointWith, if_neg h0, if_neg h2, Nat.add_assoc] using positive_other (.inr (j,0)) hz i h0
      · intro hz
        refine ⟨endpoint k (.inr (j,b.succ)), Or.inl (Or.inr ⟨(j,b),rfl⟩), ?_⟩
        intro i
        by_cases h : i = .inr (j,b.succ)
        · simpa [endpoint, h] using baseline pi i
        · simpa only [endpoint, if_neg h, Nat.add_assoc] using positive_other (.inr (j,b.succ)) hz i h
  · refine ⟨endpoint k (.inl ()), Or.inl (Or.inl ⟨(),rfl⟩), ?_⟩
    intro i
    have hb := baseline pi i
    have hn : cost pi (family k i) ≠ 8 * k + 16 := fun he => exists_zero ⟨i,he⟩
    have strong : 8 * k + 17 ≤ cost pi (family k i) := by omega
    by_cases h : i = .inl ()
    · subst i
      simpa [endpoint] using baseline pi (.inl ())
    · simpa only [endpoint, if_neg h, Nat.add_assoc] using strong

end D5.S3.Arith.FibonacciAtomic.FourExitRawDomination
