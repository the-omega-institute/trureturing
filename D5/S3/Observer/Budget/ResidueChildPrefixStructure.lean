/- GID: D5/S3/Observer/Budget/ResidueChildPrefixStructure
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/ResidueChildPrefixStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Residue protocols admit chronological child prefixes and exact family splicing. -/

import D5.S3.Observer.Budget.ResiduePosteriorClosure
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Observer.Budget.ResiduePosteriorClosure
open D5.S3.Observer.Budget.ResidueLeafOptimality
open D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
namespace D5.S3.Observer.Budget.ResidueChildPrefixStructure

/-- Chronological extraction from every identifying tree, and exact realization
of every ordered identifying child family with internal nonlast heads. -/
theorem residue_child_prefix_structure (p e d : ℕ) [Fact p.Prime] (hd : d < e)
    (b : ZMod (p ^ d)) (I : Finset (ZMod (p ^ (d + 1))))
    (hne : I.Nonempty) (hI : I ⊆ children p d b) :
    let X := ZMod (p ^ e)
    let Tree := PassiveProtocol X (fun _ => ℕ)
    let R := runPassiveProtocol (residueReadout p e)
    let C := node p e (d + 1) (Nat.succ_le_of_lt hd)
    let S := siblings p e d hd I
    let Ident := fun (A : Finset X) (T : Tree) => Set.InjOn (R T) (A : Set X)
    (∀ T : Tree, Ident S T →
      ∃ (o : Fin I.card ≃ I) (U : Fin I.card → Tree)
        (P : Fin I.card → List (Sigma (fun _ : X => ℕ)))
        (c : Fin I.card → X) (next : Fin I.card → ℕ → Tree),
        (∀ i, c i ∈ C (o i).val ∧ Ident (C (o i).val) (U i) ∧
          ((i.val + 1 < I.card ∨ (I.card = 1 ∧ d + 1 < e)) →
            U i = .query (c i) (next i)) ∧
          i.val ≤ (P i).length ∧
          ∀ a ∈ C (o i).val, R T a = P i ++ R (U i) a) ∧
        (∀ i j, i < j → (P i ++ [Sigma.mk (c i) d]).IsPrefix (P j))) ∧
    (∀ (o : Fin I.card ≃ I) (U : Fin I.card → Tree),
      (∀ i, Ident (C (o i).val) (U i)) →
      (∀ i, i.val + 1 < I.card →
        ∃ c ∈ C (o i).val, ∃ next : ℕ → Tree, U i = .query c next) →
      ∃ (c : Fin I.card → X) (next : Fin I.card → ℕ → Tree) (V : Tree),
        (∀ i, i.val + 1 < I.card → c i ∈ C (o i).val ∧ U i = .query (c i) (next i)) ∧
        Ident S V ∧ ∀ i a, a ∈ C (o i).val →
          R V a =
            (List.ofFn (fun j => (⟨c j, d⟩ : Sigma (fun _ : X => ℕ)))).take i.val ++ R (U i) a ∧
          (R V a).length = i.val + (R (U i) a).length) := by
  classical
  dsimp only
  let X := ZMod (p ^ e)
  let Tree := PassiveProtocol X (fun _ => ℕ)
  let q := residueReadout p e
  let R := runPassiveProtocol q
  let C := node p e (d + 1) (Nat.succ_le_of_lt hd)
  let S := siblings p e d hd
  let L := primePowerProjection p (Nat.succ_le_of_lt hd)
  let Ident := fun (A : Finset X) (T : Tree) => Set.InjOn (R T) (A : Set X)
  have hp : p.Prime := Fact.out
  have positive : ∀ _ : X, (0 : ℚ) < (p ^ e : ℚ)⁻¹ :=
    fun _ => inv_pos.mpr (pow_pos (by exact_mod_cast hp.pos) _)
  have normalized : ∑ _ : X, (p ^ e : ℚ)⁻¹ = 1 := by
    dsimp [X]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_pow]
    exact mul_inv_cancel₀ (ne_of_gt (pow_pos (by exact_mod_cast hp.pos) _))
  have geo := residue_posterior_closure p e (fun _ => (p ^ e : ℚ)⁻¹) positive normalized
  have threshold := geo.1
  have cards := geo.2.2.2.1
  have geom := geo.2.2.2.2.2.1
  have outside := geo.2.2.2.2.2.2.1
  clear geo positive normalized
  have cmem (z) (a : X) : a ∈ C z ↔ L a = z := by simp [C, L, node]
  have smem (J) (a : X) : a ∈ S J ↔ L a ∈ J := by simp [S, L, siblings]
  have cne (z) : (C z).Nonempty := by
    rw [← Finset.card_pos, cards]
    exact pow_pos hp.pos _
  have sub (J) (z) (hz : z ∈ J) : C z ⊆ S J :=
    fun a ha => (smem J a).2 ((cmem z a).1 ha ▸ hz)
  have inside (z) (a c : X) (ha : a ∈ C z) (hc : c ∈ C z) : q c a ≠ d := by
    have h := (threshold (d + 1) (Nat.succ_le_of_lt hd) a c).2
      (((cmem z a).1 ha).trans ((cmem z c).1 hc).symm)
    dsimp [q]; omega
  have reject (J) (valid : J ⊆ children p d b) (c : X) (hc : c ∈ S J)
      (a : X) (ha : a ∈ S (J.erase (L c))) : q c a = d := by
    have f := (geom d hd b J valid c).2.2.2 hc |>.1
    have haf : a ∈ (siblings p e d hd J).filter (fun a => residueReadout p e c a = d) := by
      rw [f]; exact ha
    exact (Finset.mem_filter.mp haf).2
  have constant (J) (ne : J.Nonempty) (valid : J ⊆ children p d b)
      (c : X) (hc : c ∉ S J) : ∃ r, ∀ a ∈ S J, q c a = r := by
    obtain ⟨r, _, hr⟩ := outside d hd b J ne valid c hc
    refine ⟨r, fun a ha => ?_⟩
    have hf : (S J).filter (fun a => q c a = r) = S J := by
      simpa only [ite_true] using hr r
    have haf : a ∈ (S J).filter (fun a => q c a = r) := by rw [hf]; exact ha
    exact (Finset.mem_filter.mp haf).2
  have extract (T : Tree) : ∀ (J : Finset (ZMod (p ^ (d + 1)))),
      J.Nonempty → J ⊆ children p d b → Ident (S J) T →
      ∃ (n : ℕ) (o : Fin n → ZMod (p ^ (d + 1))) (U : Fin n → Tree)
        (P : Fin n → List (Sigma (fun _ : X => ℕ)))
        (c : Fin n → X) (next : Fin n → ℕ → Tree),
        Function.Injective o ∧ (∀ z, z ∈ J ↔ ∃ i, o i = z) ∧
        (∀ i, c i ∈ C (o i) ∧ Ident (C (o i)) (U i) ∧
          ((i.val + 1 < n ∨ (n = 1 ∧ d + 1 < e)) → U i = .query (c i) (next i)) ∧
          i.val ≤ (P i).length ∧ ∀ a ∈ C (o i), R T a = P i ++ R (U i) a) ∧
        (∀ i j, i < j → (P i ++ [Sigma.mk (c i) d]).IsPrefix (P j)) := by
    induction T with
    | stop =>
      intro J ne valid ident
      have ss : (↑(S J) : Set X).Subsingleton := fun a ha a' ha' => ident ha ha' rfl
      obtain ⟨z, hz⟩ := ne
      obtain ⟨a, ha⟩ := cne z
      have jeq : J = {z} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hz, fun w hw => ?_⟩
        obtain ⟨a', ha'⟩ := cne w
        exact ((cmem w a').1 ha').symm.trans
          ((congrArg L (ss (sub J w hw ha') (sub J z hz ha))).trans ((cmem z a).1 ha))
      have leaf : ¬d + 1 < e := by
        intro h
        have small : (C z).card ≤ 1 := Finset.card_le_one.mpr
          (fun a ha b hb => ss (sub J z hz ha) (sub J z hz hb))
        rw [cards] at small
        have big : 1 < p ^ (e - (d + 1)) := one_lt_pow₀ hp.one_lt (by omega)
        omega
      refine ⟨1, fun _ => z, fun _ => .stop, fun _ => [], fun _ => a,
        fun _ _ => .stop, fun i j _ => Subsingleton.elim i j, ?_, ?_, ?_⟩
      · intro w; simp [jeq, eq_comm]
      · intro i
        exact ⟨ha, fun _ hx _ hy _ => ss (sub J z hz hx) (sub J z hz hy),
          fun h => False.elim (by rcases h with h | ⟨_, h⟩ <;> omega), by simp,
          fun _ _ => rfl⟩
      · intro i j h; exact False.elim (by have := i.isLt; have := j.isLt; omega)
    | query c next ih =>
      intro J ne valid ident
      by_cases hc : c ∈ S J
      · have lc : L c ∈ J := (smem J c).1 hc
        have cc : c ∈ C (L c) := (cmem _ _).2 rfl
        by_cases rem : (J.erase (L c)).Nonempty
        · have ident' : Ident (S (J.erase (L c))) (next d) := by
            intro a ha a' ha' he
            apply ident ((sub J (L a) (Finset.mem_erase.mp ((smem _ _).1 ha)).2) ((cmem _ _).2 rfl))
              ((sub J (L a') (Finset.mem_erase.mp ((smem _ _).1 ha')).2) ((cmem _ _).2 rfl))
            simp only [R, runPassiveProtocol, reject J valid c hc a ha,
              reject J valid c hc a' ha', he]
          obtain ⟨n, o, U, P, cs, ns, oi, onto, props, chron⟩ :=
            ih d _ rem ((Finset.erase_subset _ _).trans valid) ident'
          have no (i) : o i ≠ L c := (Finset.mem_erase.mp ((onto _).2 ⟨i, rfl⟩)).1
          refine ⟨n + 1, Fin.cons (L c) o, Fin.cons (.query c next) U,
            Fin.cons [] (fun i => ⟨c,d⟩ :: P i), Fin.cons c cs, Fin.cons next ns,
            Fin.cons_injective_of_injective (by rintro ⟨i, hi⟩; exact no i hi) oi, ?_, ?_, ?_⟩
          · intro z
            constructor
            · intro hz
              by_cases he : z = L c
              · exact ⟨0, by simpa using he.symm⟩
              · obtain ⟨i, hi⟩ := (onto z).1 (Finset.mem_erase.mpr ⟨he, hz⟩)
                exact ⟨i.succ, by simpa using hi⟩
            · rintro ⟨i, rfl⟩
              refine Fin.cases (by simpa using lc) (fun j => ?_) i
              simpa using (Finset.mem_erase.mp ((onto _).2 ⟨j,rfl⟩)).2
          · intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact ⟨cc, fun _ ha _ hb he => ident (sub J _ lc ha) (sub J _ lc hb) he,
                fun _ => rfl, Nat.zero_le _, fun _ _ => rfl⟩
            · obtain ⟨cj, uj, hj, len, tr⟩ := props j
              refine ⟨cj, uj, fun h => hj (Or.inl (by simp only [Fin.val_succ] at h; omega)),
                by simpa using Nat.succ_le_succ len, ?_⟩
              intro a ha
              have ar : a ∈ S (J.erase (L c)) := sub _ _ ((onto _).2 ⟨j,rfl⟩) ha
              simpa only [Fin.cons_succ, R, runPassiveProtocol, reject J valid c hc a ar,
                List.cons_append] using
                  congrArg (List.cons (⟨c,d⟩ : Sigma (fun _ : X => ℕ))) (tr a ha)
          · intro i j
            refine Fin.cases ?_ (fun i' => ?_) i
            · refine Fin.cases (fun h => False.elim (by simp at h)) (fun j' _ => ?_) j
              exact ⟨P j', rfl⟩
            · refine Fin.cases (fun h => False.elim (by simp at h)) (fun j' h => ?_) j
              obtain ⟨xs, hx⟩ := chron i' j' (by simpa using h)
              refine ⟨xs, ?_⟩
              simpa only [Fin.cons_succ, List.cons_append] using
                congrArg (List.cons ⟨c,d⟩) hx
        · have jeq : J = {L c} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨lc, fun z hz => by by_contra h; exact rem ⟨z, Finset.mem_erase.mpr ⟨h,hz⟩⟩⟩
          refine ⟨1, fun _ => L c, fun _ => .query c next, fun _ => [], fun _ => c,
            fun _ => next, fun i j _ => Subsingleton.elim i j, ?_, ?_, ?_⟩
          · intro z; simp [jeq, eq_comm]
          · intro i
            exact ⟨cc, fun _ ha _ hb he => ident (sub J _ lc ha) (sub J _ lc hb) he,
              fun _ => rfl, by simp, fun _ _ => rfl⟩
          · intro i j h; exact False.elim (by have := i.isLt; have := j.isLt; omega)
      · obtain ⟨r, hr⟩ := constant J ne valid c hc
        have ident' : Ident (S J) (next r) := by
          intro a ha a' ha' he
          apply ident ha ha'
          simp only [R, runPassiveProtocol, hr a ha, hr a' ha', he]
        obtain ⟨n,o,U,P,cs,ns,oi,onto,props,chron⟩ := ih r J ne valid ident'
        refine ⟨n,o,U,(fun i => ⟨c,r⟩ :: P i),cs,ns,oi,onto,?_,?_⟩
        · intro i
          obtain ⟨ci,ui,hi,len,tr⟩ := props i
          refine ⟨ci,ui,hi,by simp only [List.length_cons]; omega,?_⟩
          intro a ha
          simpa only [R, runPassiveProtocol, hr a (sub J _ ((onto _).2 ⟨i,rfl⟩) ha),
            List.cons_append] using congrArg (List.cons (⟨c,r⟩ : Sigma (fun _ : X => ℕ))) (tr a ha)
        · intro i j h
          obtain ⟨xs,hx⟩ := chron i j h
          exact ⟨xs, by simpa only [List.cons_append] using congrArg (List.cons ⟨c,r⟩) hx⟩
  constructor
  · intro T ident
    obtain ⟨n,o,U,P,c,next,oi,onto,props,chron⟩ := extract T I hne hI ident
    let equiv : Fin n ≃ I := Equiv.ofBijective
      (fun i => ⟨o i, (onto _).2 ⟨i,rfl⟩⟩)
      ⟨fun i j h => oi (congrArg Subtype.val h), fun z => by
        obtain ⟨i,hi⟩ := (onto z.val).1 z.property
        exact ⟨i, Subtype.ext hi⟩⟩
    have card : n = I.card := by
      simpa using Fintype.card_congr equiv
    subst n
    exact ⟨equiv,U,P,c,next,props,chron⟩
  · intro o U hu heads
    have selected : ∀ i, ∃ (c : X) (next : ℕ → Tree), i.val + 1 < I.card →
        c ∈ C (o i).val ∧ U i = .query c next := by
      intro i
      by_cases h : i.val + 1 < I.card
      · obtain ⟨c,hc,next,he⟩ := heads i h
        exact ⟨c,next,fun _ => ⟨hc,he⟩⟩
      · exact ⟨0,fun _ => .stop,fun h' => False.elim (h h')⟩
    choose c next hs using selected
    have different (z w : ZMod (p ^ (d + 1))) (hz : z ∈ children p d b)
        (hw : w ∈ children p d b) (hne : w ≠ z)
        (x a : X) (hx : x ∈ C z) (ha : a ∈ C w) : q x a = d := by
      apply reject (children p d b) (Finset.Subset.refl _) x
        ((smem _ _).2 ((cmem _ _).1 hx ▸ hz)) a
      apply (smem _ _).2
      rw [(cmem _ _).1 ha, (cmem _ _).1 hx]
      exact Finset.mem_erase.mpr ⟨hne,hw⟩
    have build : ∀ n (o : Fin (n + 1) → ZMod (p ^ (d + 1)))
        (U : Fin (n + 1) → Tree) (c : Fin (n + 1) → X)
        (next : Fin (n + 1) → ℕ → Tree),
        Function.Injective o → (∀ i, o i ∈ children p d b) →
        (∀ i, Ident (C (o i)) (U i)) →
        (∀ i, i.val + 1 < n + 1 → c i ∈ C (o i) ∧ U i = .query (c i) (next i)) →
        ∃ V : Tree,
          (∀ i j a, a ∈ C (o i) → ∀ b, b ∈ C (o j) → R V a = R V b → a = b) ∧
          ∀ i a, a ∈ C (o i) → R V a =
            (List.ofFn (fun j => (⟨c j,d⟩ : Sigma (fun _ : X => ℕ)))).take i.val ++ R (U i) a := by
      intro n
      induction n with
      | zero =>
        intro o U c next oi valid hu hs
        refine ⟨U 0, ?_, ?_⟩
        · intro i j a ha b hb he
          have hi : i = 0 := by apply Fin.ext; simp
          have hj : j = 0 := by apply Fin.ext; simp
          subst i; subst j
          exact hu 0 ha hb he
        · intro i a ha
          have hi : i = 0 := by apply Fin.ext; simp
          subst i; simp
      | succ n ih =>
        intro o U c next oi valid hu hs
        obtain ⟨W, sep, tr⟩ := ih (fun i => o i.succ) (fun i => U i.succ)
          (fun i => c i.succ) (fun i => next i.succ)
          (oi.comp (Fin.succ_injective _)) (fun i => valid i.succ) (fun i => hu i.succ)
          (fun i h => hs i.succ (by simpa only [Fin.val_succ] using Nat.succ_lt_succ h))
        obtain ⟨hc, head⟩ := hs 0 (by simp)
        let V : Tree := .query (c 0) (fun r => if r = d then W else next 0 r)
        have yes (a : X) (ha : a ∈ C (o 0)) : R V a = R (U 0) a := by
          rw [head]
          simp only [V,R,runPassiveProtocol,if_neg (inside _ a (c 0) ha hc)]
        have no (i : Fin (n + 1)) (a : X) (ha : a ∈ C (o i.succ)) :
            R V a = ⟨c 0,d⟩ :: R W a := by
          have r := different (o 0) (o i.succ) (valid 0) (valid i.succ)
            (fun h => Fin.succ_ne_zero i (oi h)) (c 0) a hc ha
          simp only [V,R,runPassiveProtocol,r,ite_true]
        refine ⟨V,?_,?_⟩
        · intro i j
          refine Fin.cases ?_ (fun i' => ?_) i
          · refine Fin.cases ?_ (fun j' => ?_) j
            · intro a ha b hb he
              exact hu 0 ha hb ((yes a ha).symm.trans (he.trans (yes b hb)))
            · intro a ha b hb he
              rw [yes a ha, no j' b hb, head] at he
              have eqr := congrArg (fun z : Sigma (fun _ : X => ℕ) => z.2) (List.cons.inj he).1
              exact False.elim (inside _ a (c 0) ha hc eqr)
          · refine Fin.cases ?_ (fun j' => ?_) j
            · intro a ha b hb he
              rw [no i' a ha, yes b hb, head] at he
              have eqr := congrArg (fun z : Sigma (fun _ : X => ℕ) => z.2) (List.cons.inj he).1
              exact False.elim (inside _ b (c 0) hb hc eqr.symm)
            · intro a ha b hb he
              rw [no i' a ha, no j' b hb] at he
              exact sep i' j' a ha b hb (List.cons.inj he).2
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · intro a ha; simpa using yes a ha
          · intro a ha
            rw [no j a ha, tr j a ha]
            simp only [List.ofFn_succ, Fin.val_succ, List.take_succ_cons, List.cons_append]
    have kp : 0 < I.card := Finset.card_pos.mpr hne
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt kp)
    generalize hk : I.card = k at o U hu c next hs ⊢
    have kn : k = n + 1 := hk.symm.trans hn
    clear hk
    subst k
    obtain ⟨V, sep, tr⟩ := build n (fun i => (o i).val) U c next
      (Subtype.val_injective.comp o.injective) (fun i => hI (o i).property) hu hs
    refine ⟨c,next,V,hs,?_,?_⟩
    · intro a ha b hb he
      obtain ⟨i, hi⟩ := o.surjective ⟨L a, (smem I a).1 ha⟩
      obtain ⟨j, hj⟩ := o.surjective ⟨L b, (smem I b).1 hb⟩
      exact sep i j a ((cmem _ _).2 (congrArg Subtype.val hi).symm)
        b ((cmem _ _).2 (congrArg Subtype.val hj).symm) he
    · intro i a ha
      refine ⟨tr i a ha, ?_⟩
      change (R V a).length = i.val + (R (U i) a).length
      rw [tr i a ha, List.length_append, List.length_take, List.length_ofFn,
        Nat.min_eq_left (Nat.le_of_lt i.isLt)]

#print axioms residue_child_prefix_structure

end D5.S3.Observer.Budget.ResidueChildPrefixStructure
