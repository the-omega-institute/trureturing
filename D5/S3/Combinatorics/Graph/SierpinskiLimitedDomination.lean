/- GID: D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SierpinskiLimitedDomination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Božović Conjecture 12: limited domination in Sierpiński graphs has an exact sharp value. -/

/- Public theorem judgement:
   claim: proof_shape: definition; escape_witness: none
   result: proof_shape: content; escape_witness: color_link, color_fiber_bijective, adjacent_empty_bonus, group_lower_bound; admission_basis: open-problem-resolution (#12456; Proved)
   Direct frozen definition dependency: SimpleGraph.IsDominating in GraphCoverDomination.
   Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import D5.S3.ConceptDynamics.GraphColoring.GraphCoverDomination
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.SierpinskiLimitedDomination


def sierAdj (r m : ℕ) (u v : (Fin (r + 1) → Fin m)) : Prop :=
  ∃ h : Fin (r + 1),
    (∀ t : Fin (r + 1), t < h → u t = v t) ∧
    u h ≠ v h ∧
    (∀ t : Fin (r + 1), h < t → u t = v h ∧ v t = u h)

def sierGraph (r m : ℕ) : SimpleGraph ((Fin (r + 1) → Fin m)) where
  Adj := sierAdj r m
  symm := ⟨fun u v huv => by
    rcases huv with ⟨h, hp, hd, hs⟩
    exact ⟨h, fun t ht => (hp t ht).symm, hd.symm,
      fun t ht => ⟨(hs t ht).2, (hs t ht).1⟩⟩⟩
  loopless := ⟨fun u huv => by
    rcases huv with ⟨h, _, hd, _⟩
    exact hd rfl⟩

noncomputable def isKLimited {r m k : ℕ} (D : Finset ((Fin (r + 1) → Fin m))) : Prop :=
  by
    classical
    exact (sierGraph r m).IsDominating (D : Set (Fin (r + 1) → Fin m)) ∧
      ∀ u ∈ D, (((sierGraph r m).neighborFinset u) \ D).card ≤ k

noncomputable def gamma (r m k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ D : Finset ((Fin (r + 1) → Fin m)), isKLimited (r := r) (m := m) (k := k) D ∧ D.card = n}

private def fiber {r m : ℕ} (D : Finset ((Fin (r + 1) → Fin m))) (p : (Fin r → Fin m)) : Finset ((Fin (r + 1) → Fin m)) :=
  D.filter (fun u => Fin.init u = p)

def claim : Prop := ∀ n m k : ℕ, 1 ≤ n → 2 ≤ m → 1 ≤ k → k ≤ m - 1 →
  gamma (n - 1) m k = (m - k) * m ^ (n - 1)


private noncomputable def color (m : ℕ) : (r : ℕ) → (Fin (r + 1) → Fin m) → ZMod m
  | 0, u => (u (Fin.last 0) : ZMod m)
  | r+1, u => 2 * color m r (Fin.init u) - (u (Fin.last r).castSucc : ZMod m) +
      (u (Fin.last (r+1)) : ZMod m)



private noncomputable def upperD (r m k : ℕ) : Finset ((Fin (r + 1) → Fin m)) :=
  by classical exact Finset.univ.filter (fun u => (color m r u).val < m-k)



private noncomputable def colorLabel (r m : ℕ) [NeZero m] (p : (Fin r → Fin m)) (a : Fin m) : Fin m :=
  ⟨(color m r (Fin.snoc (α := fun _ => Fin m) p a)).val, ZMod.val_lt _⟩



private noncomputable def missing {r m : ℕ} (D : Finset ((Fin (r + 1) → Fin m))) (p : (Fin r → Fin m)) : Finset (Fin m) :=
  by classical exact Finset.univ.filter (fun a => Fin.snoc (α := fun _ => Fin m) p a ∉ D)



theorem result : claim := by
  classical
  let word_init {r m : ℕ} (p : (Fin r → Fin m)) (a : Fin m) : Fin.init (Fin.snoc (α := fun _ => Fin m) p a : Fin (r + 1) → Fin m) = p := by
    funext i
    simp [Fin.init]


  let word_last {r m : ℕ} (p : (Fin r → Fin m)) (a : Fin m) : (Fin.snoc (α := fun _ => Fin m) p a : Fin (r + 1) → Fin m) (Fin.last r) = a := by
    simp only [Fin.snoc_last]


  let word_eta {r m : ℕ} (u : (Fin (r + 1) → Fin m)) : Fin.snoc (α := fun _ => Fin m) (Fin.init u) (u (Fin.last r)) = u := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.init]


  let word_injective {r m : ℕ} : Function.Injective (fun x : (Fin r → Fin m) × Fin m => Fin.snoc (α := fun _ => Fin m) x.1 x.2) := by
    rintro ⟨p, a⟩ ⟨q, b⟩ h
    have hp : p = q := by
      funext i
      have := congrFun h i.castSucc
      simpa using this
    have ha : a = b := by
      have := congrFun h (Fin.last r)
      simpa using this
    simp [hp, ha]


  let external_at_most_one (r m : ℕ) (u v w : (Fin (r + 1) → Fin m))
      (huv : sierAdj r m u v) (huw : sierAdj r m u w)
      (hvbase : Fin.init v ≠ Fin.init u) (hwbase : Fin.init w ≠ Fin.init u) : v = w := by
    rcases huv with ⟨h, hp, hd, hs⟩
    rcases huw with ⟨j, hq, he, ht⟩
    have hn_h : h ≠ Fin.last r := by
      intro hh
      apply hvbase
      funext i
      have := hp i.castSucc (by simp [hh])
      change v i.castSucc = u i.castSucc
      exact this.symm
    have hn_j : j ≠ Fin.last r := by
      intro hj
      apply hwbase
      funext i
      have := hq i.castSucc (by simp [hj])
      change w i.castSucc = u i.castSucc
      exact this.symm
    rcases lt_trichotomy h j with hlt | heq | hgt
    · have uhj : u j = v h := (hs j (by exact hlt)).1
      have ulastv : u (Fin.last r) = v h :=
        (hs (Fin.last r) (Fin.lt_last_iff_ne_last.mpr hn_h)).1
      have ujlast : u j = u (Fin.last r) := uhj.trans ulastv.symm
      exact False.elim (he (ujlast.trans (ht (Fin.last r) (Fin.lt_last_iff_ne_last.mpr hn_j)).1))
    · subst j
      have hvh : v h = u (Fin.last r) := (hs (Fin.last r) (Fin.lt_last_iff_ne_last.mpr hn_h)).1.symm
      have hwh : w h = u (Fin.last r) := (ht (Fin.last r) (Fin.lt_last_iff_ne_last.mpr hn_h)).1.symm
      funext t
      by_cases hlt : t < h
      · exact (hp t hlt).symm.trans (hq t hlt)
      · by_cases hEq : t = h
        · subst t; exact hvh.trans hwh.symm
        · have hgt : h < t := by omega
          exact (hs t hgt).2.trans (ht t hgt).2.symm
    · have ujh : u h = w j := (ht h (by exact hgt)).1
      have ulastw : u (Fin.last r) = w j :=
        (ht (Fin.last r) (Fin.lt_last_iff_ne_last.mpr hn_j)).1
      have uhlast : u h = u (Fin.last r) := ujh.trans ulastw.symm
      exact False.elim (hd (uhlast.trans (hs (Fin.last r) (Fin.lt_last_iff_ne_last.mpr hn_h)).1))


  let univ_kLimited (r m k : ℕ) : isKLimited (r := r) (m := m) (k := k) Finset.univ := by
    constructor
    · intro v
      exact Or.inl (Finset.mem_univ v)
    · intro u hu
      rw [Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)]
      simp


  let gamma_le (r m k : ℕ) (D : Finset ((Fin (r + 1) → Fin m))) (hD : isKLimited (r := r) (m := m) (k := k) D) :
      gamma r m k ≤ D.card := by
    exact Nat.sInf_le ⟨D, hD, rfl⟩


  let gamma_attained (r m k : ℕ) :
      ∃ D : Finset ((Fin (r + 1) → Fin m)), isKLimited (r := r) (m := m) (k := k) D ∧ D.card = gamma r m k := by
    have hne : {n : ℕ | ∃ D : Finset ((Fin (r + 1) → Fin m)),
        isKLimited (r := r) (m := m) (k := k) D ∧ D.card = n}.Nonempty :=
      ⟨Finset.univ.card, Finset.univ, univ_kLimited r m k, rfl⟩
    exact Nat.sInf_mem hne


  let card_sum_fiber (r m : ℕ) (D : Finset ((Fin (r + 1) → Fin m))) :
      D.card = ∑ p : (Fin r → Fin m), (fiber D p).card := by
    classical
    simpa [fiber] using
      (Finset.card_eq_sum_card_fiberwise
        (s := D) (t := (Finset.univ : Finset ((Fin r → Fin m))))
        (f := Fin.init) (by intro u hu; simp))


  let fiber_card_le (r m : ℕ) (D : Finset ((Fin (r + 1) → Fin m))) (p : (Fin r → Fin m)) :
      (fiber D p).card ≤ m := by
    classical
    let F := fiber D p
    have hinj : Set.InjOn (fun u : (Fin (r + 1) → Fin m) => u (Fin.last r)) (↑F : Set ((Fin (r + 1) → Fin m))) := by
      intro u hu v hv huv
      have hpu : Fin.init u = p := (Finset.mem_filter.mp hu).2
      have hpv : Fin.init v = p := (Finset.mem_filter.mp hv).2
      calc
        u = Fin.snoc (α := fun _ => Fin m) (Fin.init u) (u (Fin.last r)) := (word_eta u).symm
        _ = Fin.snoc (α := fun _ => Fin m) (Fin.init v) (v (Fin.last r)) := by
          rw [hpu.trans hpv.symm]
          exact congrArg (Fin.snoc (α := fun _ => Fin m) (Fin.init v)) huv
        _ = v := word_eta v
    have himage : (F.image (fun u : (Fin (r + 1) → Fin m) => u (Fin.last r))).card = F.card :=
      Finset.card_image_of_injOn hinj
    rw [← himage]
    have hle := Finset.card_le_card
      (Finset.image_subset_iff.mpr (fun _ _ => Finset.mem_univ _)
        : F.image (fun u : (Fin (r + 1) → Fin m) => u (Fin.last r)) ⊆ Finset.univ)
    simpa using hle


  let fiber_card_eq_count (r m : ℕ) (D : Finset ((Fin (r + 1) → Fin m))) (p : (Fin r → Fin m)) :
      (fiber D p).card = (Finset.univ.filter (fun a : Fin m => Fin.snoc (α := fun _ => Fin m) p a ∈ D)).card := by
    classical
    let F := fiber D p
    have e : F.image (fun u : (Fin (r + 1) → Fin m) => u (Fin.last r)) =
        Finset.univ.filter (fun a : Fin m => Fin.snoc (α := fun _ => Fin m) p a ∈ D) := by
      ext a
      constructor
      · intro ha
        rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
        have hpu : Fin.init u = p := (Finset.mem_filter.mp hu).2
        have hueta : Fin.snoc (α := fun _ => Fin m) p (u (Fin.last r)) = u := by
          rw [← hpu]
          exact word_eta u
        have huD : u ∈ D := (Finset.mem_filter.mp hu).1
        have hwordD : Fin.snoc (α := fun _ => Fin m) p (u (Fin.last r)) ∈ D := by simpa [hueta] using huD
        simpa using hwordD
      · intro ha
        have haD : Fin.snoc (α := fun _ => Fin m) p a ∈ D := (Finset.mem_filter.mp ha).2
        have hpref : Fin.init (Fin.snoc (α := fun _ => Fin m) p a : Fin (r + 1) → Fin m) = p := word_init p a
        exact Finset.mem_image.mpr ⟨Fin.snoc (α := fun _ => Fin m) p a, Finset.mem_filter.mpr ⟨haD, hpref⟩, word_last p a⟩
    rw [← e, Finset.card_image_of_injOn]
    exact (by
      intro u hu v hv huv
      have hpu : Fin.init u = p := (Finset.mem_filter.mp hu).2
      have hpv : Fin.init v = p := (Finset.mem_filter.mp hv).2
      calc
        u = Fin.snoc (α := fun _ => Fin m) (Fin.init u) (u (Fin.last r)) := (word_eta u).symm
        _ = Fin.snoc (α := fun _ => Fin m) (Fin.init v) (v (Fin.last r)) := by
          rw [hpu.trans hpv.symm]
          exact congrArg (Fin.snoc (α := fun _ => Fin m) (Fin.init v)) huv
        _ = v := word_eta v)


  let mem_neighbor {r m : ℕ} (u v : (Fin (r + 1) → Fin m)) :
      v ∈ (sierGraph r m).neighborFinset u ↔ sierAdj r m u v := by
    classical
    exact (sierGraph r m).mem_neighborFinset u v


  let adj_same_prefix {r m : ℕ} (p : (Fin r → Fin m)) (a b : Fin m) (hab : a ≠ b) :
      sierAdj r m (Fin.snoc (α := fun _ => Fin m) p a) (Fin.snoc (α := fun _ => Fin m) p b) := by
    refine ⟨Fin.last r, ?_, ?_, ?_⟩
    · intro t ht
      have hn : t ≠ Fin.last r := ne_of_lt ht
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hn
      simp
    · simpa using hab
    · intro t ht
      have htbound := t.isLt
      simp only [Fin.lt_def, Fin.val_last] at ht
      omega


  let prefix_ne_witness {r m : ℕ} {u v : (Fin (r + 1) → Fin m)} {h : Fin (r+1)}
      (hp : ∀ t, t < h → u t = v t) (hne : Fin.init u ≠ Fin.init v) : h ≠ Fin.last r := by
    intro heq
    apply hne
    funext i
    exact hp i.castSucc (by simp [heq])


  let adj_prefix {r m : ℕ} {u v : (Fin ((r+1) + 1) → Fin m)}
      (huv : sierAdj (r+1) m u v) (hne : Fin.init u ≠ Fin.init v) :
      sierAdj r m (Fin.init u) (Fin.init v) := by
    rcases huv with ⟨h, hp, hd, hs⟩
    have hh : h ≠ Fin.last (r+1) := prefix_ne_witness hp hne
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hh
    refine ⟨j, ?_, hd, ?_⟩
    · intro t ht
      exact hp t.castSucc ht
    · intro t ht
      exact hs t.castSucc ht


  let color_link (r m : ℕ) (u v : (Fin (r + 1) → Fin m)) (huv : sierAdj r m u v)
      (hne : Fin.init u ≠ Fin.init v) : color m r u = color m r v := by
    induction r with
    | zero =>
      exact False.elim (hne (Subsingleton.elim _ _))
    | succ r ih =>
      rcases huv with ⟨h, hp, hd, hs⟩
      have hh : h ≠ Fin.last (r+1) := prefix_ne_witness hp hne
      obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hh
      by_cases hj : j = Fin.last r
      · subst j
        have hpref : Fin.init (Fin.init u) = Fin.init (Fin.init v) := by
          funext i
          exact hp i.castSucc.castSucc (by simp)
        have hc : ∃ z : ZMod m, color m r (Fin.init u) = z + (u (Fin.last r).castSucc : ZMod m) ∧
            color m r (Fin.init v) = z + (v (Fin.last r).castSucc : ZMod m) := by
          cases r with
          | zero => exact ⟨0, by simp [color, Fin.init], by simp [color, Fin.init]⟩
          | succ s =>
            have hprev : u (Fin.last s).castSucc.castSucc = v (Fin.last s).castSucc.castSucc :=
              congrFun hpref (Fin.last s)
            refine ⟨2 * color m s (Fin.init (Fin.init u)) - (u (Fin.last s).castSucc.castSucc : ZMod m),
              rfl, ?_⟩
            simp only [color, Fin.init]
            rw [← hpref, ← hprev]
        rcases hc with ⟨z, hu, hv⟩
        have huL := (hs (Fin.last (r+1)) (by simp)).1
        have hvL := (hs (Fin.last (r+1)) (by simp)).2
        simp only [color]
        rw [hu, hv, huL, hvL]
        ring
      · have hpv : Fin.init (Fin.init u) ≠ Fin.init (Fin.init v) := by
          intro heq
          obtain ⟨t, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
          exact hd (congrFun heq t)
        have hprefix : sierAdj r m (Fin.init u) (Fin.init v) :=
          ⟨j, fun t ht => hp t.castSucc ht, hd, fun t ht => hs t.castSucc ht⟩
        have hcol := ih (Fin.init u) (Fin.init v) hprefix hpv
        have hjlast : j < Fin.last r := Fin.lt_last_iff_ne_last.mpr hj
        have huu := (hs (Fin.last r).castSucc hjlast).1
        have hvv := (hs (Fin.last r).castSucc hjlast).2
        have huL := (hs (Fin.last (r+1)) (by simp)).1
        have hvL := (hs (Fin.last (r+1)) (by simp)).2
        simp only [color]
        rw [hcol, huu, hvv, huL, hvL]
        ring


  let color_fiber_shift (r m : ℕ) (p : (Fin r → Fin m)) :
      ∃ z : ZMod m, ∀ a : Fin m, color m r (Fin.snoc (α := fun _ => Fin m) p a) = z + (a : ZMod m) := by
    cases r with
    | zero =>
      refine ⟨0, fun a => ?_⟩
      change (Fin.snoc (α := fun _ => Fin m) p a (Fin.last 0) : ZMod m) = 0 + (a : ZMod m)
      rw [zero_add (a : ZMod m)]
      exact congrArg (fun b : Fin m => (b : ZMod m)) (word_last p a)
    | succ r =>
      exact ⟨2 * color m r p - (p (Fin.last r) : ZMod m),
        fun a => by simp [color, word_init]⟩


  let color_fiber_bijective (r m : ℕ) [NeZero m] (p : (Fin r → Fin m)) :
      Function.Bijective (fun a : Fin m => color m r (Fin.snoc (α := fun _ => Fin m) p a)) := by
    rcases color_fiber_shift r m p with ⟨z, hz⟩
    constructor
    · intro a b hab
      change color m r (Fin.snoc (α := fun _ => Fin m) p a) = color m r (Fin.snoc (α := fun _ => Fin m) p b) at hab
      rw [hz a, hz b] at hab
      have hcast : (a : ZMod m) = (b : ZMod m) := add_left_cancel hab
      apply Fin.ext
      have hval := congrArg ZMod.val hcast
      simpa [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using hval
    · intro x
      let a : Fin m := ⟨(x-z).val, ZMod.val_lt _⟩
      refine ⟨a, ?_⟩
      change color m r (Fin.snoc (α := fun _ => Fin m) p a) = x
      rw [hz a]
      change z + (((x-z).val : ℕ) : ZMod m) = x
      rw [ZMod.natCast_zmod_val]
      abel



  let adj_same_base {r m : ℕ} {u v : (Fin (r + 1) → Fin m)} (hp : Fin.init u = Fin.init v)
      (hne : u ≠ v) : sierAdj r m u v := by
    have hd : u (Fin.last r) ≠ v (Fin.last r) := by
      intro hh
      apply hne
      rw [← word_eta u, ← word_eta v, hp, hh]
    rw [← word_eta u, ← word_eta v, hp]
    exact adj_same_prefix _ _ _ hd


  let mem_upperD {r m k : ℕ} {u : (Fin (r + 1) → Fin m)} :
      u ∈ upperD r m k ↔ (color m r u).val < m-k := by
    classical
    simp [upperD]


  let card_fin_lt (m s : ℕ) (hs : s ≤ m) :
      (Finset.univ.filter (fun a : Fin m => a.val < s)).card = s := by
    classical
    calc
      _ = (Finset.univ : Finset (Fin s)).card := by
        apply Finset.card_bij (fun a ha => (⟨a.val, (Finset.mem_filter.mp ha).2⟩ : Fin s))
        · intro a ha; simp
        · intro a ha b hb hab
          exact Fin.ext (congrArg (fun x : Fin s => x.val) hab)
        · intro b hb
          let a : Fin m := ⟨b.val, lt_of_lt_of_le b.isLt hs⟩
          exact ⟨a, by simp [a], rfl⟩
      _ = s := by simp


  let colorLabel_bijective (r m : ℕ) [NeZero m] (p : (Fin r → Fin m)) :
      Function.Bijective (colorLabel r m p) := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_, rfl⟩
    intro a b hab
    apply (color_fiber_bijective r m p).1
    apply ZMod.val_injective m
    exact congrArg Fin.val hab


  let upper_fiber_card (r m k : ℕ) [NeZero m] (p : (Fin r → Fin m)) :
      (fiber (upperD r m k) p).card = m-k := by
    classical
    rw [fiber_card_eq_count]
    calc
      _ = (Finset.univ.filter (fun a : Fin m => a.val < m-k)).card := by
        apply Finset.card_bijective (colorLabel r m p) (colorLabel_bijective r m p)
        intro a
        simpa [colorLabel] using (mem_upperD (u := Fin.snoc (α := fun _ => Fin m) p a))
      _ = m-k := card_fin_lt m (m-k) (Nat.sub_le _ _)


  let upper_card (r m k : ℕ) [NeZero m] :
      (upperD r m k).card = (m-k) * m^r := by
    rw [card_sum_fiber]
    simp [upper_fiber_card, mul_comm]


  let mem_missing {r m : ℕ} (D : Finset ((Fin (r + 1) → Fin m))) (p : (Fin r → Fin m)) (a : Fin m) :
      a ∈ missing D p ↔ Fin.snoc (α := fun _ => Fin m) p a ∉ D := by
    classical
    simp [missing]


  let missing_card (r m : ℕ) (D : Finset ((Fin (r + 1) → Fin m))) (p : (Fin r → Fin m)) :
      (missing D p).card = m - (fiber D p).card := by
    classical
    rw [fiber_card_eq_count]
    have heq : missing D p = Finset.univ \ (Finset.univ.filter (fun a : Fin m => Fin.snoc (α := fun _ => Fin m) p a ∈ D)) := by
      ext a
      rw [mem_missing]
      simp
    rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp


  let word_inj (r m : ℕ) (p : (Fin r → Fin m)) : Function.Injective (Fin.snoc (α := fun _ => Fin m) p) := by
    intro a b hab
    have h := congrFun hab (Fin.last r)
    simpa using h


  let upper_dominating (r m k : ℕ) [NeZero m] (hk : k < m) :
      (sierGraph r m).IsDominating (upperD r m k : Set (Fin (r + 1) → Fin m)) := by
    classical
    intro v
    by_cases hv : v ∈ upperD r m k
    · exact Or.inl hv
    apply Or.inr
    obtain ⟨a, ha⟩ := (color_fiber_bijective r m (Fin.init v)).2 0
    have hwD : Fin.snoc (α := fun _ => Fin m) (Fin.init v) a ∈ upperD r m k := by
      apply mem_upperD.mpr
      have hzero : color m r (Fin.snoc (α := fun _ => Fin m) (Fin.init v) a) = 0 := by
        exact ha
      rw [hzero]
      simpa using Nat.sub_pos_of_lt hk
    refine ⟨Fin.snoc (α := fun _ => Fin m) (Fin.init v) a, hwD, ?_⟩
    apply adj_same_base
    · simp [word_init]
    · intro heq
      exact hv (heq.symm ▸ hwD)


  let upper_limited (r m k : ℕ) [NeZero m] (hkm : k ≤ m) :
      ∀ u ∈ upperD r m k, (((sierGraph r m).neighborFinset u) \ upperD r m k).card ≤ k := by
    classical
    intro u hu
    have hsub : ((sierGraph r m).neighborFinset u) \ upperD r m k ⊆
        (missing (upperD r m k) (Fin.init u)).image (Fin.snoc (α := fun _ => Fin m) (Fin.init u)) := by
      intro v hv
      rcases Finset.mem_sdiff.mp hv with ⟨hadj, hvD⟩
      have hbase : Fin.init u = Fin.init v := by
        by_contra hne
        have hc := color_link r m u v (mem_neighbor _ _ |>.mp hadj) hne
        exact hvD (mem_upperD.mpr (hc ▸ mem_upperD.mp hu))
      refine Finset.mem_image.mpr ⟨v (Fin.last r), ?_, ?_⟩
      · apply (mem_missing _ _ _).mpr
        simpa [hbase, word_eta] using hvD
      · rw [hbase, word_eta]
    have hcount : (missing (upperD r m k) (Fin.init u)).card = k := by
      rw [missing_card, upper_fiber_card, Nat.sub_sub_self hkm]
    calc
      _ ≤ ((missing (upperD r m k) (Fin.init u)).image (Fin.snoc (α := fun _ => Fin m) (Fin.init u))).card := Finset.card_le_card hsub
      _ = (missing (upperD r m k) (Fin.init u)).card :=
        Finset.card_image_of_injective _ (word_inj r m (Fin.init u))
      _ = k := hcount


  let upper_bound (r m k : ℕ) [NeZero m] (hk : k < m) :
      gamma r m k ≤ (m-k) * m^r := by
    rw [← upper_card]
    exact gamma_le r m k (upperD r m k)
      ⟨upper_dominating r m k hk, upper_limited r m k hk.le⟩



  let internal_missing_subset (r m : ℕ) (D : Finset ((Fin (r + 1) → Fin m)))
      (p : (Fin r → Fin m)) (u : (Fin (r + 1) → Fin m)) (hu : u ∈ D) (hpu : Fin.init u = p) :
      (missing D p).image (Fin.snoc (α := fun _ => Fin m) p) ⊆ ((sierGraph r m).neighborFinset u) \ D := by
    classical
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    have haD := (mem_missing D p a).mp ha
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_neighbor _ _ |>.mpr ?_, haD⟩
    apply adj_same_base
    · simpa [word_init] using hpu
    · intro heq
      exact haD (heq ▸ hu)


  let internal_missing_card (r m : ℕ) (D : Finset ((Fin (r + 1) → Fin m))) (p : (Fin r → Fin m)) :
      ((missing D p).image (Fin.snoc (α := fun _ => Fin m) p)).card = m - (fiber D p).card := by
    classical
    rw [Finset.card_image_of_injective _ (word_inj r m p), missing_card]


  let nonempty_fiber_lower (r m k : ℕ) (D : Finset ((Fin (r + 1) → Fin m)))
      (hD : isKLimited (k := k) D) (p : (Fin r → Fin m)) (hne : (fiber D p).Nonempty) :
      m-k ≤ (fiber D p).card := by
    classical
    obtain ⟨u, hu⟩ := hne
    obtain ⟨huD, hup⟩ := Finset.mem_filter.mp hu
    have hc := (Finset.card_le_card (internal_missing_subset r m D p u huD hup)).trans (hD.2 u huD)
    rw [internal_missing_card] at hc
    omega


  let external_fiber_bonus (r m k : ℕ) (hk : k < m) (D : Finset ((Fin (r + 1) → Fin m)))
      (hD : isKLimited (k := k) D) (p : (Fin r → Fin m)) (u v : (Fin (r + 1) → Fin m))
      (hu : u ∈ D) (hpu : Fin.init u = p) (hadj : sierAdj r m u v)
      (hv : v ∉ D) (hpv : Fin.init v ≠ p) :
      m-k+1 ≤ (fiber D p).card := by
    classical
    have hvm : v ∉ (missing D p).image (Fin.snoc (α := fun _ => Fin m) p) := by
      intro hvf
      obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hvf
      exact hpv (heq ▸ word_init p a)
    have hsub : insert v ((missing D p).image (Fin.snoc (α := fun _ => Fin m) p)) ⊆ ((sierGraph r m).neighborFinset u) \ D := by
      apply Finset.insert_subset
      · exact Finset.mem_sdiff.mpr ⟨(mem_neighbor _ _).mpr hadj, hv⟩
      · exact internal_missing_subset r m D p u hu hpu
    have hc := (Finset.card_le_card hsub).trans (hD.2 u hu)
    rw [Finset.card_insert_of_notMem hvm, internal_missing_card] at hc
    omega


  let empty_fiber_not_mem (r m : ℕ) (D : Finset ((Fin (r + 1) → Fin m))) (p : (Fin r → Fin m))
      (he : (fiber D p).card = 0) (u : (Fin (r + 1) → Fin m)) (hup : Fin.init u = p) : u ∉ D := by
    classical
    intro hu
    have hf : u ∈ fiber D p := Finset.mem_filter.mpr ⟨hu, hup⟩
    rw [Finset.card_eq_zero.mp he] at hf
    simp at hf


  let empty_forces_link_endpoint (r m k : ℕ) (D : Finset ((Fin (r + 1) → Fin m)))
      (hD : isKLimited (k := k) D) (p : (Fin r → Fin m)) (he : (fiber D p).card = 0)
      (u v : (Fin (r + 1) → Fin m)) (hup : Fin.init u = p) (hadj : sierAdj r m u v)
      (hvp : Fin.init v ≠ p) : v ∈ D := by
    classical
    have huD := empty_fiber_not_mem r m D p he u hup
    obtain ⟨w, hwD, huw⟩ := (hD.1 u).resolve_left huD
    have hwp : Fin.init w ≠ p := by
      intro heq
      exact empty_fiber_not_mem r m D p he w heq hwD
    have hvw : v = w := external_at_most_one r m u v w hadj huw
      (by simpa [hup] using hvp) (by simpa [hup] using hwp)
    exact hvw.symm ▸ hwD


  let lift_adj {r m : ℕ} {p q : (Fin (r + 1) → Fin m)} {h : Fin (r+1)}
      (hp : ∀ t, t < h → p t = q t) (hd : p h ≠ q h)
      (hs : ∀ t, h < t → p t = q h ∧ q t = p h) :
      sierAdj (r+1) m (Fin.snoc (α := fun _ => Fin m) p (q h)) (Fin.snoc (α := fun _ => Fin m) q (p h)) := by
    refine ⟨h.castSucc, ?_, ?_, ?_⟩
    · intro t ht
      have htne : t ≠ Fin.last (r+1) := by
        intro heq
        subst t
        have hv := h.isLt
        simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at ht
        omega
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last htne
      simpa using hp i ht
    · simpa using hd
    · intro t
      refine Fin.lastCases ?_ (fun i => ?_) t
      · intro ht; simp
      · intro hti
        simpa using hs i hti


  let adj_index_unique {n m : ℕ} (p q : Fin n → Fin m) (h j : Fin n)
      (hp : ∀ t, t < h → p t = q t) (hd : p h ≠ q h)
      (hq : ∀ t, t < j → p t = q t) (he : p j ≠ q j) : h = j := by
    rcases lt_trichotomy h j with hlt | heq | hgt
    · exact False.elim (hd (hq h hlt))
    · exact heq
    · exact False.elim (he (hp j hgt))


  let quotient_unique_link (r m : ℕ) (p q : (Fin (r + 1) → Fin m)) (hadj : sierAdj r m p q) :
      ∃! ab : Fin m × Fin m, sierAdj (r+1) m (Fin.snoc (α := fun _ => Fin m) p ab.1) (Fin.snoc (α := fun _ => Fin m) q ab.2) := by
    rcases hadj with ⟨h, hp, hd, hs⟩
    refine ⟨(q h, p h), lift_adj hp hd hs, ?_⟩
    rintro ⟨a, b⟩ hab
    rcases hab with ⟨j, hq, he, ht⟩
    have hne : p ≠ q := by intro heq; exact hd (congrFun heq h)
    have hj : j ≠ Fin.last (r+1) := prefix_ne_witness hq (by simpa [word_init] using hne)
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
    have hi : h = i := adj_index_unique p q h i hp hd
      (fun t htt => by simpa using hq t.castSucc htt) (by simpa using he)
    subst i
    have hh := ht (Fin.last (r+1)) (by simp)
    simpa [Prod.mk.injEq] using hh


  let quotient_adj_iff (r m : ℕ) (p q : (Fin (r + 1) → Fin m)) (hne : p ≠ q) :
      sierAdj r m p q ↔ ∃ a b : Fin m, sierAdj (r+1) m (Fin.snoc (α := fun _ => Fin m) p a) (Fin.snoc (α := fun _ => Fin m) q b) := by
    constructor
    · intro hpq
      obtain ⟨ab, hab, _⟩ := quotient_unique_link r m p q hpq
      exact ⟨ab.1, ab.2, hab⟩
    · rintro ⟨a, b, hab⟩
      have h := adj_prefix hab (by simpa [word_init] using hne)
      simpa [word_init] using h


  let adjacent_empty_bonus (r m k : ℕ) (hk : k < m) (D : Finset ((Fin ((r+1) + 1) → Fin m)))
      (hD : isKLimited (k := k) D) (p q : (Fin (r + 1) → Fin m)) (he : (fiber D p).card = 0)
      (hpq : sierAdj r m p q) : m-k+1 ≤ (fiber D q).card := by
    classical
    obtain ⟨ab, hab, _⟩ := quotient_unique_link r m p q hpq
    have hpne : p ≠ q := by
      intro heq
      exact (sierGraph r m).ne_of_adj hpq heq
    have hvD : Fin.snoc (α := fun _ => Fin m) q ab.2 ∈ D := empty_forces_link_endpoint (r+1) m k D hD p he
      (Fin.snoc (α := fun _ => Fin m) p ab.1) (Fin.snoc (α := fun _ => Fin m) q ab.2) (word_init _ _) hab (by simpa [word_init] using hpne.symm)
    exact external_fiber_bonus (r+1) m k hk D hD q (Fin.snoc (α := fun _ => Fin m) q ab.2) (Fin.snoc (α := fun _ => Fin m) p ab.1)
      hvD (word_init _ _) ((sierGraph (r+1) m).adj_symm hab)
      (empty_fiber_not_mem (r+1) m D p he _ (word_init _ _))
      (by simpa [word_init] using hpne)



  let wordEquiv (r m : ℕ) : (Fin r → Fin m) × Fin m ≃ (Fin (r + 1) → Fin m) := {
    toFun := fun x => Fin.snoc (α := fun _ => Fin m) x.1 x.2
    invFun := fun u => (Fin.init u, u (Fin.last r))
    left_inv := by rintro ⟨p, a⟩; simp [word_init, word_last]
    right_inv := word_eta
  }

  let sum_words (r m : ℕ) (f : (Fin (r + 1) → Fin m) → ℕ) :
      (∑ u : (Fin (r + 1) → Fin m), f u) = ∑ p : (Fin r → Fin m), ∑ a : Fin m, f (Fin.snoc (α := fun _ => Fin m) p a) := by
    classical
    calc
      _ = ∑ x : (Fin r → Fin m) × Fin m, f (Fin.snoc (α := fun _ => Fin m) x.1 x.2) := by
        exact (Fintype.sum_equiv (wordEquiv r m) _ _ (fun _ => rfl)).symm
      _ = _ := Fintype.sum_prod_type _


  let group_lower_bound (r m k : ℕ) (hk1 : 1 ≤ k) (hkm : k < m)
      (D : Finset ((Fin ((r+1) + 1) → Fin m))) (hD : isKLimited (k := k) D) (p : (Fin r → Fin m)) :
      (m-k)*m ≤ ∑ a : Fin m, (fiber D (Fin.snoc (α := fun _ => Fin m) p a)).card := by
    classical
    by_cases he : ∃ a : Fin m, (fiber D (Fin.snoc (α := fun _ => Fin m) p a)).card = 0
    · obtain ⟨a, ha⟩ := he
      have hbonus : ∀ b : Fin m, b ≠ a → m-k+1 ≤ (fiber D (Fin.snoc (α := fun _ => Fin m) p b)).card := by
        intro b hb
        exact adjacent_empty_bonus r m k hkm D hD (Fin.snoc (α := fun _ => Fin m) p a) (Fin.snoc (α := fun _ => Fin m) p b) ha
          (adj_same_prefix p a b hb.symm)
      have hkm' : m-k ≤ m-1 := by omega
      have hm : m-1+1 = m := by omega
      have harith : (m-k)*m ≤ (m-k+1)*(m-1) := by nlinarith
      calc
        _ ≤ (m-k+1)*(m-1) := harith
        _ = ∑ b ∈ Finset.univ.erase a, (m-k+1) := by simp [mul_comm]
        _ ≤ ∑ b ∈ Finset.univ.erase a, (fiber D (Fin.snoc (α := fun _ => Fin m) p b)).card := by
          apply Finset.sum_le_sum
          intro b hb
          exact hbonus b (Finset.mem_erase.mp hb).1
        _ ≤ ∑ b : Fin m, (fiber D (Fin.snoc (α := fun _ => Fin m) p b)).card :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    · have hnonempty : ∀ a : Fin m, (fiber D (Fin.snoc (α := fun _ => Fin m) p a)).Nonempty := by
        intro a
        apply Finset.card_pos.mp
        have hn : (fiber D (Fin.snoc (α := fun _ => Fin m) p a)).card ≠ 0 := by intro h; exact he ⟨a, h⟩
        omega
      calc
        _ = ∑ a : Fin m, (m-k) := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun a _ => nonempty_fiber_lower (r+1) m k D hD _ (hnonempty a))


  let dominating_nonempty (r m : ℕ) (hm : 0 < m) (D : Finset ((Fin (r + 1) → Fin m)))
      (hD : (sierGraph r m).IsDominating (D : Set (Fin (r + 1) → Fin m))) : D.Nonempty := by
    classical
    let u : (Fin (r + 1) → Fin m) := fun _ => ⟨0, hm⟩
    by_cases hu : u ∈ D
    · exact ⟨u, hu⟩
    · obtain ⟨v, hv, _⟩ := (hD u).resolve_left hu
      exact ⟨v, hv⟩


  let lower_bound_zero (m k : ℕ) (hm : 0 < m) (D : Finset ((Fin (0 + 1) → Fin m)))
      (hD : isKLimited (k := k) D) : m-k ≤ D.card := by
    classical
    let p : (Fin 0 → Fin m) := fun i => Fin.elim0 i
    have hf : fiber D p = D := by
      ext u
      simp [fiber, Subsingleton.elim (Fin.init u) p]
    have hn : (fiber D p).Nonempty := by
      rw [hf]
      exact dominating_nonempty 0 m hm D hD.1
    simpa [hf] using nonempty_fiber_lower 0 m k D hD p hn


  let lower_bound_succ (r m k : ℕ) (hk1 : 1 ≤ k) (hkm : k < m)
      (D : Finset ((Fin ((r+1) + 1) → Fin m))) (hD : isKLimited (k := k) D) :
      (m-k)*m^(r+1) ≤ D.card := by
    classical
    rw [card_sum_fiber]
    change (m-k)*m^(r+1) ≤ ∑ p : (Fin (r + 1) → Fin m), (fiber D p).card
    rw [sum_words]
    calc
      _ = ∑ p : (Fin r → Fin m), (m-k)*m := by
        simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ _ := Finset.sum_le_sum (fun p _ => group_lower_bound r m k hk1 hkm D hD p)


  let lower_bound (r m k : ℕ) (hk1 : 1 ≤ k) (hkm : k < m)
      (D : Finset ((Fin (r + 1) → Fin m))) (hD : isKLimited (k := k) D) :
      (m-k)*m^r ≤ D.card := by
    cases r with
    | zero => simpa using lower_bound_zero m k (by omega) D hD
    | succ r => exact lower_bound_succ r m k hk1 hkm D hD


  let gamma_exact (r m k : ℕ) [NeZero m] (hk1 : 1 ≤ k) (hkm : k < m) :
      gamma r m k = (m-k)*m^r := by
    apply Nat.le_antisymm (upper_bound r m k hkm)
    obtain ⟨D, hD, hc⟩ := gamma_attained r m k
    rw [← hc]
    exact lower_bound r m k hk1 hkm D hD


  intro n m k hn hm hk1 hkm
  let : NeZero m := ⟨by omega⟩
  exact gamma_exact (n-1) m k hk1 (by omega)

#print axioms result

end D5.S3.Combinatorics.Graph.SierpinskiLimitedDomination
