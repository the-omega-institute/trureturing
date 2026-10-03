/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveThree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveThree
   mirror-E: none(waiver:row-four-three-letter-obstructions)
   anchors: []
   utility: none
   digest: Excludes two first-occurrence orders by constructing forbidden patterns. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveThree

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders

theorem forbidden_last_first (w : List ℕ) (a b c : ℕ)
    (ha : w.count a = 2) (hb : w.count b = 2) (hc : w.count c = 2)
    (hab : a < b) (hbc : b < c)
    (hsame : ∀ p ∈ w, ∀ q ∈ w,
      (w).idxOf p < (w).idxOf q → secondPos p w < secondPos q w)
    (h2231 : ¬ NonnestingDefs.Occurs [2, 2, 3, 1] w)
    (h3221 : ¬ NonnestingDefs.Occurs [3, 2, 2, 1] w) :
    ¬ ((w).idxOf b < (w).idxOf c ∧ (w).idxOf c < (w).idxOf a) ∧
      ¬ ((w).idxOf c < (w).idxOf b ∧ (w).idxOf b < (w).idxOf a) := by
  have count_two_positions (a : ℕ) (w : List ℕ)
      (hw : w.count a = 2) :
      (w).idxOf a < secondPos a w ∧
        w[(w).idxOf a]? = some a ∧ w[secondPos a w]? = some a := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ := count_two_decomposition a w hw
    have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    constructor
    · rw [hfirst, hsecond]
      omega
    constructor
    · rw [hfirst]
      simp
    · rw [hsecond]
      have hle : ¬ u.length + 1 + v.length < u.length := by omega
      simp [List.getElem?_append, hle]
      have heq : u.length + 1 + v.length - u.length = v.length + 1 := by omega
      rw [heq]
      simp
  have pa := count_two_positions a w ha
  have pb := count_two_positions b w hb
  have pc := count_two_positions c w hc
  have hma : a ∈ w := List.mem_of_getElem? pa.2.1
  have hmb : b ∈ w := List.mem_of_getElem? pb.2.1
  have hmc : c ∈ w := List.mem_of_getElem? pc.2.1
  have hfa : (w).idxOf a < w.length := (List.getElem?_eq_some_iff.mp pa.2.1).1
  have hfb : (w).idxOf b < w.length := (List.getElem?_eq_some_iff.mp pb.2.1).1
  have hfc : (w).idxOf c < w.length := (List.getElem?_eq_some_iff.mp pc.2.1).1
  have hsa : secondPos a w < w.length := (List.getElem?_eq_some_iff.mp pa.2.2).1
  have hsb : secondPos b w < w.length := (List.getElem?_eq_some_iff.mp pb.2.2).1
  have hsc : secondPos c w < w.length := (List.getElem?_eq_some_iff.mp pc.2.2).1
  have vfa : w[(w).idxOf a] = a := (List.getElem?_eq_some_iff.mp pa.2.1).2
  have vfb : w[(w).idxOf b] = b := (List.getElem?_eq_some_iff.mp pb.2.1).2
  have vfc : w[(w).idxOf c] = c := (List.getElem?_eq_some_iff.mp pc.2.1).2
  have vsa : w[secondPos a w] = a := (List.getElem?_eq_some_iff.mp pa.2.2).2
  have vsb : w[secondPos b w] = b := (List.getElem?_eq_some_iff.mp pb.2.2).2
  have vsc : w[secondPos c w] = c := (List.getElem?_eq_some_iff.mp pc.2.2).2
  have hfour (p₀ p₁ p₂ p₃ : ℕ)
      (h₀ : p₀ < p₁) (h₁ : p₁ < p₂) (h₂ : p₂ < p₃)
      (h₃ : p₃ < w.length) :
      List.Sublist [w[p₀], w[p₁], w[p₂], w[p₃]] w := by
    let p : Fin 4 → ℕ := fun j =>
      if j.val = 0 then p₀ else if j.val = 1 then p₁ else
      if j.val = 2 then p₂ else p₃
    have hp : ∀ j : Fin 4, p j < w.length := by
      intro j
      fin_cases j <;> simp [p] <;> omega
    let f : Fin 4 ↪o Fin w.length :=
      OrderEmbedding.ofMapLEIff (fun j => ⟨p j, hp j⟩) (by
        intro i j
        fin_cases i <;> fin_cases j <;> simp [p] <;> omega)
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨f, ?_⟩
    intro j
    fin_cases j <;> simp [f, p]
  let x : ℕ → ℕ := fun i => if i = 1 then a else if i = 2 then b else c
  have hocc (σ : List ℕ) (hletters : NonnestingDefs.letters σ = 3)
      (hsub : List.Sublist (σ.map x) w) : NonnestingDefs.Occurs σ w := by
    unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
    refine ⟨x, ?_, ?_, hsub, by simp⟩
    · intro i hi hlt
      rw [hletters] at hlt
      have hi' : i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl
      · simpa [x] using hab
      · simpa [x] using hbc
    · intro i hi hle
      rw [hletters] at hle
      have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi' with rfl | rfl | rfl
      · simpa [x] using hma
      · simpa [x] using hmb
      · simpa [x] using hmc
  constructor
  · rintro ⟨hbcFirst, hcaFirst⟩
    have hsbsc : secondPos b w < secondPos c w :=
      hsame b hmb c hmc hbcFirst
    have hscsa : secondPos c w < secondPos a w :=
      hsame c hmc a hma hcaFirst
    have hsub : List.Sublist [b, b, c, a] w := by
      simpa [vfb, vsb, vsc, vsa] using
        hfour ((w).idxOf b) (secondPos b w)
          (secondPos c w) (secondPos a w) pb.1 hsbsc hscsa hsa
    apply h2231
    apply hocc [2, 2, 3, 1] (by decide)
    simpa [x] using hsub
  · rintro ⟨hcbFirst, hbaFirst⟩
    have hsbsa : secondPos b w < secondPos a w :=
      hsame b hmb a hma hbaFirst
    have hsub : List.Sublist [c, b, b, a] w := by
      simpa [vfc, vfb, vsb, vsa] using
        hfour ((w).idxOf c) ((w).idxOf b)
          (secondPos b w) (secondPos a w) hcbFirst pb.1 hsbsa hsa
    apply h3221
    apply hocc [3, 2, 2, 1] (by decide)
    simpa [x] using hsub

theorem separated_three_orders (w : List ℕ) (a b c : ℕ)
    (ha : w.count a = 2) (hb : w.count b = 2) (hc : w.count c = 2)
    (hab : a < b) (hbc : b < c)
    (hsame : ∀ p ∈ w, ∀ q ∈ w,
      (w).idxOf p < (w).idxOf q → secondPos p w < secondPos q w)
    (h1231 : ¬ NonnestingDefs.Occurs [1, 2, 3, 1] w)
    (h1312 : ¬ NonnestingDefs.Occurs [1, 3, 1, 2] w) :
    ((w).idxOf a < (w).idxOf b → (w).idxOf b < (w).idxOf c →
      secondPos a w < (w).idxOf c) ∧
    ((w).idxOf a < (w).idxOf c → (w).idxOf c < (w).idxOf b →
      secondPos a w < (w).idxOf c) ∧
    ((w).idxOf c < (w).idxOf a → (w).idxOf a < (w).idxOf b →
      secondPos c w < (w).idxOf a) := by
  have count_two_positions (a : ℕ) (w : List ℕ)
      (hw : w.count a = 2) :
      (w).idxOf a < secondPos a w ∧
        w[(w).idxOf a]? = some a ∧ w[secondPos a w]? = some a := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ := count_two_decomposition a w hw
    have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    constructor
    · rw [hfirst, hsecond]
      omega
    constructor
    · rw [hfirst]
      simp
    · rw [hsecond]
      have hle : ¬ u.length + 1 + v.length < u.length := by omega
      simp [List.getElem?_append, hle]
      have heq : u.length + 1 + v.length - u.length = v.length + 1 := by omega
      rw [heq]
      simp
  have pa := count_two_positions a w ha
  have pb := count_two_positions b w hb
  have pc := count_two_positions c w hc
  have hma : a ∈ w := List.mem_of_getElem? pa.2.1
  have hmb : b ∈ w := List.mem_of_getElem? pb.2.1
  have hmc : c ∈ w := List.mem_of_getElem? pc.2.1
  have hfc : (w).idxOf c < w.length := (List.getElem?_eq_some_iff.mp pc.2.1).1
  have hsa : secondPos a w < w.length := (List.getElem?_eq_some_iff.mp pa.2.2).1
  have hsb : secondPos b w < w.length := (List.getElem?_eq_some_iff.mp pb.2.2).1
  have hsc : secondPos c w < w.length := (List.getElem?_eq_some_iff.mp pc.2.2).1
  have vfa : w[(w).idxOf a] = a := (List.getElem?_eq_some_iff.mp pa.2.1).2
  have vfb : w[(w).idxOf b] = b := (List.getElem?_eq_some_iff.mp pb.2.1).2
  have vfc : w[(w).idxOf c] = c := (List.getElem?_eq_some_iff.mp pc.2.1).2
  have vsa : w[secondPos a w] = a := (List.getElem?_eq_some_iff.mp pa.2.2).2
  have vsb : w[secondPos b w] = b := (List.getElem?_eq_some_iff.mp pb.2.2).2
  have vsc : w[secondPos c w] = c := (List.getElem?_eq_some_iff.mp pc.2.2).2
  have hfour (p₀ p₁ p₂ p₃ : ℕ)
      (h₀ : p₀ < p₁) (h₁ : p₁ < p₂) (h₂ : p₂ < p₃)
      (h₃ : p₃ < w.length) :
      List.Sublist [w[p₀], w[p₁], w[p₂], w[p₃]] w := by
    let p : Fin 4 → ℕ := fun j =>
      if j.val = 0 then p₀ else if j.val = 1 then p₁ else
      if j.val = 2 then p₂ else p₃
    have hp : ∀ j : Fin 4, p j < w.length := by
      intro j
      fin_cases j <;> simp [p] <;> omega
    let f : Fin 4 ↪o Fin w.length :=
      OrderEmbedding.ofMapLEIff (fun j => ⟨p j, hp j⟩) (by
        intro i j
        fin_cases i <;> fin_cases j <;> simp [p] <;> omega)
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨f, ?_⟩
    intro j
    fin_cases j <;> simp [f, p]
  let x : ℕ → ℕ := fun i => if i = 1 then a else if i = 2 then b else c
  have hocc (σ : List ℕ) (hletters : NonnestingDefs.letters σ = 3)
      (hsub : List.Sublist (σ.map x) w) : NonnestingDefs.Occurs σ w := by
    unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
    refine ⟨x, ?_, ?_, hsub, by simp⟩
    · intro i hi hlt
      rw [hletters] at hlt
      have hi' : i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl
      · simpa [x] using hab
      · simpa [x] using hbc
    · intro i hi hle
      rw [hletters] at hle
      have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi' with rfl | rfl | rfl
      · simpa [x] using hma
      · simpa [x] using hmb
      · simpa [x] using hmc
  constructor
  · intro habFirst hbcFirst
    by_contra hsep
    have hfcsa : (w).idxOf c < secondPos a w := by
      have hne : (w).idxOf c ≠ secondPos a w := by
        intro h
        have hca' : some c = some a := by
          calc
            some c = w[(w).idxOf c]? := pc.2.1.symm
            _ = w[secondPos a w]? := congrArg (fun i => w[i]?) h
            _ = some a := pa.2.2
        have hca : c = a := by simpa using hca'
        exact (Nat.ne_of_gt (hab.trans hbc)) hca
      omega
    have hsub : List.Sublist [a, b, c, a] w := by
      simpa [vfa, vfb, vfc, vsa] using
        hfour ((w).idxOf a) ((w).idxOf b) ((w).idxOf c)
          (secondPos a w) habFirst hbcFirst hfcsa hsa
    exact h1231 (hocc [1, 2, 3, 1] (by decide) (by simpa [x] using hsub))
  constructor
  · intro hacFirst hcbFirst
    by_contra hsep
    have hfcsa : (w).idxOf c < secondPos a w := by
      have hne : (w).idxOf c ≠ secondPos a w := by
        intro h
        have hca' : some c = some a := by
          calc
            some c = w[(w).idxOf c]? := pc.2.1.symm
            _ = w[secondPos a w]? := congrArg (fun i => w[i]?) h
            _ = some a := pa.2.2
        have hca : c = a := by simpa using hca'
        exact (Nat.ne_of_gt (hab.trans hbc)) hca
      omega
    have hsasb : secondPos a w < secondPos b w :=
      hsame a hma b hmb (lt_trans hacFirst hcbFirst)
    have hsub : List.Sublist [a, c, a, b] w := by
      simpa [vfa, vfc, vsa, vsb] using
        hfour ((w).idxOf a) ((w).idxOf c) (secondPos a w)
          (secondPos b w) hacFirst hfcsa hsasb hsb
    exact h1312 (hocc [1, 3, 1, 2] (by decide) (by simpa [x] using hsub))
  · intro hcaFirst habFirst
    by_contra hsep
    have hfasc : (w).idxOf a < secondPos c w := by
      have hne : (w).idxOf a ≠ secondPos c w := by
        intro h
        have hac' : some a = some c := by
          calc
            some a = w[(w).idxOf a]? := pa.2.1.symm
            _ = w[secondPos c w]? := congrArg (fun i => w[i]?) h
            _ = some c := pc.2.2
        have hac : a = c := by simpa using hac'
        exact (Nat.ne_of_lt (hab.trans hbc)) hac
      omega
    have hscsa : secondPos c w < secondPos a w :=
      hsame c hmc a hma hcaFirst
    have hsasb : secondPos a w < secondPos b w :=
      hsame a hma b hmb habFirst
    have hsub : List.Sublist [a, c, a, b] w := by
      simpa [vfa, vsc, vsa, vsb] using
        hfour ((w).idxOf a) (secondPos c w) (secondPos a w)
          (secondPos b w) hfasc hscsa hsasb hsb
    exact h1312 (hocc [1, 3, 1, 2] (by decide) (by simpa [x] using hsub))

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveThree

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveThree.forbidden_last_first
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveThree.separated_three_orders
