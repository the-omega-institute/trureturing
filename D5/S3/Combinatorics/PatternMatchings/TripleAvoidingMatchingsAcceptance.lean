/- GID: D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsAcceptance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsAcceptance
   mirror-E: none(waiver:queue-phase-induction)
   anchors: []
   utility: none
   digest: The ordered open queue and pending obligation certify acceptance of every avoider. -/

import D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchingsDecoder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings

open TripleAvoidingMatchingsDefs

set_option maxHeartbeats 1200000 in
/-- Scanning an avoider follows the automaton, with a pending oldest closure
preserved by every intervening opening. -/
theorem encode_accepted {n : ℕ} (m : Matching n) (hm : AvoidsP1 m) :
    AcceptFrom 0 false (List.ofFn (encode m)) := by
  classical
  have inv : ∀ v, m.1 (m.1 v) = v := fun v => (m.2 v).1
  have neq : ∀ v, m.1 v ≠ v := fun v => (m.2 v).2
  obtain ⟨rank, force⟩ := (scan_characterization m).mp hm
  have scan : ∀ (vs : List (Fin (2 * n))) (t : ℕ)
      (q : List (Fin (2 * n))) (f : Bool),
      t ≤ 2 * n → vs.Pairwise (· < ·) → q.Pairwise (· < ·) →
      (∀ x, x ∈ vs ↔ t ≤ x.val) →
      (∀ x, x ∈ q ↔ x.val < t ∧ t ≤ (m.1 x).val) →
      (f = true → ∃ s x y, s.val < t ∧ m.1 s < s ∧ x < m.1 s ∧
        s ≤ m.1 x ∧ m.1 s < y ∧ y < s ∧ s ≤ m.1 y ∧
        x ∈ q ∧ (∀ z ∈ q, x ≤ z) ∧
        ∀ u, s < u → u.val < t → u < m.1 u) →
      AcceptFrom q.length f (vs.map (encode m)) := by
    intro vs
    induction vs with
    | nil =>
      intro t q f ht _ _ hvs hq hf
      have he : t = 2 * n := by
        by_contra h
        have hlt : t < 2 * n := by omega
        have hx := (hvs ⟨t, hlt⟩).mpr (by rfl)
        simp at hx
      have hqe : q = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        have h := (hq x).mp hx
        have hb := (m.1 x).isLt
        omega
      have hfe : f = false := by
        cases f with
        | false => rfl
        | true =>
          obtain ⟨s, x, y, hs, hc, hxc, hxs, hcy, hys, hsy, hxq, _⟩ := hf rfl
          simp [hqe] at hxq
      simp [hqe, hfe, AcceptFrom]
    | cons v vs ih =>
      intro t q f ht hsort hqsort hvs hq hf
      obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp hsort
      have htv : t ≤ v.val := (hvs v).mp (by simp)
      have hv : v.val = t := by
        by_contra h
        have hlt : t < 2 * n := by omega
        let x : Fin (2 * n) := ⟨t, hlt⟩
        have hx : x ∈ v :: vs := (hvs x).mpr (by rfl)
        rcases List.mem_cons.mp hx with hx | hx
        · have hval := congrArg Fin.val hx
          simp [x] at hval
          omega
        · have h := hfirst x hx
          change v.val < t at h
          omega
      have ht' : t + 1 ≤ 2 * n := by have := v.isLt; omega
      have hvs' : ∀ x, x ∈ vs ↔ t + 1 ≤ x.val := by
        intro x
        constructor
        · intro hx
          have h := hfirst x hx
          change v.val < x.val at h
          omega
        · intro hx
          have hmem := (hvs x).mpr (by omega)
          rcases List.mem_cons.mp hmem with h | h
          · subst x
            omega
          · exact h
      have update (q' : List (Fin (2 * n)))
          (he : ∀ x, x ∈ q' ↔
            (x ∈ q ∧ x ≠ m.1 v) ∨ (x = v ∧ v < m.1 v)) :
          ∀ x, x ∈ q' ↔ x.val < t + 1 ∧ t + 1 ≤ (m.1 x).val := by
        intro x
        rw [he, hq]
        have hiff : m.1 x = v ↔ x = m.1 v := by
          constructor
          · intro h
            simpa [inv] using congrArg m.1 h
          · intro h
            rw [h, inv]
        have hne : (m.1 x).val ≠ t ↔ x ≠ m.1 v := by
          constructor
          · intro h hx
            have he := congrArg Fin.val (hiff.mpr hx)
            omega
          · intro h he
            exact h (hiff.mp (Fin.ext (by omega)))
        constructor
        · rintro (⟨⟨hxt, htx⟩, hxm⟩ | ⟨hxv, ho⟩)
          · have hh := hne.mpr hxm
            omega
          · subst x
            change v.val < (m.1 v).val at ho
            omega
        · intro h
          by_cases hxt : x.val < t
          · exact Or.inl ⟨⟨hxt, by omega⟩, hne.mp (by omega)⟩
          · have hxv : x = v := Fin.ext (by omega)
            subst x
            exact Or.inr ⟨rfl, by change v.val < (m.1 v).val; omega⟩
      by_cases ho : v < m.1 v
      · have enc : encode m v = .opening := by simp [encode, ho]
        have qsort' : (q ++ [v]).Pairwise (· < ·) := by
          refine List.pairwise_append.mpr ⟨hqsort, by simp, ?_⟩
          intro x hx y hy
          have h := (hq x).mp hx
          have hyv : y = v := by simpa using hy
          subst y
          change x.val < v.val
          omega
        have qmem' := update (q ++ [v]) (by
          intro x
          simp only [List.mem_append, List.mem_singleton]
          have hnc : x ∈ q → x ≠ m.1 v := by
            intro hx he
            have hh := (hq x).mp hx
            subst x
            change v.val < (m.1 v).val at ho
            omega
          constructor
          · rintro (hx | hx)
            · exact Or.inl ⟨hx, hnc hx⟩
            · exact Or.inr ⟨hx, ho⟩
          · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
            · exact Or.inl hx
            · exact Or.inr hx)
        have hf' : f = true → ∃ s x y, s.val < t + 1 ∧ m.1 s < s ∧
            x < m.1 s ∧ s ≤ m.1 x ∧ m.1 s < y ∧ y < s ∧ s ≤ m.1 y ∧
            x ∈ q ++ [v] ∧ (∀ z ∈ q ++ [v], x ≤ z) ∧
            ∀ u, s < u → u.val < t + 1 → u < m.1 u := by
          intro hftrue
          obtain ⟨s, x, y, hs, hc, hxc, hxs, hcy, hys, hsy, hxq, hmin, hp⟩ := hf hftrue
          refine ⟨s, x, y, by omega, hc, hxc, hxs, hcy, hys, hsy,
            by simp [hxq], ?_, ?_⟩
          · intro z hz
            rcases List.mem_append.mp hz with hz | hz
            · exact hmin z hz
            · have hzv : z = v := by simpa using hz
              subst z
              have hx := (hq x).mp hxq
              change x.val ≤ v.val
              omega
          · intro u hsu hut
            by_cases hu : u.val < t
            · exact hp u hsu hu
            · have huv : u = v := Fin.ext (by omega)
              simpa [huv] using ho
        have hi := ih (t + 1) (q ++ [v]) f ht' htail qsort' hvs' qmem' hf'
        simpa [List.map_cons, enc, AcceptFrom, List.length_append] using hi
      · have hc : m.1 v < v := by have := neq v; omega
        have hcmem : m.1 v ∈ q := (hq _).mpr ⟨by omega, by rw [inv]; omega⟩
        cases q with
        | nil => simp at hcmem
        | cons x r =>
          obtain ⟨hxmin, hrsort⟩ := List.pairwise_cons.mp hqsort
          have hxq : x ∈ x :: r := by simp
          have hxprop := (hq x).mp hxq
          by_cases hcx : m.1 v = x
          · have hnolder : ¬ ∃ z, z < m.1 v ∧ v ≤ m.1 z := by
              rintro ⟨z, hzx, hz⟩
              have hzq : z ∈ x :: r := (hq z).mpr ⟨by omega, by omega⟩
              rcases List.mem_cons.mp hzq with hzq | hzq
              · subst z
                omega
              · have hh := hxmin z hzq
                omega
            have enc : encode m v = .oldest := by simp [encode, ho, hnolder]
            have qmem' := update r (by
              intro z
              simp only [List.mem_cons]
              have hxnot : x ∉ r := fun h => (lt_irrefl x) (hxmin x h)
              rw [hcx]
              have hznot : z ∈ r → z ≠ x := by
                intro hz he
                subst z
                exact hxnot hz
              constructor
              · intro hz
                exact Or.inl ⟨Or.inr hz, hznot hz⟩
              · rintro (⟨hz, hne⟩ | ⟨_, hopen⟩)
                · exact hz.resolve_left hne
                · exact (ho (by simpa [hcx] using hopen)).elim)
            have hi := ih (t + 1) r false ht' htail hrsort hvs' qmem' (by simp)
            simp only [List.map_cons, enc, AcceptFrom, List.length_cons]
            exact ⟨by omega, by simpa using hi⟩
          · have hcr : m.1 v ∈ r := (List.mem_cons.mp hcmem).resolve_left hcx
            cases r with
            | nil => simp at hcr
            | cons y r =>
              obtain ⟨hymin, hrsort'⟩ := List.pairwise_cons.mp hrsort
              have hxy : x < y := hxmin y (by simp)
              have hcy : m.1 v = y := by
                rcases List.mem_cons.mp hcr with h | h
                · exact h
                · have hyc := hymin (m.1 v) h
                  exact (rank v x y hc hxy hyc (by omega)
                    (by have := (hq y).mp (by simp); omega)).elim
              have hyprop := (hq y).mp (by simp)
              have hfnot : f = false := by
                cases f with
                | false => rfl
                | true =>
                  obtain ⟨s, z, u, hs, hsc, hzc, hzs, hcu, hus, hsu,
                    hzq, hzmin, hp⟩ := hf rfl
                  have hpartner := force s z u v hsc hzc hzs hcu hus hsu
                    (by omega) hc (by intro a hsa hav; exact hp a hsa (by omega))
                  have hzx := hzmin x (by simp)
                  rw [hcy] at hpartner
                  omega
              have enc : encode m v = .second := by
                simp [encode, ho, show ∃ z, z < m.1 v ∧ v ≤ m.1 z from
                  ⟨x, by simpa [hcy] using hxy, by omega⟩]
              have qsort' : (x :: r).Pairwise (· < ·) :=
                List.pairwise_cons.mpr ⟨fun z hz => hxmin z (by simp [hz]), hrsort'⟩
              have qmem' := update (x :: r) (by
                intro z
                simp only [List.mem_cons, hcy]
                have hxne : x ≠ y := ne_of_lt hxy
                have hznot : z ∈ r → z ≠ y := by
                  intro hz he
                  subst z
                  exact (lt_irrefl y) (hymin y hz)
                constructor
                · rintro (hz | hz)
                  · exact Or.inl ⟨Or.inl hz, by simpa [hz] using hxne⟩
                  · exact Or.inl ⟨Or.inr (Or.inr hz), hznot hz⟩
                · rintro (⟨hz, hne⟩ | ⟨_, hopen⟩)
                  · rcases hz with hz | hz | hz
                    · exact Or.inl hz
                    · exact (hne hz).elim
                    · exact Or.inr hz
                  · exact (ho (by simpa [hcy] using hopen)).elim)
              have hf' : decide (3 ≤ (x :: y :: r).length) = true →
                  ∃ s z u, s.val < t + 1 ∧ m.1 s < s ∧ z < m.1 s ∧
                    s ≤ m.1 z ∧ m.1 s < u ∧ u < s ∧ s ≤ m.1 u ∧
                    z ∈ x :: r ∧ (∀ a ∈ x :: r, z ≤ a) ∧
                    ∀ a, s < a → a.val < t + 1 → a < m.1 a := by
                intro hlen
                have hrne : r ≠ [] := by
                  intro he
                  simp [he] at hlen
                obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil r hrne
                have hzprop := (hq z).mp (by simp [hz])
                refine ⟨v, x, z, by omega, hc, by simpa [hcy] using hxy,
                  by omega, by simpa [hcy] using hymin z hz, by omega, by omega,
                  by simp, ?_, ?_⟩
                · intro a ha
                  rcases List.mem_cons.mp ha with ha | ha
                  · subst a
                    exact le_rfl
                  · exact (hxmin a (by simp [ha])).le
                · intro a hva hat
                  change v.val < a.val at hva
                  omega
              have hi := ih (t + 1) (x :: r) _ ht' htail qsort' hvs' qmem' hf'
              simp only [List.map_cons, enc, AcceptFrom]
              refine ⟨hfnot, by simp, ?_⟩
              simpa using hi
  have hsort : (List.finRange (2 * n)).Pairwise (· < ·) := by
    rw [← List.ofFn_id]
    exact List.pairwise_ofFn.mpr (fun i j hij => hij)
  have hs := scan (List.finRange (2 * n)) 0 [] false (by omega) hsort
    (by simp) (by simp) (by simp) (by simp)
  simpa [List.ofFn_eq_map] using hs

end D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings
