/- GID: D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsCorrespondence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsCorrespondence
   mirror-E: none(waiver:constructive-scan-bijection)
   anchors: []
   utility: none
   digest: Queue decoding and scanning give inverse maps between avoiders and accepted words. -/

import D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchingsAcceptance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings

open TripleAvoidingMatchingsDefs

set_option maxHeartbeats 2000000 in
/-- The labeled scan is a bijection, including both choices at height two. -/
noncomputable def matchingEquiv (n : ℕ) : {m : Matching n // AvoidsP1 m} ≃ Accepted n := by
  classical
  have pair_mem : ∀ (p : List (Fin (2 * n) × Fin (2 * n))),
      (p.flatMap fun e => [e.1, e.2]).Nodup →
      ∀ a b, (a, b) ∈ p → pairFunction p a = b ∧ pairFunction p b = a := by
    intro p
    induction p with
    | nil => simp
    | cons e p ih =>
      rcases e with ⟨c, d⟩
      intro hn a b hab
      change (c :: d :: p.flatMap (fun e => [e.1, e.2])).Nodup at hn
      obtain ⟨hc, hd, hp⟩ := List.nodup_cons.mp hn |>.imp_right List.nodup_cons.mp
      have hcd : c ≠ d := fun h => hc (by simp [h])
      rcases List.mem_cons.mp hab with hab | hab
      · have ha : a = c := congrArg Prod.fst hab
        have hb : b = d := congrArg Prod.snd hab
        subst a
        subst b
        simp [pairFunction, hcd.symm]
      · have ha : a ∈ p.flatMap (fun e => [e.1, e.2]) :=
          List.mem_flatMap.mpr ⟨(a, b), hab, by simp⟩
        have hb : b ∈ p.flatMap (fun e => [e.1, e.2]) :=
          List.mem_flatMap.mpr ⟨(a, b), hab, by simp⟩
        have hac : a ≠ c := by intro h; subst a; exact hc (by simp [ha])
        have had : a ≠ d := by intro h; subst a; exact hd ha
        have hbc : b ≠ c := by intro h; subst b; exact hc (by simp [hb])
        have hbd : b ≠ d := by intro h; subst b; exact hd hb
        simpa [pairFunction, hac, had, hbc, hbd] using ih hp a b hab
  have queued : ∀ (w : List Action) (q vs : List (Fin (2 * n)))
      (p : List (Fin (2 * n) × Fin (2 * n))),
      decodePairs q vs w = some p → ∀ x ∈ q, ∃ b ∈ vs, (x, b) ∈ p := by
    intro w
    induction w with
    | nil =>
      intro q vs p hp x hx
      cases q <;> cases vs <;> simp [decodePairs] at hp
      simp at hx
    | cons a w ih =>
      intro q vs p hp x hx
      cases vs with
      | nil => simp [decodePairs] at hp
      | cons v vs =>
        cases a with
        | opening =>
          simp only [decodePairs] at hp
          obtain ⟨b, hb, hpair⟩ := ih (q ++ [v]) vs p hp x (by simp [hx])
          exact ⟨b, by simp [hb], hpair⟩
        | oldest =>
          cases q with
          | nil => simp [decodePairs] at hp
          | cons y q =>
            cases hd : decodePairs q vs w with
            | none => simp [decodePairs, hd] at hp
            | some p' =>
              simp only [decodePairs, hd, Option.map_some, Option.some.injEq] at hp
              subst p
              rcases List.mem_cons.mp hx with hxy | hx
              · subst x
                exact ⟨v, by simp, by simp⟩
              · obtain ⟨b, hb, hpair⟩ := ih q vs p' hd x hx
                exact ⟨b, by simp [hb], by simp [hpair]⟩
        | second =>
          cases q with
          | nil => simp [decodePairs] at hp
          | cons y q =>
            cases q with
            | nil => simp [decodePairs] at hp
            | cons z q =>
              cases hd : decodePairs (y :: q) vs w with
              | none => simp [decodePairs, hd] at hp
              | some p' =>
                simp only [decodePairs, hd, Option.map_some, Option.some.injEq] at hp
                subst p
                by_cases hxz : x = z
                · subst x
                  exact ⟨v, by simp, by simp⟩
                · have hx' : x ∈ y :: q := by
                    simpa only [List.mem_cons, hxz, false_or] using hx
                  obtain ⟨b, hb, hpair⟩ := ih (y :: q) vs p' hd x hx'
                  exact ⟨b, by simp [hb], by simp [hpair]⟩
  have run : ∀ (vs : List (Fin (2 * n))) (w : List Action) (t : ℕ)
      (q : List (Fin (2 * n))) (f : Bool) (m : Matching n)
      (p : List (Fin (2 * n) × Fin (2 * n))),
      vs.length = w.length → vs.Pairwise (· < ·) → q.Pairwise (· < ·) →
      (∀ x, x ∈ vs ↔ t ≤ x.val) →
      (∀ x, x ∈ q ↔ x.val < t ∧ t ≤ (m.1 x).val) →
      AcceptFrom q.length f w → decodePairs q vs w = some p →
      (∀ a b, (a, b) ∈ p → m.1 a = b ∧ m.1 b = a) →
      vs.map (encode m) = w ∧
      (∀ u x y, t ≤ u.val → m.1 u < u → x < y → y < m.1 u →
        u ≤ m.1 x → u ≤ m.1 y → False) ∧
      (∀ s x y u, t ≤ s.val → m.1 s < s → x < m.1 s → s ≤ m.1 x →
        m.1 s < y → y < s → s ≤ m.1 y → s < u → m.1 u < u →
        (∀ a, s < a → a < u → a < m.1 a) → m.1 u = x) ∧
      (f = true → ∀ x r, q = x :: r → ∀ u, t ≤ u.val → m.1 u < u →
        (∀ a, t ≤ a.val → a < u → a < m.1 a) → m.1 u = x) := by
    intro vs
    induction vs with
    | nil =>
      intro w t q f m p hlen _ _ hvs _ _ _ _
      have hw : w = [] := List.length_eq_zero_iff.mp hlen.symm
      subst w
      refine ⟨rfl, ?_, ?_, ?_⟩
      · intro u x y hu
        have hh := (hvs u).mpr hu
        simp at hh
      · intro s x y u hs
        have hh := (hvs s).mpr hs
        simp at hh
      · intro hf x r hq u hu
        have hh := (hvs u).mpr hu
        simp at hh
    | cons v vs ih =>
      intro w t q f m p hlen hsort hqsort hvs hq ha hd hcomp
      cases w with
      | nil => simp at hlen
      | cons a w =>
        have inv : ∀ x, m.1 (m.1 x) = x := fun x => (m.2 x).1
        obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp hsort
        have htv : t ≤ v.val := (hvs v).mp (by simp)
        have hv : v.val = t := by
          by_contra h
          have hlt : t < 2 * n := by have := v.isLt; omega
          let x : Fin (2 * n) := ⟨t, hlt⟩
          have hx := (hvs x).mpr (by rfl)
          rcases List.mem_cons.mp hx with hx | hx
          · have hh := congrArg Fin.val hx
            simp [x] at hh
            omega
          · have hh := hfirst x hx
            change v.val < t at hh
            omega
        have hvs' : ∀ x, x ∈ vs ↔ t + 1 ≤ x.val := by
          intro x
          constructor
          · intro hx
            have hh := hfirst x hx
            change v.val < x.val at hh
            omega
          · intro hx
            have hh := (hvs x).mpr (by omega)
            rcases List.mem_cons.mp hh with hh | hh
            · subst x
              omega
            · exact hh
        have hlen' : vs.length = w.length := by simpa using hlen
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
        cases a with
        | opening =>
          simp only [decodePairs] at hd
          obtain ⟨b, hb, hvb⟩ := queued w (q ++ [v]) vs p hd v (by simp)
          have hmv := (hcomp v b hvb).1
          have ho : v < m.1 v := by rw [hmv]; exact hfirst b hb
          have enc : encode m v = .opening := by simp [encode, ho]
          have qsort' : (q ++ [v]).Pairwise (· < ·) := by
            refine List.pairwise_append.mpr ⟨hqsort, by simp, ?_⟩
            intro x hx y hy
            have hh := (hq x).mp hx
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
          obtain ⟨he, hrank, hforce, hforced⟩ :=
            ih w (t + 1) (q ++ [v]) f m p hlen' htail qsort' hvs' qmem'
              (by simpa [AcceptFrom, List.length_append] using ha) hd hcomp
          refine ⟨by simp [enc, he], ?_, ?_, ?_⟩
          · intro u x y hu hc hxy hyc hxu hyu
            by_cases huv : u = v
            · subst u
              omega
            · exact hrank u x y (by omega) hc hxy hyc hxu hyu
          · intro s x y u hs hc hxc hxs hcy hys hsy hsu huc hp
            by_cases hsv : s = v
            · subst s
              omega
            · exact hforce s x y u (by omega) hc hxc hxs hcy hys hsy hsu huc hp
          · intro hf x r hqr u hu hc hp
            have huv : u ≠ v := by intro h; subst u; omega
            have hq' : q ++ [v] = x :: (r ++ [v]) := by simp [hqr]
            exact hforced hf x (r ++ [v]) hq' u (by omega) hc
              (fun a ha hau => hp a (by omega) hau)
        | oldest =>
          cases q with
          | nil => simp [AcceptFrom] at ha
          | cons x r =>
            obtain ⟨hxmin, hrsort⟩ := List.pairwise_cons.mp hqsort
            cases hdec : decodePairs r vs w with
            | none => simp [decodePairs, hdec] at hd
            | some p' =>
              simp only [decodePairs, hdec, Option.map_some, Option.some.injEq] at hd
              subst p
              obtain ⟨hmx, hmv⟩ := hcomp x v (by simp)
              have hxprop := (hq x).mp (by simp)
              have hc : m.1 v < v := by rw [hmv]; change x.val < v.val; omega
              have ho : ¬ v < m.1 v := not_lt_of_ge hc.le
              have hnolder : ¬ ∃ z, z < m.1 v ∧ v ≤ m.1 z := by
                rintro ⟨z, hzx, hz⟩
                have hzq := (hq z).mpr ⟨by omega, by omega⟩
                rcases List.mem_cons.mp hzq with hzq | hzq
                · subst z
                  omega
                · have hh := hxmin z hzq
                  omega
              have enc : encode m v = .oldest := by simp [encode, ho, hnolder]
              have qmem' := update r (by
                intro z
                simp only [List.mem_cons, hmv]
                have hznot : z ∈ r → z ≠ x := by
                  intro hz he
                  subst z
                  exact (lt_irrefl x) (hxmin x hz)
                constructor
                · intro hz
                  exact Or.inl ⟨Or.inr hz, hznot hz⟩
                · rintro (⟨hz, hne⟩ | ⟨_, hopen⟩)
                  · exact hz.resolve_left hne
                  · exact (ho (by simpa [hmv] using hopen)).elim)
              have ha' : AcceptFrom r.length false w := by
                simpa [AcceptFrom] using ha.2
              obtain ⟨he, hrank, hforce, _⟩ := ih w (t + 1) r false m p' hlen'
                htail hrsort hvs' qmem' ha' hdec
                (by intro a b hab; exact hcomp a b (by simp [hab]))
              refine ⟨by simp [enc, he], ?_, ?_, ?_⟩
              · intro u a b hu huc hab hbc hau hbu
                by_cases huv : u = v
                · subst u
                  exact (hnolder ⟨b, hbc, hbu⟩).elim
                · exact hrank u a b (by omega) huc hab hbc hau hbu
              · intro s a b u hs hsc hac has hcb hbs hsb hsu huc hp
                by_cases hsv : s = v
                · subst s
                  exact (hnolder ⟨a, hac, has⟩).elim
                · exact hforce s a b u (by omega) hsc hac has hcb hbs hsb hsu huc hp
              · intro hf y r' hqr u hu huc hp
                have hxy : x = y := (List.cons.inj hqr).1
                by_cases huv : u = v
                · simpa [huv, hxy] using hmv
                · have hvu : v < u := by change v.val < u.val; omega
                  have hh := hp v (by omega) hvu
                  omega
        | second =>
          cases q with
          | nil => simp [AcceptFrom] at ha
          | cons x r =>
            cases r with
            | nil => simp [AcceptFrom] at ha
            | cons y r =>
              obtain ⟨hxmin, hysort⟩ := List.pairwise_cons.mp hqsort
              obtain ⟨hymin, hrsort⟩ := List.pairwise_cons.mp hysort
              have hxy : x < y := hxmin y (by simp)
              cases hdec : decodePairs (x :: r) vs w with
              | none => simp [decodePairs, hdec] at hd
              | some p' =>
                simp only [decodePairs, hdec, Option.map_some, Option.some.injEq] at hd
                subst p
                obtain ⟨hmy, hmv⟩ := hcomp y v (by simp)
                have hxprop := (hq x).mp (by simp)
                have hyprop := (hq y).mp (by simp)
                have hc : m.1 v < v := by rw [hmv]; change y.val < v.val; omega
                have ho : ¬ v < m.1 v := not_lt_of_ge hc.le
                have enc : encode m v = .second := by
                  simp [encode, ho, show ∃ z, z < m.1 v ∧ v ≤ m.1 z from
                    ⟨x, by simpa [hmv] using hxy, by omega⟩]
                have qsort' : (x :: r).Pairwise (· < ·) :=
                  List.pairwise_cons.mpr
                    ⟨fun z hz => hxmin z (by simp [hz]), hrsort⟩
                have qmem' := update (x :: r) (by
                  intro z
                  simp only [List.mem_cons, hmv]
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
                    · exact (ho (by simpa [hmv] using hopen)).elim)
                have ha' : AcceptFrom (x :: r).length
                    (decide (3 ≤ (x :: y :: r).length)) w := by
                  simpa [AcceptFrom] using ha.2.2
                obtain ⟨he, hrank, hforce, hforced⟩ := ih w (t + 1) (x :: r) _ m p'
                  hlen' htail qsort' hvs' qmem' ha' hdec
                  (by intro a b hab; exact hcomp a b (by simp [hab]))
                have old_unique (z : Fin (2 * n)) (hzy : z < y) (hzq : z ∈ x :: y :: r) :
                    z = x := by
                  rcases List.mem_cons.mp hzq with hz | hz
                  · exact hz
                  · rcases List.mem_cons.mp hz with hz | hz
                    · subst z
                      omega
                    · have hh := hymin z hz
                      omega
                refine ⟨by simp [enc, he], ?_, ?_, ?_⟩
                · intro u a b hu huc hab hbc hau hbu
                  by_cases huv : u = v
                  · subst u
                    have haq := (hq a).mpr ⟨by omega, by omega⟩
                    have hbq := (hq b).mpr ⟨by omega, by omega⟩
                    have hax := old_unique a (by simpa [hmv] using lt_trans hab hbc) haq
                    have hbx := old_unique b (by simpa [hmv] using hbc) hbq
                    omega
                  · exact hrank u a b (by omega) huc hab hbc hau hbu
                · intro s a b u hs hsc hac has hcb hbs hsb hsu huc hp
                  by_cases hsv : s = v
                  · subst s
                    have haq := (hq a).mpr ⟨by omega, by omega⟩
                    have hax := old_unique a (by simpa [hmv] using hac) haq
                    have hbq := (hq b).mpr ⟨by omega, by omega⟩
                    have hbr : b ∈ r := by
                      rcases List.mem_cons.mp hbq with hbq | hbq
                      · subst b
                        omega
                      · rcases List.mem_cons.mp hbq with hbq | hbq
                        · subst b
                          omega
                        · exact hbq
                    have hrne : r ≠ [] := by intro h; simp [h] at hbr
                    have hlenr : 0 < r.length := List.length_pos_iff.mpr hrne
                    have hftrue : decide (3 ≤ (x :: y :: r).length) = true := by
                      simp only [decide_eq_true_eq, List.length_cons]
                      omega
                    have hh := hforced hftrue x r rfl u (by omega) huc
                      (by intro z hz hzu; exact hp z (by change v.val < z.val; omega) hzu)
                    simpa [hax] using hh
                  · exact hforce s a b u (by omega) hsc hac has hcb hbs hsb hsu huc hp
                · intro hf
                  have hff : f = false := ha.1
                  simp [hff] at hf
  have correct (w : Accepted n) : AvoidsP1 (decodeMatching w) ∧
      encode (decodeMatching w) = w.1 := by
    let vs := List.finRange (2 * n)
    have hex := decode_pairs (List.ofFn w.1) [] vs false (by simp [vs]) w.2
    let p := Classical.choose hex
    have hs := Classical.choose_spec hex
    have hperm : (p.flatMap fun e => [e.1, e.2]).Perm vs := by simpa using hs.2
    have hn : (p.flatMap fun e => [e.1, e.2]).Nodup :=
      hperm.nodup_iff.mpr (by simpa [vs] using List.nodup_finRange (2 * n))
    have hfun : (decodeMatching w).1 = pairFunction p := rfl
    have hsort : vs.Pairwise (· < ·) := by
      rw [show vs = List.ofFn id from rfl]
      exact List.pairwise_ofFn.mpr (fun i j hij => hij)
    obtain ⟨he, hrank, hforce, _⟩ := run vs (List.ofFn w.1) 0 [] false
      (decodeMatching w) p (by simp [vs]) hsort (by simp) (by simp [vs]) (by simp)
      w.2 hs.1 (by intro a b hab; rw [hfun]; exact pair_mem p hn a b hab)
    refine ⟨(scan_characterization _).mpr ⟨?_, ?_⟩, ?_⟩
    · intro u x y
      exact hrank u x y (by omega)
    · intro s x y u
      exact hforce s x y u (by omega)
    · apply List.ofFn_injective
      simpa [vs, List.ofFn_eq_map] using he
  refine
    { toFun := fun m => ⟨encode m.1, encode_accepted m.1 m.2⟩
      invFun := fun w => ⟨decodeMatching w, (correct w).1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro m
    apply Subtype.ext
    apply encode_injective _ _ (correct ⟨encode m.1, encode_accepted m.1 m.2⟩).1 m.2
    exact (correct ⟨encode m.1, encode_accepted m.1 m.2⟩).2
  · intro w
    apply Subtype.ext
    exact (correct w).2

end D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings
