/- GID: D5/S0/Computability/Coding/TwoWordCode
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/TwoWordCode
   mirror-E: none(waiver:abstract-labelled-word-criterion)
   anchors: []
   utility: none
   digest: A labelled two-word encoding is injective exactly when its words do not commute. -/

module

public import Mathlib.InformationTheory.Coding.PrefixFree
public import Mathlib.Data.List.Basic

/-!
Two labelled finite words form a uniquely decodable encoding exactly when they
fail to commute. The alphabet is arbitrary. Empty and equal words remain in the
statement, and proper prefix overlap is allowed.
-/

public section

namespace D5.S0.Computability.Coding.TwoWordCode

universe u

private def enc {α : Type u} (a b : List α) (s : List Bool) : List α :=
  s.flatMap (fun t => if t then b else a)

private theorem prefix_injective {α : Type u} (f : Bool → List α)
    (hf : Function.Injective f)
    (hp : InformationTheory.IsPrefixFree (Set.range f))
    (he : [] ∉ Set.range f) : Function.Injective (fun s : List Bool => s.flatMap f) := by
  intro s t h
  apply hf.list_map
  apply hp.isUniquelyDecodable he (s.map f) (t.map f)
  · intro w hw
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
    exact ⟨i, rfl⟩
  · intro w hw
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
    exact ⟨i, rfl⟩
  · exact h

private theorem recode_injective :
    Function.Injective (enc [false] [false, true]) := by
  have hp : Function.Injective (enc [false] [true, false]) := by
    apply prefix_injective (fun t => if t then [true, false] else [false])
    · intro i j h
      cases i <;> cases j <;> simp_all
    · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ h
      cases i <;> cases j <;> simp_all
    · rintro ⟨i, h⟩
      cases i <;> simp_all
  intro s t h
  have hr := congrArg List.reverse h
  have hr' : enc [false] [true, false] s.reverse =
      enc [false] [true, false] t.reverse := by
    simpa only [enc, List.reverse_flatMap, Function.comp_def,
      apply_ite List.reverse, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.append_nil, List.cons_append] using hr
  exact List.reverse_inj.mp (hp hr')

private theorem enc_recode {α : Type u} (a r : List α) (s : List Bool) :
    enc a r (enc [false] [false, true] s) = enc a (a ++ r) s := by
  induction s with
  | nil => rfl
  | cons t s ih =>
      cases t with
      | false => simpa [enc] using congrArg (fun w => a ++ w) ih
      | true => simpa [enc, List.append_assoc] using congrArg (fun w => (a ++ r) ++ w) ih

private theorem extend_injective {α : Type u} (a r : List α)
    (h : Function.Injective (enc a r)) : Function.Injective (enc a (a ++ r)) := by
  intro s t he
  apply recode_injective
  apply h
  simpa only [enc_recode] using he

private theorem swap_injective {α : Type u} (a b : List α)
    (h : Function.Injective (enc a b)) : Function.Injective (enc b a) := by
  have hs : ∀ s : List Bool, enc a b (s.map Bool.not) = enc b a s := by
    intro s
    induction s with
    | nil => rfl
    | cons t s ih =>
      cases t with
      | false => simpa [enc] using congrArg (fun w => b ++ w) ih
      | true => simpa [enc] using congrArg (fun w => a ++ w) ih
  intro s t he
  have e : s.map Bool.not = t.map Bool.not := h (by rw [hs, hs]; exact he)
  have ee := congrArg (List.map Bool.not) e
  simpa only [List.map_map, Function.comp_def, Bool.not_not,
    List.map_id_fun', id_def] using ee

/-- Labelled two-word unique decoding over an arbitrary alphabet is equivalent
    to noncommutation, including empty, equal and overlapping words. -/
theorem injective_iff_noncommuting {α : Type u} (a b : List α) :
    Function.Injective (fun s : List Bool => s.flatMap (fun t => if t then b else a)) ↔
      a ++ b ≠ b ++ a := by
  constructor
  · intro h hab
    have e : ([false, true] : List Bool) = [true, false] := h (by simpa using hab)
    cases e
  · intro hab
    have descent : ∀ N : Nat, ∀ a b : List α,
        a.length + b.length = N → a ++ b ≠ b ++ a → Function.Injective (enc a b) := by
      intro N
      induction N using Nat.strongRecOn with
      | ind N ih =>
        intro a b hN hn
        have ha : a ≠ [] := by intro e; subst a; simp at hn
        have hb : b ≠ [] := by intro e; subst b; simp at hn
        by_cases hp : a <+: b
        · obtain ⟨r, rfl⟩ := hp
          have hsmall : a.length + r.length < N := by
            simp only [List.length_append] at hN
            have := List.length_pos_iff.mpr ha
            omega
          have hnr : a ++ r ≠ r ++ a := by
            intro he
            apply hn
            simpa only [List.append_assoc] using congrArg (fun w => a ++ w) he
          exact extend_injective a r (ih _ hsmall a r rfl hnr)
        · by_cases hq : b <+: a
          · obtain ⟨r, rfl⟩ := hq
            have hsmall : b.length + r.length < N := by
              simp only [List.length_append] at hN
              have := List.length_pos_iff.mpr hb
              omega
            have hnr : b ++ r ≠ r ++ b := by
              intro he
              apply hn
              simpa only [List.append_assoc] using
                (congrArg (fun w => b ++ w) he).symm
            exact swap_injective b (b ++ r)
              (extend_injective b r (ih _ hsmall b r rfl hnr))
          · apply prefix_injective (fun t => if t then b else a)
            · intro i j he
              cases i <;> cases j <;> simp_all
            · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ he
              cases i <;> cases j <;> simp_all
            · rintro ⟨i, he⟩
              cases i <;> simp_all
    exact descent (a.length + b.length) a b rfl hab

end D5.S0.Computability.Coding.TwoWordCode
