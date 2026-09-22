/- GID: D5/S3/Arith/Covering/BinaryAffineGeometry
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/BinaryAffineGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Mixed binary affine covers contain one of the six minimal geometric configurations. -/

import D5.S3.Arith.Covering.BinaryCarryQuotient

set_option autoImplicit false

namespace D5.S3.Arith.Covering.BinaryAffineGeometry

abbrev Point := Fin 2 × Fin 2

/-- The three nonzero binary linear forms, in the order x, y, x+y. -/
def coord (d : Fin 3) (p : Point) : Fin 2 := ![p.1, p.2, p.1 + p.2] d

inductive Shape where
  | empty | full | line (d : Fin 3) (c : Fin 2) | point (p : Point)
  deriving DecidableEq, Fintype

def Shape.mem : Shape → Point → Prop
  | .empty, _ => False
  | .full, _ => True
  | .line d c, p => coord d p = c
  | .point q, p => p = q

instance (s : Shape) (p : Point) : Decidable (s.mem p) := by
  cases s <;> unfold Shape.mem <;> infer_instance

def Shape.anchor : Shape → Point
  | .point p => p
  | .line d c => if d = 1 then (0,c) else (c,0)
  | _ => (0,0)

/-- Availability refers to exact sets, so inactive and repeated events cause no ambiguity. -/
def Alternatives (F : Prop) (L : Fin 3 → Fin 2 → Prop) (P : Point → Prop) : Prop :=
  F ∨ (∃ d, L d 0 ∧ L d 1) ∨
  (∃ p : Point, L 0 p.1 ∧ L 1 p.2 ∧ L 2 (p.1 + p.2)) ∨
  (∃ d e p, d ≠ e ∧ L d (1 - coord d p) ∧ L e (1 - coord e p) ∧ P p) ∨
  (∃ d c, L d c ∧ ∀ p, coord d p ≠ c → P p) ∨ (∀ p, P p)

/-- Each unordered pair of directions occurs once, via its omitted direction. -/
inductive Pattern where
  | full | parallel (d : Fin 3) | pencil (p : Point)
  | corner (omitted : Fin 3) (p : Point)
  | linePoints (d : Fin 3) (c : Fin 2) | points
  deriving DecidableEq, Fintype

def Pattern.shapes : Pattern → Finset Shape
  | .full => {.full}
  | .parallel d => {.line d 0, .line d 1}
  | .pencil p => {.line 0 p.1, .line 1 p.2, .line 2 (p.1 + p.2)}
  | .corner d p => {.line (d+1) (1 - coord (d+1) p),
      .line (d+2) (1 - coord (d+2) p), .point p}
  | .linePoints d c => {.line d c} ∪
      (Finset.univ.filter (fun p : Point => coord d p ≠ c)).image Shape.point
  | .points => Finset.univ.image Shape.point

/-- Every selected set has a private point, hence no proper subfamily covers. -/
def MinimalCover (C : Finset Shape) : Prop :=
  (∀ p : Point, ∃ s ∈ C, s.mem p) ∧
    ∀ s ∈ C, ∃ p : Point, s.mem p ∧ ∀ t ∈ C, t.mem p → t = s

instance (C : Finset Shape) : Decidable (MinimalCover C) := by
  unfold MinimalCover; infer_instance

/-- Completeness is proved by separating the line cover from its uncovered points.
The pure-line branch uses the existing line-cover theorem. In the other branch,
two directions leave one point, one direction leaves a complementary pair, and
no directions leave all four points. No finiteness assumption on the event
family is needed: F, L and P may themselves be existential availabilities. -/
theorem mixed_cover_iff (F : Prop) (L : Fin 3 → Fin 2 → Prop) (P : Point → Prop) :
    ((∀ p : Point, F ∨ (∃ d, L d (coord d p)) ∨ P p) ↔ Alternatives F L P) ∧
    (Fintype.card Pattern = 27 ∧ Function.Injective Pattern.shapes) ∧
    (∀ t : Pattern, MinimalCover t.shapes) := by
  refine ⟨?_, ?_⟩
  · classical
    have bits (a b : Fin 2) : a ≠ b ↔ a = 1 - b := by decide +revert
    have pairGeom (d e : Fin 3) (p q : Point) (hne : d ≠ e) :
        coord d q = 1 - coord d p ∨ coord e q = 1 - coord e p ∨ q = p := by
      revert d e p q; decide
    have pencilGeom (p q : Point) :
        q.1 = p.1 ∨ q.2 = p.2 ∨ q.1 + q.2 = p.1 + p.2 := by
      revert p q; decide
    constructor
    · intro cover
      by_cases hf : F
      · exact Or.inl hf
      have cov (p : Point) : (∃ d, L d (coord d p)) ∨ P p := (cover p).resolve_left hf
      by_cases parallel : ∃ d, L d 0 ∧ L d 1
      · exact Or.inr (Or.inl parallel)
      have unique (d : Fin 3) (a b : Fin 2) (ha : L d a) (hb : L d b) : a = b := by
        fin_cases a <;> fin_cases b <;> first | rfl | exact False.elim (parallel ⟨d, by tauto⟩)
      by_cases lines : ∀ p : Point, ∃ d, L d (coord d p)
      · let a (i : Fin 3 × Fin 2) : Fin 2 := if i.1 = 1 then 0 else 1
        let b (i : Fin 3 × Fin 2) : Fin 2 := if i.1 = 0 then 0 else 1
        have eqn (d : Fin 3) (c u v : Fin 2) :
            ((a (d,c) : ℤ) * (u : ℤ) + (b (d,c) : ℤ) * (v : ℤ) + (c : ℤ)) % 2 = 0 ↔
              coord d (u,v) = c := by
          revert d c u v; decide
        have lc : ∀ u v : Fin 2, ∃ i : Fin 3 × Fin 2, L i.1 i.2 ∧
            ((a i : ℤ) * (u : ℤ) + (b i : ℤ) * (v : ℤ) + (i.2 : ℤ)) % 2 = 0 := by
          intro u v
          obtain ⟨d, hd⟩ := lines (u,v)
          exact ⟨(d,coord d (u,v)), hd, (eqn _ _ _ _).mpr rfl⟩
        have hn : ∀ i : Fin 3 × Fin 2, L i.1 i.2 → a i ≠ 0 ∨ b i ≠ 0 := by
          rintro ⟨d,c⟩ _; fin_cases d <;> norm_num [a,b]
        rcases (BinaryCarryQuotient.plane_cover_iff (fun i => L i.1 i.2) a b
          (fun i => i.2) hn).mp lc with h | h
        · obtain ⟨⟨d,c⟩, ⟨e,t⟩, hd, he, ha, hb, hct⟩ := h
          have inj : ∀ d e : Fin 3, a (d,c) = a (e,t) → b (d,c) = b (e,t) → d = e := by
            intro d' e'; fin_cases d' <;> fin_cases e' <;> norm_num [a,b]
          have de : d = e := inj d e ha hb
          exact False.elim (hct (unique d c t hd (de ▸ he)))
        · obtain ⟨⟨d,c⟩, ⟨e,t⟩, ⟨f,s⟩, hd, he, hf', hde, hdf, hef, hsum⟩ := h
          have de : d ≠ e := by intro h; subst e; exact hde rfl
          have df : d ≠ f := by intro h; subst f; exact hdf rfl
          have ef : e ≠ f := by intro h; subst f; exact hef rfl
          have concurrency : ∀ (d e f : Fin 3) (c t s : Fin 2),
              d ≠ e → d ≠ f → e ≠ f → ((c : ℤ) + (t : ℤ) + (s : ℤ)) % 2 = 0 →
              ∃ p : Point, coord d p = c ∧ coord e p = t ∧ coord f p = s := by decide
          obtain ⟨p,hp,hq,hr⟩ := concurrency d e f c t s de df ef hsum
          have all (g : Fin 3) : L g (coord g p) := by
            have which : g = d ∨ g = e ∨ g = f := by omega
            rcases which with rfl | rfl | rfl
            · exact hp.symm ▸ hd
            · exact hq.symm ▸ he
            · exact hr.symm ▸ hf'
          exact Or.inr (Or.inr (Or.inl ⟨p,all 0,all 1,all 2⟩))
      · push Not at lines
        obtain ⟨p, hp⟩ := lines
        have pp : P p := (cov p).resolve_left (by simpa using hp)
        by_cases two : ∃ d e c t, d ≠ e ∧ L d c ∧ L e t
        · obtain ⟨d,e,c,t,hde,hd,he⟩ := two
          have hc : c = 1 - coord d p := (bits _ _).mp (fun h => hp d (h ▸ hd))
          have ht : t = 1 - coord e p := (bits _ _).mp (fun h => hp e (h ▸ he))
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d,e,p,hde,hc ▸ hd,ht ▸ he,pp⟩)))
        by_cases one : ∃ d c, L d c
        · obtain ⟨d,c,hd⟩ := one
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
          refine ⟨d,c,hd,?_⟩
          intro q hq
          rcases cov q with ⟨e,he⟩ | hq'
          · have de : d = e := by by_contra hn; exact two ⟨d,e,c,coord e q,hn,hd,he⟩
            subst e
            exact False.elim (hq (unique d _ _ he hd))
          · exact hq'
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (fun q =>
            (cov q).resolve_left (fun ⟨d,hd⟩ => one ⟨d,_,hd⟩))))))
    · intro h p
      rcases h with hf | ⟨d,h₀,h₁⟩ | ⟨q,hx,hy,hz⟩ | ⟨d,e,q,hde,hd,he,hq⟩ |
        ⟨d,c,hd,hp⟩ | hp
      · exact Or.inl hf
      · right; left; use d
        rcases (show coord d p = 0 ∨ coord d p = 1 by omega) with h | h <;> simpa [h]
      · right; left
        rcases pencilGeom q p with hx' | hy' | hz'
        · exact ⟨0, by simpa [coord,hx'] using hx⟩
        · exact ⟨1, by simpa [coord,hy'] using hy⟩
        · exact ⟨2, by simpa [coord,hz'] using hz⟩
      · right
        rcases pairGeom d e q p hde with hd' | he' | hp'
        · exact Or.inl ⟨d, hd' ▸ hd⟩
        · exact Or.inl ⟨e, he' ▸ he⟩
        · exact Or.inr (hp' ▸ hq)
      · right
        by_cases hc : coord d p = c
        · exact Or.inl ⟨d,hc ▸ hd⟩
        · exact Or.inr (hp p hc)
      · exact Or.inr (Or.inr (hp p))
  · exact ⟨⟨by decide, by decide⟩, by decide⟩

end D5.S3.Arith.Covering.BinaryAffineGeometry
