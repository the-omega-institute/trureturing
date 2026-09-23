/- GID: D5/S3/Arith/Covering/MixedAffineQuotient
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/MixedAffineQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Guarded systems of original congruences admit exact mixed binary quotient coverage. -/

import D5.S3.Arith.Covering.BinaryAffineGeometry

set_option autoImplicit false

namespace D5.S3.Arith.Covering.MixedAffineQuotient

open BinaryCarryQuotient BinaryAffineGeometry

/-- Every event keeps its own row index type and its fixed original phase guard. -/
structure Event where
  Index : Type
  guard : Prop
  rows : Index → Row

def Event.covers (E : Event) (k l : ℤ) : Prop := E.guard ∧ ∀ j, (E.rows j).covers k l

def Event.carry (E : Event) (M k l u v : ℤ) : Prop := E.guard ∧ ∀ j,
  (E.rows j).active M k l ∧
    ((E.rows j).scaled M k l / M + (2 * M / (E.rows j).e) *
      ((E.rows j).a * u + (E.rows j).b * v)) % 2 = 0

/-- Homogeneous equations, with no phase variable and no nonzero-normal restriction. -/
def Event.kernel (E : Event) (M x y : ℤ) : Prop := ∀ j,
  2 ∣ (2 * M / (E.rows j).e) * ((E.rows j).a * x + (E.rows j).b * y)

/-- A shape witness consists of the original guarded event at one prescribed
lift, and the fixed homogeneous equations identifying its translated shape. -/
def Witness (E : Event) (M k l : ℤ) (s : Shape) : Prop :=
  E.covers (k + M * (s.anchor.1 : ℤ)) (l + M * (s.anchor.2 : ℤ)) ∧
    ∀ p : Point, E.kernel M ((p.1 : ℤ) - (s.anchor.1 : ℤ))
      ((p.2 : ℤ) - (s.anchor.2 : ℤ)) ↔ s.mem p

def Criterion {ι : Type*} (events : ι → Event) (M k l : ℤ) : Prop :=
  Alternatives (∃ i, Witness (events i) M k l .full)
    (fun d c => ∃ i, Witness (events i) M k l (.line d c))
    (fun p => ∃ i, Witness (events i) M k l (.point p))

/-- All participating original events are tested at shifts of this one lift.
The existential chooses a representative, never a new phase. -/
def ProjectedCriterion {ι : Type*} (events : ι → Event) (M k l : ℤ) : Prop :=
  ∃ z w : ℤ, Criterion events M (k + M * z) (l + M * w)

/-- Exact mixed descent. The conclusions expose the row activation equations,
the four possible slice types, exact original-event witnesses, the six-pattern
criterion, representative invariance, projection, and both global equivalences. -/
theorem result {ι : Type*} (events : ι → Event) (M : ℤ) (hM : 0 < M)
    (he : ∀ i j, 0 < ((events i).rows j).e ∧ ((events i).rows j).e ∣ 2 * M) :
    (∀ i k l u v, (events i).covers (k + M * u) (l + M * v) ↔
      (events i).carry M k l u v) ∧
    (∀ i k l, ∃ s : Shape, ∀ p : Point,
      (events i).covers (k + M * (p.1 : ℤ)) (l + M * (p.2 : ℤ)) ↔ s.mem p) ∧
    (∀ i k l s, Witness (events i) M k l s ↔ s ≠ .empty ∧ ∀ p : Point,
      (events i).covers (k + M * (p.1 : ℤ)) (l + M * (p.2 : ℤ)) ↔ s.mem p) ∧
    (∀ k l, (∀ p : Point, ∃ i,
      (events i).covers (k + M * (p.1 : ℤ)) (l + M * (p.2 : ℤ))) ↔
      Criterion events M k l) ∧
    (∀ k l z w, Criterion events M (k + M * z) (l + M * w) ↔
      Criterion events M k l) ∧
    (∀ k l, ProjectedCriterion events M k l ↔ Criterion events M k l) ∧
    ((∀ k l : ℤ, ∃ i, (events i).covers k l) ↔
      ∀ k l : ℤ, 0 ≤ k → k < M → 0 ≤ l → l < M → Criterion events M k l) ∧
    ((∀ k l : ℤ, 0 ≤ k → k < 2 * M → 0 ≤ l → l < 2 * M →
      ∃ i, (events i).covers k l) ↔
      ∀ k l : ℤ, 0 ≤ k → k < M → 0 ≤ l → l < M → Criterion events M k l) := by
  classical
  let q (i : ι) (j : (events i).Index) := 2 * M / ((events i).rows j).e
  have qe (i : ι) (j : (events i).Index) : q i j * ((events i).rows j).e = 2 * M :=
    Int.ediv_mul_cancel (he i j).2
  have scale (i : ι) (j : (events i).Index) (k l : ℤ) :
      ((events i).rows j).covers k l ↔ 2 * M ∣ ((events i).rows j).scaled M k l := by
    have qne : q i j ≠ 0 := by intro hz; have := qe i j; rw [hz] at this; omega
    change ((events i).rows j).e ∣ _ ↔ 2 * M ∣ q i j * _
    rw [← qe i j, Int.mul_dvd_mul_iff_left qne]
  have shift (i : ι) (j : (events i).Index) (k l u v : ℤ) :
      ((events i).rows j).scaled M (k + M * u) (l + M * v) =
      ((events i).rows j).scaled M k l + M *
        (q i j * (((events i).rows j).a * u + ((events i).rows j).b * v)) := by
    dsimp [Row.scaled,q]; ring
  have split (f t : ℤ) :
      (2 * M ∣ f + M * t) ↔ M ∣ f ∧ (f / M + t) % 2 = 0 := by
    constructor
    · intro h
      have hf : M ∣ f := by
        have h' : M ∣ f + M * t := dvd_trans (by exact ⟨2,by ring⟩) h
        exact (Int.dvd_add_left (dvd_mul_right M t)).mp h'
      refine ⟨hf,?_⟩
      rw [show f + M * t = M * (f / M + t) by
        rw [mul_add,Int.mul_ediv_cancel_of_dvd hf], mul_comm 2 M,
        Int.mul_dvd_mul_iff_left (ne_of_gt hM)] at h
      exact Int.emod_eq_zero_of_dvd h
    · rintro ⟨hf,ht⟩
      rw [show f + M * t = M * (f / M + t) by
        rw [mul_add,Int.mul_ediv_cancel_of_dvd hf], mul_comm 2 M,
        Int.mul_dvd_mul_iff_left (ne_of_gt hM)]
      exact Int.dvd_of_emod_eq_zero ht
  have lift (i : ι) (k l u v : ℤ) :
      (events i).covers (k + M * u) (l + M * v) ↔ (events i).carry M k l u v := by
    simp only [Event.covers,Event.carry]
    apply and_congr_right; intro _
    apply forall_congr'; intro j
    rw [scale,shift,split]
    rfl
  have transport (i : ι) (k l : ℤ) (a p : Point)
      (ha : (events i).covers (k + M * (a.1 : ℤ)) (l + M * (a.2 : ℤ))) :
      (events i).covers (k + M * (p.1 : ℤ)) (l + M * (p.2 : ℤ)) ↔
      (events i).kernel M ((p.1 : ℤ) - (a.1 : ℤ)) ((p.2 : ℤ) - (a.2 : ℤ)) := by
    rw [Event.covers, and_iff_right ha.1]
    apply forall_congr'; intro j
    have hj := (scale i j _ _).mp (ha.2 j)
    rw [scale]
    rw [show ((events i).rows j).scaled M (k + M * (p.1 : ℤ)) (l + M * (p.2 : ℤ)) =
      ((events i).rows j).scaled M (k + M * (a.1 : ℤ)) (l + M * (a.2 : ℤ)) +
      M * (q i j * (((events i).rows j).a * ((p.1 : ℤ) - (a.1 : ℤ)) +
        ((events i).rows j).b * ((p.2 : ℤ) - (a.2 : ℤ)))) by dsimp [Row.scaled,q]; ring]
    rw [Int.dvd_add_right hj, mul_comm 2 M, Int.mul_dvd_mul_iff_left (ne_of_gt hM)]
    simp only [q,mul_comm 2 M]
  have classification (i : ι) (k l : ℤ) : ∃ s : Shape, ∀ p : Point,
      (events i).covers (k + M * (p.1 : ℤ)) (l + M * (p.2 : ℤ)) ↔ s.mem p := by
    let S (p : Point) := (events i).covers (k + M * (p.1 : ℤ)) (l + M * (p.2 : ℤ))
    have rect (p q r s : Point)
        (hx : (p.1 : ℤ) + (q.1 : ℤ) = (r.1 : ℤ) + (s.1 : ℤ))
        (hy : (p.2 : ℤ) + (q.2 : ℤ) = (r.2 : ℤ) + (s.2 : ℤ)) :
        S p → S q → S r → S s := by
      intro hp hq hr
      refine ⟨hp.1,?_⟩
      intro j
      let row := (events i).rows j
      let f (t : Point) := row.a * (k + M * (t.1 : ℤ)) +
        row.b * (l + M * (t.2 : ℤ)) - row.c
      have identity : f s = f p + f q - f r := by
        dsimp [f]
        linear_combination -M * row.a * hx - M * row.b * hy
      change row.e ∣ f s
      rw [identity]
      exact dvd_sub (dvd_add (hp.2 j) (hq.2 j)) (hr.2 j)
    have c₁ : S (0,0) → S (0,1) → S (1,0) → S (1,1) :=
      fun a b c => rect (0,1) (1,0) (0,0) (1,1) (by norm_num) (by norm_num) b c a
    have c₂ : S (0,0) → S (0,1) → S (1,1) → S (1,0) :=
      fun a b c => rect (0,0) (1,1) (0,1) (1,0) (by norm_num) (by norm_num) a c b
    have c₃ : S (0,0) → S (1,0) → S (1,1) → S (0,1) :=
      fun a b c => rect (0,0) (1,1) (1,0) (0,1) (by norm_num) (by norm_num) a c b
    have c₄ : S (0,1) → S (1,0) → S (1,1) → S (0,0) :=
      fun a b c => rect (0,1) (1,0) (1,1) (0,0) (by norm_num) (by norm_num) a b c
    change ∃ s : Shape, ∀ p : Point, S p ↔ s.mem p
    by_cases h₀ : S (0,0) <;> by_cases h₁ : S (0,1) <;>
      by_cases h₂ : S (1,0) <;> by_cases h₃ : S (1,1)
    · refine ⟨.full,?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,h₀,h₁,h₂,h₃]
    · exact False.elim (h₃ (c₁ h₀ h₁ h₂))
    · exact False.elim (h₂ (c₂ h₀ h₁ h₃))
    · refine ⟨.line 0 0,?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,coord,h₀,h₁,h₂,h₃]
    · exact False.elim (h₁ (c₃ h₀ h₂ h₃))
    · refine ⟨.line 1 0,?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,coord,h₀,h₁,h₂,h₃]
    · refine ⟨.line 2 0,?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,coord,Fin.reduceAdd,h₀,h₁,h₂,h₃]
    · refine ⟨.point (0,0),?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,h₀,h₁,h₂,h₃]
    · exact False.elim (h₀ (c₄ h₁ h₂ h₃))
    · refine ⟨.line 2 1,?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,coord,Fin.reduceAdd,h₀,h₁,h₂,h₃]
    · refine ⟨.line 1 1,?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,coord,h₀,h₁,h₂,h₃]
    · refine ⟨.point (0,1),?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,h₀,h₁,h₂,h₃]
    · refine ⟨.line 0 1,?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,coord,h₀,h₁,h₂,h₃]
    · refine ⟨.point (1,0),?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,h₀,h₁,h₂,h₃]
    · refine ⟨.point (1,1),?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,h₀,h₁,h₂,h₃]
    · refine ⟨.empty,?_⟩
      simp [Prod.forall,Fin.forall_fin_two,Shape.mem,h₀,h₁,h₂,h₃]
  have witness (i : ι) (k l : ℤ) (s : Shape) : Witness (events i) M k l s ↔
      s ≠ .empty ∧ ∀ p : Point,
        (events i).covers (k + M * (p.1 : ℤ)) (l + M * (p.2 : ℤ)) ↔ s.mem p := by
    have anchor : ∀ s : Shape, s ≠ .empty → s.mem s.anchor := by decide
    constructor
    · rintro ⟨ha,hs⟩
      have exactShape (p : Point) := (transport i k l s.anchor p ha).trans (hs p)
      refine ⟨?_,exactShape⟩
      intro hz; subst s; exact (exactShape _).mp ha
    · rintro ⟨hne,hs⟩
      have ha := (hs s.anchor).mpr (anchor s hne)
      exact ⟨ha,fun p => (transport i k l s.anchor p ha).symm.trans (hs p)⟩
  have local_equiv (k l : ℤ) : (∀ p : Point, ∃ i,
      (events i).covers (k + M * (p.1 : ℤ)) (l + M * (p.2 : ℤ))) ↔
      Criterion events M k l := by
    rw [Criterion, ← (mixed_cover_iff _ _ _).1]
    apply forall_congr'; intro p
    constructor
    · rintro ⟨i,hi⟩
      obtain ⟨s,hs⟩ := classification i k l
      have hm := (hs p).mp hi
      cases s with
      | empty => exact False.elim hm
      | full => exact Or.inl ⟨i,(witness i k l _).mpr ⟨by decide,hs⟩⟩
      | line d c =>
        exact Or.inr (Or.inl ⟨d,i,(witness i k l _).mpr ⟨by simp, hm.symm ▸ hs⟩⟩)
      | point q =>
        exact Or.inr (Or.inr ⟨i,(witness i k l _).mpr ⟨by simp, hm.symm ▸ hs⟩⟩)
    · rintro (⟨i,hi⟩ | ⟨d,i,hi⟩ | ⟨i,hi⟩) <;>
        exact ⟨i,((witness i k l _).mp hi).2 p |>.mpr (by simp [Shape.mem])⟩
  let bit (z : ℤ) : Fin 2 := ⟨(z % 2).toNat,by omega⟩
  have bitval (z : ℤ) : ((bit z : Fin 2) : ℤ) = z % 2 := by dsimp [bit]; omega
  have all_lifts (k l : ℤ) :
      (∀ p : Point, ∃ i, (events i).covers (k + M * (p.1 : ℤ)) (l + M * (p.2 : ℤ))) ↔
      ∀ z w : ℤ, ∃ i, (events i).covers (k + M * z) (l + M * w) := by
    constructor
    · intro h z w
      obtain ⟨i,hi⟩ := h (bit z,bit w)
      refine ⟨i,?_⟩
      rw [lift] at hi ⊢
      simpa only [Event.carry,bitval,Int.add_emod,Int.mul_emod,Int.emod_emod] using hi
    · intro h p; exact h _ _
  have invariant (k l z w : ℤ) :
      Criterion events M (k + M * z) (l + M * w) ↔ Criterion events M k l := by
    rw [← local_equiv,← local_equiv,all_lifts,all_lifts]
    constructor
    · intro h s t
      simpa only [show k + M * z + M * (s-z) = k + M*s by ring,
        show l + M*w + M*(t-w) = l + M*t by ring] using h (s-z) (t-w)
    · intro h s t
      simpa only [show k + M*(z+s) = k + M*z + M*s by ring,
        show l + M*(w+t) = l + M*w + M*t by ring] using h (z+s) (w+t)
  have global_equiv : (∀ k l : ℤ, ∃ i, (events i).covers k l) ↔
      ∀ k l : ℤ, 0 ≤ k → k < M → 0 ≤ l → l < M → Criterion events M k l := by
    constructor
    · intro h k l _ _ _ _; exact (local_equiv k l).mp (fun p => h _ _)
    · intro h k l
      have hb := h (k%M) (l%M) (Int.emod_nonneg _ (ne_of_gt hM))
        (Int.emod_lt_of_pos _ hM) (Int.emod_nonneg _ (ne_of_gt hM)) (Int.emod_lt_of_pos _ hM)
      have hf := (all_lifts _ _).mp ((local_equiv _ _).mpr hb)
      simpa only [Int.emod_add_mul_ediv] using hf (k/M) (l/M)
  refine ⟨lift,classification,witness,local_equiv,invariant,?_,global_equiv,?_⟩
  · intro k l
    constructor
    · rintro ⟨z,w,h⟩; exact (invariant k l z w).mp h
    · intro h; exact ⟨0,0,by simpa using h⟩
  · constructor
    · intro h k l hk hkM hl hlM
      apply (local_equiv k l).mp
      rintro ⟨u,v⟩
      have hu : 0 ≤ (u : ℤ) ∧ (u : ℤ) < 2 := ⟨by positivity,by exact_mod_cast u.isLt⟩
      have hv : 0 ≤ (v : ℤ) ∧ (v : ℤ) < 2 := ⟨by positivity,by exact_mod_cast v.isLt⟩
      exact h _ _ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
    · intro h k l _ _ _ _; exact global_equiv.mpr h k l

end D5.S3.Arith.Covering.MixedAffineQuotient
