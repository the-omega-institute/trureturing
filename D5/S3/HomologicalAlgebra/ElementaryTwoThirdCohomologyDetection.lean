/- GID: D5/S3/HomologicalAlgebra/ElementaryTwoThirdCohomologyDetection
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/ElementaryTwoThirdCohomologyDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality, mathlib/module/Mathlib.Algebra.Module.Projective]
   utility: none
   digest: Actual third cohomology of finite elementary two-groups is detected by all cyclic restrictions for coefficients with surjective doubling. -/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection
open CategoryTheory groupCohomology

set_option maxHeartbeats 2400000 in
/-- For surjective doubling coefficients, all nonidentity cyclic subgroup restrictions
jointly detect actual degree-three cohomology, including rank zero. -/
theorem cyclic_restriction_detects_third_cohomology
    (M : Type) [AddCommGroup M] (half : ∀ m : M, ∃ k, k + k = m)
    (r : ℕ)
    (c : groupCohomology (Rep.trivial ℤ (Multiplicative (Fin r → ZMod 2)) M) 3)
    (hr : ∀ g : Multiplicative (Fin r → ZMod 2), g ≠ 1 →
      groupCohomology.map (Subgroup.zpowers g).subtype (𝟙 _) 3 c = 0) : c = 0 := by
  classical
  let E (r : ℕ) := Multiplicative (Fin r → ZMod 2)
  let Q := Multiplicative (ZMod 2)
  let d2 {G : Type} [CommGroup G] (B : G → G → M) (a b c : G) : M := B b c - B (a * b) c + B a (b * c) - B a b
  let d3 {G : Type} [CommGroup G] (f : G → G → G → M) (a b c d : G) : M := f b c d - f (a * b) c d + f a (b * c) d - f a b (c * d) + f a b c
  have d2d3 {G : Type} [CommGroup G] (B : G → G → M) (a b c d : G) : d3 (d2 B) a b c d = 0 := by
    simp only [d3, d2, mul_assoc]
    abel
  have normalization {G : Type} [CommGroup G] (f : G → G → G → M) (hf : ∀ a b c d, d3 f a b c d = 0) :
      ∃ N : G → G → M, ∀ a b, (f 1 a b - d2 N 1 a b = 0) ∧
        (f a 1 b - d2 N a 1 b = 0) ∧ (f a b 1 - d2 N a b 1 = 0) := by
    let N : G → G → M := fun a b => f 1 1 b - f a 1 1
    refine ⟨N, ?_⟩
    have h0 : f 1 1 1 = 0 := by simpa [d3] using hf 1 1 1 1
    intro a b
    have h1 := hf 1 1 a b
    have h2 := hf a 1 1 b
    have h3 := hf a b 1 1
    simp only [d3, one_mul, mul_one, h0] at h1 h2 h3
    dsimp [d2, N]
    simp only [one_mul, mul_one, h0]
    constructor
    · linear_combination (norm := abel) h1
    constructor
    · linear_combination (norm := abel) -h2
    · linear_combination (norm := abel) h3
  have comparison {G H : Type} [CommGroup G] [CommGroup H] (f : G × H → G × H → G × H → M)
      (hf : ∀ a b c d, d3 f a b c d = 0) (a b c : G) (x y z : H) :
    let A : G × H := (a,1); let B : G × H := (b,1); let C : G × H := (c,1)
    let X : G × H := (1,x); let Y : G × H := (1,y); let Z : G × H := (1,z)
    let β : G × H → G × H → M := fun s t =>
      -f (1,s.2) (s.1,1) t + f (s.1,1) (1,t.2) (t.1,1) -
        f (1,t.2) (s.1,1) (t.1,1) + f (1,s.2) (1,t.2) (s.1*t.1,1)
    f (a,x) (b,y) (c,z) = f A B C +
      (f A B Z - f A Z B + f Z A B) +
      (f A Y Z - f Y A Z + f Y Z A) + f X Y Z + d2 β (a,x) (b,y) (c,z) := by
    dsimp only
    have h1 := hf (1,x) (a,1) (b,y) (c,z)
    have h2 := hf (1,x) (1,y) (a * b,1) (c,z)
    have h3 := hf (1,x) (1,y) (1,z) (a * b * c,1)
    have h4 := hf (1,y) (a,1) (b,1) (c,z)
    have h5 := hf (a,1) (1,y) (b,1) (c,z)
    have h6 := hf (1,y) (1,z) (a,1) (b * c,1)
    have h7 := hf (1,y) (a,1) (1,z) (b * c,1)
    have h8 := hf (a,1) (1,y) (1,z) (b * c,1)
    have h9 := hf (a,1) (b,1) (1,z) (c,1)
    have h10 := hf (a,1) (1,z) (b,1) (c,1)
    have h11 := hf (1,z) (a,1) (b,1) (c,1)
    simp only [d3, Prod.mul_def, one_mul, mul_one, mul_assoc] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp only [d2, Prod.mul_def, mul_assoc]
    linear_combination (norm := abel) -h1 + h2 - h3 - h4 + h5 - h6 + h7 - h8 - h9 + h10 - h11
  have splitting (r : ℕ) (F : (Fin r → ZMod 2) → (Fin r → ZMod 2) → M)
      (hc : ∀ a b c, F a b + F (a + b) c = F b c + F a (b + c))
      (hdiag : ∀ a, F a a = 0) (htwo : ∀ a b, F a b + F a b = 0) :
      ∃ b : (Fin r → ZMod 2) → M, b 0 = 0 ∧
        (∀ a, b a + b a = 0) ∧ (∀ a c, F a c = b c - b (a + c) + b a) := by
    classical
    let V := Fin r → ZMod 2
    have aa : ∀ a : V, a+a = 0 := fun a => by ext i; exact CharTwo.add_self_eq_zero (a i)
    have F0 : ∀ a, F 0 a = 0 := by
      intro a
      have h := hc 0 0 a
      simpa [hdiag 0] using h
    have Fz : ∀ a, F a 0 = 0 := by
      intro a
      have h := hc a 0 0
      simpa [hdiag 0] using h
    have Fs : ∀ a b, F a b = F b a := by
      intro a b
      have h1 := hc a b (a + b)
      have h2 := hc b b a
      have h3 := htwo b (a + b)
      have ba : b+(a + b) = a := by
        calc b+(a + b) = (b+b)+a := by abel
             _ = a := by rw [aa, zero_add]
      simp only [hdiag, aa, F0, ba, add_zero, zero_add, add_comm b a] at h1 h2
      linear_combination (norm := abel) h1 + h2 + h3
    let K : AddSubgroup M := {
      carrier := {m | m+m = 0}
      zero_mem' := by simp
      add_mem' := by intros a b ha hb; change (a + b)+(a + b)=0; rw [add_add_add_comm, ha, hb, add_zero]
      neg_mem' := by intro a ha; change -a + -a = 0; rw [← neg_add, ha, neg_zero] }
    let Fk : V → V → K := fun a b => ⟨F a b, htwo a b⟩
    let X := {p : K × V // True}
    letI : Add X := ⟨fun s t => ⟨(s.val.1+t.val.1+Fk s.val.2 t.val.2, s.val.2+t.val.2), trivial⟩⟩
    letI : Zero X := ⟨⟨(0,0), trivial⟩⟩
    letI : Neg X := ⟨id⟩
    letI : AddGroup X := AddGroup.ofLeftAxioms
      (fun s t u => by
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          change (s.val.1.val+t.val.1.val+F s.val.2 t.val.2)+u.val.1.val+F (s.val.2+t.val.2) u.val.2 =
            s.val.1.val+(t.val.1.val+u.val.1.val+F t.val.2 u.val.2)+F s.val.2 (t.val.2+u.val.2)
          linear_combination (norm := abel) hc s.val.2 t.val.2 u.val.2
        · exact add_assoc _ _ _)
      (fun s => by
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          change 0+s.val.1.val+F 0 s.val.2 = s.val.1.val
          rw [F0]; abel
        · exact zero_add _)
      (fun s => by
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          change s.val.1.val+s.val.1.val+F s.val.2 s.val.2 = 0
          rw [hdiag, s.val.1.property, add_zero]
        · exact aa s.val.2)
    letI : AddCommGroup X := { (inferInstance : AddGroup X) with
      add_comm := fun s t => by
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          change s.val.1.val+t.val.1.val+F s.val.2 t.val.2 = t.val.1.val+s.val.1.val+F t.val.2 s.val.2
          rw [Fs]; abel
        · exact add_comm _ _ }
    have xtwo : ∀ s : X, 2 • s = 0 := by
      intro s
      rw [two_nsmul]
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        change s.val.1.val+s.val.1.val+F s.val.2 s.val.2 = 0
        rw [hdiag, s.val.1.property, add_zero]
      · exact aa s.val.2
    letI : Module (ZMod 2) X := AddCommGroup.zmodModule xtwo
    let q : X →+ V := {
      toFun := fun x => x.val.2
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    let ql : X →ₗ[ZMod 2] V := q.toZModLinearMap 2
    have qsurj : LinearMap.range ql = ⊤ := LinearMap.range_eq_top.mpr (fun a => ⟨⟨(0,a), trivial⟩, rfl⟩)
    obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective ql qsurj
    have ss : ∀ a, (s a).val.2 = a := fun a => LinearMap.congr_fun hs a
    refine ⟨fun a => (s a).val.1.val, ?_, ?_, ?_⟩
    · have h := s.map_zero
      exact congrArg (fun x : X => x.val.1.val) h
    · intro a; exact (s a).val.1.property
    · intro a c
      have h := congrArg (fun x : X => x.val.1.val) (s.map_add a c)
      change (s (a + c)).val.1.val = (s a).val.1.val+(s c).val.1.val+F (s a).val.2 (s c).val.2 at h
      rw [ss, ss] at h
      change F a c = (s c).val.1.val - (s (a + c)).val.1.val + (s a).val.1.val
      rw [h, add_comm (s a).val.1.val (s c).val.1.val,
        sub_add_eq_sub_sub, sub_add_eq_sub_sub, sub_self, zero_sub,
        sub_eq_add_neg, add_right_comm, neg_add_cancel, zero_add]
      exact (eq_neg_iff_add_eq_zero).mpr (htwo a c)
  have productDescent (r : ℕ) (half : ∀ m : M, ∃ k, k+k=m)
      (ih : ∀ f : E r → E r → E r → M,
        (∀ a b c d, d3 f a b c d = 0) →
        (∀ a b, f 1 a b = 0 ∧ f a 1 b = 0 ∧ f a b 1 = 0) →
        (∀ a, f a a a = 0) → ∃ B, ∀ a b c, d2 B a b c = f a b c)
      (F : E r × Q → E r × Q → E r × Q → M)
      (hc : ∀ a b c d, d3 F a b c d = 0)
      (hn : ∀ a b, F 1 a b = 0 ∧ F a 1 b = 0 ∧ F a b 1 = 0)
      (hd : ∀ a, F a a a = 0) : ∃ B, ∀ a b c, d2 B a b c = F a b c := by
    classical
    let T : Q := Multiplicative.ofAdd (1 : ZMod 2)
    have TT : T*T=1 := by decide
    have Tne : T ≠ 1 := by decide
    have casesQ : ∀ x : Q, x=1 ∨ x=T := by
      intro x
      fin_cases x
      · exact Or.inl rfl
      · exact Or.inr rfl
    have onepair : ((1 : E r),(1 : Q)) = (1 : E r × Q) := rfl
    have hn1 : ∀ a b, F 1 a b = 0 := fun a b => (hn a b).1
    have hn2 : ∀ a b, F a 1 b = 0 := fun a b => (hn a b).2.1
    have hn3 : ∀ a b, F a b 1 = 0 := fun a b => (hn a b).2.2
    let β : E r × Q → E r × Q → M := fun s t =>
      -F (1,s.2) (s.1,1) t + F (s.1,1) (1,t.2) (t.1,1) -
        F (1,t.2) (s.1,1) (t.1,1) + F (1,s.2) (1,t.2) (s.1*t.1,1)
    have β1 : ∀ a, β 1 a = 0 := by intro a; simp [β, onepair, hn1, hn2, hn3]
    have β2 : ∀ a, β a 1 = 0 := by intro a; simp [β, onepair, hn1, hn2, hn3]
    let P := fun a b c => F a b c - d2 β a b c
    have pc : ∀ a b c d, d3 P a b c d = 0 := by
      intro a b c d
      have h := hc a b c d
      have hB := d2d3 β a b c d
      dsimp [P, d3] at *
      linear_combination (norm := abel) h - hB
    have pn : ∀ a b, P 1 a b = 0 ∧ P a 1 b = 0 ∧ P a b 1 = 0 := by
      intro a b
      simp [P, d2, onepair, hn1, hn2, hn3, β1, β2]
    have pd : ∀ a, P a a a = 0 := by
      intro a
      have aa : a*a=1 := by
        apply Prod.ext
        · apply Multiplicative.ofAdd.injective; ext i; exact CharTwo.add_self_eq_zero _
        · change a.2*a.2=1
          rcases casesQ a.2 with h | h <;> rw [h] <;> simp [TT]
      simp [P, d2, aa, hd, β1, β2]
    let fg : E r → E r → E r → M := fun a b c => F (a,1) (b,1) (c,1)
    let u : E r → E r → M := fun a b =>
      F (a,1) (b,1) (1,T) - F (a,1) (1,T) (b,1) + F (1,T) (a,1) (b,1)
    let v : E r → M := fun a =>
      F (a,1) (1,T) (1,T) - F (1,T) (a,1) (1,T) + F (1,T) (1,T) (a,1)
    have comp : ∀ a b c x y z,
      P (a,x) (b,y) (c,z) = fg a b c +
        (F (a,1) (b,1) (1,z) - F (a,1) (1,z) (b,1) + F (1,z) (a,1) (b,1)) +
        (F (a,1) (1,y) (1,z) - F (1,y) (a,1) (1,z) + F (1,y) (1,z) (a,1)) +
        F (1,x) (1,y) (1,z) := by
      intro a b c x y z
      have h := comparison F hc a b c x y z
      change F (a,x) (b,y) (c,z) = _ + d2 β (a,x) (b,y) (c,z) at h
      dsimp [P, fg]
      linear_combination (norm := abel) h
    have form : ∀ a b c x y z,
      P (a,x) (b,y) (c,z) = fg a b c + (if z=1 then 0 else u a b) +
        (if y=1 then 0 else if z=1 then 0 else v a) := by
      intro a b c x y z
      rw [comp]
      rcases casesQ x with rfl | rfl <;>
        rcases casesQ y with rfl | rfl <;>
        rcases casesQ z with rfl | rfl <;>
        simp [u, v, onepair, hn1, hn2, hn3, Tne, hd (1,T)]
    have u1 : ∀ a, u a 1 = 0 := by intro a; simp [u, onepair, hn1, hn2, hn3]
    have uc : ∀ a b c, u a b + u (a * b) c = u b c + u a (b * c) := by
      intro a b c
      have h := pc (a,1) (b,1) (c,1) (1,T)
      simp [d3, Prod.mul_def, form, fg, onepair, hn1, hn2, hn3, Tne] at h
      linear_combination (norm := abel) -h
    have joint : ∀ a b, u a b + u a b + (v b - v (a * b) + v a) = 0 := by
      intro a b
      have h := pc (a,1) (b,1) (1,T) (1,T)
      simp [d3, Prod.mul_def, form, fg, onepair, hn1, hn2, hn3, u1, Tne, TT] at h
      linear_combination (norm := abel) h
    have uvdiag : ∀ a, u a a + v a = 0 := by
      intro a
      have h := pd (a,T)
      simpa [form, fg, hd, Tne] using h
    have v1 : v 1 = 0 := by simp [v, onepair, hn1, hn2, hn3]
    have halves : ∀ a, ∃ k, (a=1 → k=0) ∧ k+k = -v a := by
      intro a
      by_cases ha : a=1
      · subst a; exact ⟨0, fun _ => rfl, by simp [v1]⟩
      · obtain ⟨k,hk⟩ := half (-v a); exact ⟨k, fun h => (ha h).elim, hk⟩
    choose k kzero ktwo using halves
    have k1 : k 1 = 0 := kzero 1 rfl
    let U : (Fin r → ZMod 2) → (Fin r → ZMod 2) → M := fun a b =>
      u (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) -
        (k (Multiplicative.ofAdd b) - k (Multiplicative.ofAdd (a + b)) + k (Multiplicative.ofAdd a))
    have Uc : ∀ a b c, U a b + U (a + b) c = U b c + U a (b + c) := by
      intro a b c
      have h := uc (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) (Multiplicative.ofAdd c)
      dsimp [U]
      change u (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) +
        u (Multiplicative.ofAdd (a + b)) (Multiplicative.ofAdd c) =
        u (Multiplicative.ofAdd b) (Multiplicative.ofAdd c) +
        u (Multiplicative.ofAdd a) (Multiplicative.ofAdd (b + c)) at h
      simp only [← ofAdd_add, add_assoc] at *
      linear_combination (norm := abel) h
    have Ud : ∀ a, U a a = 0 := by
      intro a
      have aa : a+a=0 := by ext i; exact CharTwo.add_self_eq_zero _
      have h := uvdiag (Multiplicative.ofAdd a)
      have hh := ktwo (Multiplicative.ofAdd a)
      dsimp [U]
      simp only [← ofAdd_add]
      rw [aa, show Multiplicative.ofAdd (0 : Fin r → ZMod 2) = 1 from rfl, k1]
      linear_combination (norm := abel) h - hh
    have Ut : ∀ a b, U a b + U a b = 0 := by
      intro a b
      have h := joint (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
      have h1 := ktwo (Multiplicative.ofAdd a)
      have h2 := ktwo (Multiplicative.ofAdd b)
      have h3 := ktwo (Multiplicative.ofAdd (a + b))
      dsimp [U]
      change u (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) +
        u (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) +
        (v (Multiplicative.ofAdd b) - v (Multiplicative.ofAdd (a + b)) + v (Multiplicative.ofAdd a)) = 0 at h
      simp only [← ofAdd_add] at *
      linear_combination (norm := abel) h - h1 - h2 + h3
    obtain ⟨b0, b01, b0two, b0d⟩ := splitting r U Uc Ud Ut
    let h : E r → M := fun a => k a + b0 a.toAdd
    have hdifferential : ∀ a b, h b - h (a * b) + h a = u a b := by
      intro a b
      have hh := b0d a.toAdd b.toAdd
      dsimp [h, U] at hh ⊢
      have hsum : (a * b).toAdd = a.toAdd + b.toAdd := rfl
      linear_combination (norm := abel) -hh
      rw [hsum]
      abel
    have htwo : ∀ a, h a + h a = -v a := by
      intro a
      have hh := ktwo a
      have hb := b0two a.toAdd
      dsimp [h]
      linear_combination (norm := abel) hh + hb
    obtain ⟨lam, lamd⟩ := ih fg
      (fun a b c d => by simpa [d3, fg, Prod.mul_def] using hc (a,1) (b,1) (c,1) (d,1))
      (fun a b => by simp [fg, onepair, hn1, hn2, hn3])
      (fun a => hd (a,1))
    let Bmix : E r × Q → E r × Q → M := fun s t => if t.2=1 then 0 else h s.1
    have Bmixd : ∀ a b c x y z, d2 Bmix (a,x) (b,y) (c,z) =
        (if z=1 then 0 else u a b) + (if y=1 then 0 else if z=1 then 0 else v a) := by
      intro a b c x y z
      rcases casesQ y with rfl | rfl <;> rcases casesQ z with rfl | rfl
      · simp [d2, Bmix]
      · simpa [d2, Bmix, Prod.mul_def, Tne] using hdifferential a b
      · simp [d2, Bmix, Prod.mul_def]
      · simp only [d2, Bmix, Prod.mul_def, Prod.fst, Prod.snd, TT, if_pos rfl, if_neg Tne]
        have hh := hdifferential a b
        have ht := htwo a
        linear_combination (norm := abel) hh - ht
    refine ⟨fun s t => β s t + lam s.1 t.1 + Bmix s t, ?_⟩
    intro s t w
    have hh := form s.1 t.1 w.1 s.2 t.2 w.2
    have hb := Bmixd s.1 t.1 w.1 s.2 t.2 w.2
    have hl := lamd s.1 t.1 w.1
    dsimp [P] at hh
    simp only [d2, Prod.mul_def] at *
    linear_combination (norm := abel) -hh + hb + hl
  let rankEquiv (r : ℕ) : E (r+1) ≃* E r × Q := by
    refine {
      toFun := fun p => (Multiplicative.ofAdd (fun i => p.toAdd i.succ),
        Multiplicative.ofAdd (p.toAdd 0))
      invFun := fun p => Multiplicative.ofAdd (Fin.cons p.2.toAdd p.1.toAdd)
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
    · intro p; apply Multiplicative.ofAdd.injective; ext i; cases i using Fin.cases <;> rfl
    · intro p; apply Prod.ext
      · apply Multiplicative.ofAdd.injective; ext i; rfl
      · rfl
    · intro p q; rfl
  have normalizedDescent (half : ∀ m : M, ∃ k, k+k=m) (r : ℕ)
      (f : E r → E r → E r → M) (hc : ∀ a b c d, d3 f a b c d = 0)
      (hn : ∀ a b, f 1 a b = 0 ∧ f a 1 b = 0 ∧ f a b 1 = 0)
      (hd : ∀ a, f a a a = 0) : ∃ B, ∀ a b c, d2 B a b c = f a b c := by
    induction r with
    | zero =>
      have e0 : ∀ a : E 0, a=1 := fun a => Subsingleton.elim _ _
      refine ⟨fun _ _ => 0, ?_⟩
      intro a b c
      rw [e0 a, e0 b, e0 c]
      simp [d2, (hn 1 1).1]
    | succ r ih =>
      let e := rankEquiv r
      let F := fun a b c => f (e.symm a) (e.symm b) (e.symm c)
      obtain ⟨B,hB⟩ := productDescent r half ih F
        (fun a b c d => by simpa [d3, F, e.symm.map_mul] using hc (e.symm a) (e.symm b) (e.symm c) (e.symm d))
        (fun a b => by simpa [F] using hn (e.symm a) (e.symm b))
        (fun a => hd (e.symm a))
      refine ⟨fun a b => B (e a) (e b), ?_⟩
      intro a b c
      simpa [d2, F, e.map_mul] using hB (e a) (e b) (e c)
  have unnormalizedDescent (half : ∀ m : M, ∃ k, k+k=m) (r : ℕ)
      (f : E r → E r → E r → M) (hc : ∀ a b c d, d3 f a b c d = 0)
      (hq : ∀ a, f a a a + f a 1 a = 0) : ∃ B, ∀ a b c, d2 B a b c = f a b c := by
    obtain ⟨N, hN⟩ := normalization f hc
    let F := fun a b c => f a b c - d2 N a b c
    have Fc : ∀ a b c d, d3 F a b c d = 0 := by
      intro a b c d
      have h := hc a b c d
      have hB := d2d3 N a b c d
      dsimp [F, d3] at *
      linear_combination (norm := abel) h - hB
    have Fd : ∀ a, F a a a = 0 := by
      intro a
      have aa : a*a=1 := by apply Multiplicative.ofAdd.injective; ext i; exact CharTwo.add_self_eq_zero _
      have hh := (hN a a).2.1
      have h := hq a
      dsimp [F]
      simp only [d2, aa, one_mul, mul_one] at hh ⊢
      linear_combination (norm := abel) h - hh
    obtain ⟨B,hB⟩ := normalizedDescent half r F Fc hN Fd
    refine ⟨fun a b => N a b+B a b, ?_⟩
    intro a b c
    have h := hB a b c
    dsimp [F, d2] at *
    linear_combination (norm := abel) h
  have d3Actual {G : Type} [Group G] (f : (Fin 3 → G) → M) (a b c d : G) :
      inhomogeneousCochains.d (Rep.trivial ℤ G M) 3 f ![a,b,c,d] =
        f ![b,c,d] - f ![a * b,c,d] + f ![a,b * c,d] - f ![a,b,c * d] + f ![a,b,c] := by
    change f (fun i => ![a,b,c,d] i.succ) + ∑ j : Fin 4, (-1 : ℤ)^(j.val+1) •
      f (Fin.contractNth j (· * ·) ![a,b,c,d]) = _
    have ht : (fun i : Fin 3 => ![a,b,c,d] i.succ) = ![b,c,d] := by
      ext i; fin_cases i <;> rfl
    have h0 : Fin.contractNth (0 : Fin 4) (· * ·) ![a,b,c,d] = ![a * b,c,d] := by
      ext i; fin_cases i <;> rfl
    have h1 : Fin.contractNth (1 : Fin 4) (· * ·) ![a,b,c,d] = ![a,b * c,d] := by
      ext i; fin_cases i <;> rfl
    have h2 : Fin.contractNth (2 : Fin 4) (· * ·) ![a,b,c,d] = ![a,b,c * d] := by
      ext i; fin_cases i <;> rfl
    have h3 : Fin.contractNth (3 : Fin 4) (· * ·) ![a,b,c,d] = ![a,b,c] := by
      ext i; fin_cases i <;> rfl
    rw [Fin.sum_univ_four, ht, h0, h1, h2, h3]
    norm_num
    abel
  have d2Actual {G : Type} [Group G] (B : (Fin 2 → G) → M) (a b c : G) :
      inhomogeneousCochains.d (Rep.trivial ℤ G M) 2 B ![a,b,c] =
        B ![b,c] - B ![a * b,c] + B ![a,b * c] - B ![a,b] := by
    change B (fun i => ![a,b,c] i.succ) + ∑ j : Fin 3, (-1 : ℤ)^(j.val+1) •
      B (Fin.contractNth j (· * ·) ![a,b,c]) = _
    have ht : (fun i : Fin 2 => ![a,b,c] i.succ) = ![b,c] := by
      ext i; fin_cases i <;> rfl
    have h0 : Fin.contractNth (0 : Fin 3) (· * ·) ![a,b,c] = ![a * b,c] := by
      ext i; fin_cases i <;> rfl
    have h1 : Fin.contractNth (1 : Fin 3) (· * ·) ![a,b,c] = ![a,b * c] := by
      ext i; fin_cases i <;> rfl
    have h2 : Fin.contractNth (2 : Fin 3) (· * ·) ![a,b,c] = ![a,b] := by
      ext i; fin_cases i <;> rfl
    rw [Fin.sum_univ_three, ht, h0, h1, h2]
    norm_num
    abel
  have zeroBoundary {G : Type} [Group G] (x : cocycles (Rep.trivial ℤ G M) 3)
      (hx : π (Rep.trivial ℤ G M) 3 x = 0) :
      ∃ B : (Fin 2 → G) → M,
        inhomogeneousCochains.d (Rep.trivial ℤ G M) 2 B =
          iCocycles (Rep.trivial ℤ G M) 3 x := by
    let K := groupCohomology.inhomogeneousCochains (Rep.trivial ℤ G M)
    let S := K.sc 3
    have hπ := ConcreteCategory.congr_hom S.π_moduleCatCyclesIso_hom x
    change S.moduleCatHomologyIso.hom (π (Rep.trivial ℤ G M) 3 x) =
      S.moduleCatLeftHomologyData.π (S.moduleCatCyclesIso.hom x) at hπ
    have hz : S.moduleCatLeftHomologyData.π (S.moduleCatCyclesIso.hom x) = 0 := by
      apply hπ.symm.trans
      rw [hx]
      change S.moduleCatHomologyIso.hom.hom (0 : S.homology) = 0
      exact map_zero _
    change (LinearMap.range S.moduleCatToCycles).mkQ (S.moduleCatCyclesIso.hom x) = 0 at hz
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨B,hB⟩ := hm
    have hi := ConcreteCategory.congr_hom S.moduleCatCyclesIso_hom_i x
    change S.moduleCatLeftHomologyData.i (S.moduleCatCyclesIso.hom x) = S.iCycles x at hi
    have hraw : S.f B = S.iCycles x := by
      rw [← hi, ← hB]
      rfl
    let B' := (K.xPrevIso (i := 2) (j := 3) rfl).hom B
    refine ⟨B', ?_⟩
    have hprev : (ComplexShape.up ℕ).prev 3 = 2 := (ComplexShape.up ℕ).prev_eq' (show (2 : ℕ)+1=3 from rfl)
    have ht : (K.xPrevIso (i := 2) (j := 3) rfl).hom ≫ K.d 2 3 = S.f := by
      exact K.eqToHom_comp_d (by rw [hprev]; rfl) rfl
    have hh := ConcreteCategory.congr_hom ht B
    exact hh.trans hraw
  revert hr
  refine groupCohomology_induction_on c ?_
  intro x hr
  let A := Rep.trivial ℤ (E r) M
  let raw := iCocycles A 3 x
  let f := fun a b c => raw ![a,b,c]
  have df : inhomogeneousCochains.d A 3 raw = 0 := by
    have h := ConcreteCategory.congr_hom ((groupCohomology.inhomogeneousCochains A).iCycles_d 3 4) x
    exact h
  have hc : ∀ a b c d, d3 f a b c d = 0 := by
    intro a b c d
    have h := congrFun df ![a,b,c,d]
    rw [d3Actual] at h
    exact h
  have hq : ∀ g, f g g g + f g 1 g = 0 := by
    intro g
    by_cases hg : g=1
    · subst g
      have h := hc 1 1 1 1
      have hh : f 1 1 1 = 0 := by simpa [d3] using h
      simp [hh]
    · let S := Subgroup.zpowers g
      let j := S.subtype
      let C := Rep.trivial ℤ S M
      let y := cocyclesMap j (𝟙 C) 3 x
      have hp := ConcreteCategory.congr_hom (groupCohomology.π_map j (𝟙 C) 3) x
      change groupCohomology.map j (𝟙 C) 3 (π A 3 x) = π C 3 y at hp
      have hy : π C 3 y = 0 := hp.symm.trans (hr g hg)
      obtain ⟨B,hB⟩ := zeroBoundary y hy
      let t : S := ⟨g, Subgroup.mem_zpowers g⟩
      have tt : t*t=1 := by
        apply Subtype.ext
        change g*g=1
        apply Multiplicative.ofAdd.injective
        ext i; exact CharTwo.add_self_eq_zero _
      have hm := ConcreteCategory.congr_hom
        (HomologicalComplex.cyclesMap_i (cochainsMap j (𝟙 C)) 3) x
      change iCocycles C 3 y = (cochainsMap j (𝟙 C)).f 3 raw at hm
      have h1 := congrFun hB ![t,t,t]
      have h2 := congrFun hB ![t,1,t]
      rw [d2Actual, hm] at h1 h2
      simp only [tt, one_mul, mul_one] at h1 h2
      have mapraw : ∀ p : Fin 3 → S,
          (cochainsMap j (𝟙 C)).f 3 raw p = raw (j ∘ p) := fun p => rfl
      rw [mapraw] at h1 h2
      have eq1 : j ∘ ![t,t,t] = ![g,g,g] := by ext i; fin_cases i <;> rfl
      have eq2 : j ∘ ![t,1,t] = ![g,1,g] := by ext i; fin_cases i <;> rfl
      rw [eq1] at h1
      rw [eq2] at h2
      change B ![t,t] - B ![1,t] + B ![t,1] - B ![t,t] = f g g g at h1
      change B ![1,t] - B ![t,t] + B ![t,t] - B ![t,1] = f g 1 g at h2
      linear_combination (norm := abel) -h1 - h2
  obtain ⟨L,hL⟩ := unnormalizedDescent half r f hc hq
  let B : (Fin 2 → E r) → M := fun p => L (p 0) (p 1)
  have hB : inhomogeneousCochains.d A 2 B = raw := by
    ext p
    have hp : p = ![p 0,p 1,p 2] := by ext i; fin_cases i <;> rfl
    rw [hp, d2Actual]
    exact hL (p 0) (p 1) (p 2)
  have hb : toCocycles A 2 3 B = x := by
    apply (ModuleCat.mono_iff_injective (iCocycles A 3)).mp inferInstance
    have hi := ConcreteCategory.congr_hom
      ((groupCohomology.inhomogeneousCochains A).toCycles_i 2 3) B
    change iCocycles A 3 (toCocycles A 2 3 B) = inhomogeneousCochains.d A 2 B at hi
    exact hi.trans hB
  rw [← hb]
  exact ConcreteCategory.congr_hom
    ((groupCohomology.inhomogeneousCochains A).toCycles_comp_homologyπ 2 3) B
end D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection
