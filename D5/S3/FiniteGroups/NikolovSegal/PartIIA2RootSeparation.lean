/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA2RootGeometry
/-! Actual A2 root normalization toward Nikolov--Segal Part II, section 2
(Inn D Phi Gamma) and Proposition 6.2. Torus kernels and simple-root images
are derived by matrix commutation/cardinality, not supplied as a classification axiom. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace NikolovSegal.PartIIA2RootSeparation
open PartIIA2Orbital PartIIA2TorusAlignment PartIIA2RootNormalization
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

private theorem diagonal_commutes_chart (g : SL(3,F)) (d : Fin 3 → F)
    (hd : g.val=Matrix.diagonal d) (a b c : F) :
    g*upper3 a b c=upper3 a b c*g ↔
      (d 0-d 1)*a=0 ∧ (d 1-d 2)*b=0 ∧ (d 0-d 2)*c=0 := by
  constructor
  · intro h
    have h01 := congrArg (fun z : SL(3,F) => z 0 1) h
    have h12 := congrArg (fun z : SL(3,F) => z 1 2) h
    have h02 := congrArg (fun z : SL(3,F) => z 0 2) h
    simp only [coe_mul,hd,Matrix.diagonal_mul,Matrix.mul_diagonal] at h01 h12 h02
    refine ⟨?_,?_,?_⟩
    · change d 0*a=a*d 1 at h01
      linear_combination h01
    · change d 1*b=b*d 2 at h12
      linear_combination h12
    · change d 0*c=c*d 2 at h02
      linear_combination h02
  · rintro ⟨h01,h12,h02⟩
    apply Subtype.ext
    change g.val*(upper3 a b c).val=(upper3 a b c).val*g.val
    rw [hd]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [upper3,Matrix.diagonal_mul,Matrix.mul_diagonal]
    · linear_combination h01
    · linear_combination h02
    · linear_combination h12

private theorem exists_unit_cube_ne_one [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) : ∃ x : Fˣ, (x:F)^3 ≠ 1 := by
  obtain ⟨x,hx⟩ := exists_pow_ne_one_of_isCyclic (G := Fˣ) (k := 3)
    (by decide) (by rw [Nat.card_eq_fintype_card,Fintype.card_units]; omega)
  exact ⟨x,fun h => hx (Units.ext h)⟩

private theorem unit_difference_ne (x : Fˣ) (hx : (x:F)^3 ≠ 1) :
    (x:F)-(↑(x*x)⁻¹:F) ≠ 0 := by
  intro h
  have he : (x:F)=(↑(x*x)⁻¹:F) := sub_eq_zero.mp h
  have hh := congrArg (fun z : F => z*(↑(x*x):F)) he
  apply hx
  calc
    (x:F)^3 = (x:F)*(↑(x*x):F) := by simp [Units.val_mul,pow_succ,mul_assoc]
    _ = 1 := by simpa [← Units.val_mul] using hh

/-- Actual first torus-kernel fixed subgroup inside the nonabelian U.
For fields of size>4, a genuine cube-separating unit is constructed. -/
theorem fixed_first_torus_kernel_iff [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) (g : SL(3,F)) (hg : g ∈ upperUnipotent) :
    (∀ x : Fˣ, diagonalPair (x,x)*g=g*diagonalPair (x,x)) ↔
      g ∈ positiveRoot (F := F) 0 := by
  obtain ⟨a,b,c,rfl⟩ := hg
  constructor
  · intro h
    obtain ⟨x,hx⟩ := exists_unit_cube_ne_one hF
    have hc := (diagonal_commutes_chart (diagonalPair (x,x)) _ rfl a b c).mp (h x)
    have hb : b=0 := (mul_eq_zero.mp hc.2.1).resolve_left (unit_difference_ne x hx)
    have hc0 : c=0 := (mul_eq_zero.mp hc.2.2).resolve_left (unit_difference_ne x hx)
    refine ⟨a,?_⟩
    rw [hb,hc0]
    change transvection (show (0:Fin 3) ≠ 1 by decide) a=upper3 a 0 0
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper3,transvection_coe]
  · rintro ⟨t,ht⟩ x
    have he := congrArg (fun z : SL(3,F) => z 0 1) ht
    have hb := congrArg (fun z : SL(3,F) => z 1 2) ht
    have hc := congrArg (fun z : SL(3,F) => z 0 2) ht
    change (transvection (show (0:Fin 3) ≠ 1 by decide) t) 0 1=(upper3 a b c) 0 1 at he
    change (transvection (show (0:Fin 3) ≠ 1 by decide) t) 1 2=(upper3 a b c) 1 2 at hb
    change (transvection (show (0:Fin 3) ≠ 1 by decide) t) 0 2=(upper3 a b c) 0 2 at hc
    simp [upper3,transvection_coe] at he hb hc
    rw [← hb,← hc]
    apply (diagonal_commutes_chart (diagonalPair (x,x)) _ rfl a 0 0).mpr
    simp
private theorem second_kernel_diagonal (x : Fˣ) :
    (diagonalPair ((x*x)⁻¹,x)).val =
      Matrix.diagonal (![↑(x*x)⁻¹,↑x,↑x] : Fin 3 → F) := by
  have hx : (((x*x)⁻¹*x)⁻¹ : Fˣ)=x := by group
  change Matrix.diagonal (![↑(x*x)⁻¹,↑x,↑((x*x)⁻¹*x)⁻¹] : Fin 3 → F)=_
  rw [hx]

/-- The actual second torus-kernel fixed subgroup is the other simple root.
The same constructed cube-separating unit controls both noncentral unwanted
coordinates, preserving their independent matrix occurrences. -/
theorem fixed_second_torus_kernel_iff [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) (g : SL(3,F)) (hg : g ∈ upperUnipotent) :
    (∀ x : Fˣ, diagonalPair ((x*x)⁻¹,x)*g=g*diagonalPair ((x*x)⁻¹,x)) ↔
      g ∈ positiveRoot (F := F) 1 := by
  obtain ⟨a,b,c,rfl⟩ := hg
  constructor
  · intro h
    obtain ⟨x,hx⟩ := exists_unit_cube_ne_one hF
    have hc := (diagonal_commutes_chart (diagonalPair ((x*x)⁻¹,x)) _
      (second_kernel_diagonal x) a b c).mp (h x)
    have hdiff : (↑(x*x)⁻¹:F)-(x:F) ≠ 0 := by
      intro hh
      exact unit_difference_ne x hx (sub_eq_zero.mpr (sub_eq_zero.mp hh).symm)
    have ha : a=0 := (mul_eq_zero.mp hc.1).resolve_left hdiff
    have hc0 : c=0 := (mul_eq_zero.mp hc.2.2).resolve_left hdiff
    refine ⟨b,?_⟩
    rw [ha,hc0]
    change transvection (show (1:Fin 3) ≠ 2 by decide) b=upper3 0 b 0
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper3,transvection_coe]
  · rintro ⟨t,ht⟩ x
    have ha := congrArg (fun z : SL(3,F) => z 0 1) ht
    have hc := congrArg (fun z : SL(3,F) => z 0 2) ht
    change (transvection (show (1:Fin 3) ≠ 2 by decide) t) 0 1=(upper3 a b c) 0 1 at ha
    change (transvection (show (1:Fin 3) ≠ 2 by decide) t) 0 2=(upper3 a b c) 0 2 at hc
    simp [upper3,transvection_coe] at ha hc
    rw [← ha,← hc]
    apply (diagonal_commutes_chart (diagonalPair ((x*x)⁻¹,x)) _
      (second_kernel_diagonal x) 0 b 0).mpr
    simp
private def firstKernelHom : Fˣ →* SL(3,F) where
  toFun x := diagonalPair (x,x)
  map_one' := diagonalPair.map_one
  map_mul' x y := diagonalPair.map_mul (x,x) (y,y)

private def secondKernelHom : Fˣ →* SL(3,F) where
  toFun x := diagonalPair ((x*x)⁻¹,x)
  map_one' := by
    change diagonalPair ((1*1)⁻¹,1)=1
    rw [one_mul,inv_one]
    exact (diagonalPair (F := F)).map_one
  map_mul' x y := by
    rw [← diagonalPair.map_mul]
    apply congrArg diagonalPair
    apply Prod.ext
    · dsimp only [Prod.fst_mul]
      simp only [mul_inv_rev]
      ac_rfl
    · rfl

private def firstKernel : Subgroup SL(3,F) := (firstKernelHom (F := F)).range
private def secondKernel : Subgroup SL(3,F) := (secondKernelHom (F := F)).range

private theorem firstKernelHom_injective : Function.Injective (firstKernelHom (F := F)) := by
  intro x y h
  have hh := congrArg (fun g : SL(3,F) => g 0 0) h
  exact Units.ext hh
private theorem secondKernelHom_injective : Function.Injective (secondKernelHom (F := F)) := by
  intro x y h
  have hh := congrArg (fun g : SL(3,F) => g 1 1) h
  exact Units.ext hh

private theorem card_firstKernel : Nat.card (firstKernel (F := F))=Nat.card Fˣ := by
  exact (Nat.card_congr (MonoidHom.ofInjective firstKernelHom_injective).toEquiv).symm
private theorem card_secondKernel : Nat.card (secondKernel (F := F))=Nat.card Fˣ := by
  exact (Nat.card_congr (MonoidHom.ofInjective secondKernelHom_injective).toEquiv).symm

private theorem torus_equal_first_mem (g : SL(3,F)) (hg : g ∈ diagonalTorus)
    (hd : g 0 0=g 1 1) : g ∈ firstKernel := by
  obtain ⟨⟨x,y⟩,rfl⟩ := hg
  have hxy : x=y := Units.ext hd
  subst y
  exact ⟨x,rfl⟩

private theorem torus_equal_second_mem (g : SL(3,F)) (hg : g ∈ diagonalTorus)
    (hd : g 1 1=g 2 2) : g ∈ secondKernel := by
  obtain ⟨⟨x,y⟩,rfl⟩ := hg
  have hxy : y=(x*y)⁻¹ := Units.ext hd
  have hx : x=(y*y)⁻¹ := by
    have he : x*y=y⁻¹ := by simpa only [inv_inv] using (congrArg Inv.inv hxy).symm
    calc
      x = (x*y)*y⁻¹ := by group
      _ = y⁻¹*y⁻¹ := by rw [he]
      _ = (y*y)⁻¹ := by group
  subst x
  exact ⟨y,rfl⟩

/-- The actual cardinal/matrix inference in root alignment. A torus subgroup
of the true kernel order centralizing one noncentral U element MUST be one of
the two literal simple-root kernels. No kernel/image choice is assumed. -/
theorem actual_torus_kernel_classification [Fintype F] [DecidableEq F]
    (L : Subgroup SL(3,F)) (hLT : L ≤ diagonalTorus)
    (hcard : Nat.card L=Nat.card Fˣ) (a b c : F) (hab : a ≠ 0 ∨ b ≠ 0)
    (hcomm : ∀ k : L, (k:SL(3,F))*upper3 a b c=upper3 a b c*(k:SL(3,F))) :
    L=firstKernel ∨ L=secondKernel := by
  rcases hab with ha|hb
  · left
    have hle : L ≤ firstKernel := by
      intro g hg
      apply torus_equal_first_mem g (hLT hg)
      obtain ⟨x,hx⟩ := hLT hg
      have hh := (diagonal_commutes_chart g _ (by rw [← hx]; rfl) a b c).mp (hcomm ⟨g,hg⟩)
      have he : (x.1:F)-(x.2:F)=0 := (mul_eq_zero.mp hh.1).resolve_right ha
      rw [← hx]
      exact sub_eq_zero.mp he
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_firstKernel,hcard]
  · right
    have hle : L ≤ secondKernel := by
      intro g hg
      apply torus_equal_second_mem g (hLT hg)
      obtain ⟨x,hx⟩ := hLT hg
      have hh := (diagonal_commutes_chart g _ (by rw [← hx]; rfl) a b c).mp (hcomm ⟨g,hg⟩)
      have he : (x.2:F)-(↑(x.1*x.2)⁻¹:F)=0 := (mul_eq_zero.mp hh.2.1).resolve_right hb
      rw [← hx]
      exact sub_eq_zero.mp he
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_secondKernel,hcard]

private abbrev rt (r : Fin 3) (t : F) : SL(3,F) := (a2Kernel% root) r t
private def kernel (r : Fin 2) : Subgroup SL(3,F) := ![firstKernel,secondKernel] r

private theorem kernel_le_torus (r : Fin 2) : kernel (F := F) r ≤ diagonalTorus := by
  fin_cases r
  all_goals rintro g ⟨x,rfl⟩; exact ⟨_,rfl⟩

private theorem card_kernel (r : Fin 2) : Nat.card (kernel (F := F) r)=Nat.card Fˣ := by
  fin_cases r
  · exact card_firstKernel
  · exact card_secondKernel

private theorem fixed_kernel_iff [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) (r : Fin 2) (g : SL(3,F)) (hg : g ∈ upperUnipotent) :
    (∀ k ∈ kernel (F := F) r, k*g=g*k) ↔ g ∈ positiveRoot (F := F) r.castSucc := by
  fin_cases r
  · change (∀ k ∈ firstKernel, k*g=g*k) ↔ g ∈ positiveRoot (F := F) 0
    rw [← fixed_first_torus_kernel_iff hF g hg]
    constructor
    · intro h x; exact h _ ⟨x,rfl⟩
    · rintro h k ⟨x,rfl⟩; exact h x
  · change (∀ k ∈ secondKernel, k*g=g*k) ↔ g ∈ positiveRoot (F := F) 1
    rw [← fixed_second_torus_kernel_iff hF g hg]
    constructor
    · intro h x; exact h _ ⟨x,rfl⟩
    · rintro h k ⟨x,rfl⟩; exact h x

private theorem rt_injective (r : Fin 3) : Function.Injective (rt (F := F) r) := by
  intro t s h
  have hh := congrArg (fun g : SL(3,F) => g ((a2Kernel% rootI) r) ((a2Kernel% rootJ) r)) h
  change (transvection ((a2Kernel% root_ne) r) t) ((a2Kernel% rootI) r) ((a2Kernel% rootJ) r)=
    (transvection ((a2Kernel% root_ne) r) s) ((a2Kernel% rootI) r) ((a2Kernel% rootJ) r) at hh
  simpa only [transvection_coe,Matrix.add_apply,Matrix.single_apply,
    ite_true,eq_self,and_self,add_left_cancel_iff] using hh

private theorem card_root (r : Fin 3) : Nat.card (positiveRoot (F := F) r)=Nat.card F := by
  let f : F → positiveRoot (F := F) r := fun t => ⟨rt r t,t,rfl⟩
  have hinj : Function.Injective f := by
    intro t s h
    exact rt_injective r (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    rintro ⟨g,t,rfl⟩; exact ⟨t,rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)).symm

private theorem noncentral_simple_root (r : Fin 2) :
    rt (F := F) r.castSucc 1 ∉ positiveRoot (F := F) 2 := by
  rintro ⟨t,ht⟩
  fin_cases r
  · have hh := congrArg (fun g : SL(3,F) => g 0 1) ht
    change (transvection (show (0:Fin 3) ≠ 2 by decide) t) 0 1=
      (transvection (show (0:Fin 3) ≠ 1 by decide) 1) 0 1 at hh
    simp [transvection_coe] at hh
  · have hh := congrArg (fun g : SL(3,F) => g 1 2) ht
    change (transvection (show (0:Fin 3) ≠ 2 by decide) t) 1 2=
      (transvection (show (1:Fin 3) ≠ 2 by decide) 1) 1 2 at hh
    simp [transvection_coe] at hh

private theorem simple_root_image [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) (alpha : MulAut SL(3,F))
    (hU : upperUnipotent.map alpha.toMonoidHom=upperUnipotent)
    (hT : diagonalTorus.map alpha.toMonoidHom=diagonalTorus)
    (hZ : (positiveRoot (F := F) 2).map alpha.toMonoidHom=positiveRoot 2)
    (r : Fin 2) :
    (positiveRoot r.castSucc).map alpha.toMonoidHom=positiveRoot (F := F) 0 ∨
    (positiveRoot r.castSucc).map alpha.toMonoidHom=positiveRoot (F := F) 1 := by
  let L := (kernel (F := F) r).map alpha.toMonoidHom
  have hLT : L ≤ diagonalTorus := by
    rintro g ⟨k,hk,rfl⟩
    rw [← hT]
    exact Subgroup.mem_map_of_mem alpha.toMonoidHom (kernel_le_torus r hk)
  have hcL : Nat.card L=Nat.card Fˣ := by
    rw [← Nat.card_congr ((kernel r).equivMapOfInjective alpha.toMonoidHom alpha.injective).toEquiv]
    exact card_kernel r
  have hu : alpha (rt r.castSucc 1) ∈ upperUnipotent := by
    rw [← hU]
    exact Subgroup.mem_map_of_mem alpha.toMonoidHom ((a2Kernel% root_mem) _ _)
  obtain ⟨a,b,c,hchart⟩ := hu
  have hnz : alpha (rt r.castSucc 1) ∉ positiveRoot (F := F) 2 := by
    intro hz
    rw [← hZ] at hz
    exact noncentral_simple_root r ((Subgroup.mem_map_iff_mem alpha.injective).mp hz)
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    have ha : a=0 := by tauto
    have hb : b=0 := by tauto
    apply hnz
    refine ⟨c,?_⟩
    rw [← hchart,ha,hb]
    change transvection (show (0:Fin 3) ≠ 2 by decide) c=upper3 0 0 c
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper3,transvection_coe]
  have hcomm : ∀ t k, k ∈ L → k*alpha (rt r.castSucc t)=alpha (rt r.castSucc t)*k := by
    rintro t k ⟨l,hl,rfl⟩
    change alpha l*alpha (rt r.castSucc t)=alpha (rt r.castSucc t)*alpha l
    have hh := congrArg alpha ((fixed_kernel_iff hF r _ ((a2Kernel% root_mem) _ _)).mpr
      ⟨t,rfl⟩ l hl)
    simpa only [map_mul] using hh
  have hc : ∀ k : L, (k:SL(3,F))*upper3 a b c=upper3 a b c*(k:SL(3,F)) := by
    intro k
    rw [hchart]
    exact hcomm 1 k k.prop
  obtain hL|hL := actual_torus_kernel_classification L hLT hcL a b c hab hc
  all_goals
    have hidx : ∃ s : Fin 2, L=kernel (F := F) s := by
      first | exact ⟨0,hL⟩ | exact ⟨1,hL⟩
    obtain ⟨s,hs⟩ := hidx
    have hle : (positiveRoot r.castSucc).map alpha.toMonoidHom ≤ positiveRoot (F := F) s.castSucc := by
      rintro g ⟨z,⟨t,rfl⟩,rfl⟩
      apply (fixed_kernel_iff hF s _ ?_).mp
      · intro k hk
        exact hcomm t k (hs.symm ▸ hk)
      · rw [← hU]
        exact Subgroup.mem_map_of_mem alpha.toMonoidHom ((a2Kernel% root_mem) _ _)
    have heq : (positiveRoot r.castSucc).map alpha.toMonoidHom=positiveRoot (F := F) s.castSucc := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [card_root,← Nat.card_congr ((positiveRoot r.castSucc).equivMapOfInjective
        alpha.toMonoidHom alpha.injective).toEquiv,card_root]
    fin_cases s
    · exact Or.inl heq
    · exact Or.inr heq

private theorem same_root_commute (r : Fin 3) (g h : SL(3,F))
    (hg : g ∈ positiveRoot (F := F) r) (hh : h ∈ positiveRoot (F := F) r) : g*h=h*g := by
  obtain ⟨t,rfl⟩ := hg
  obtain ⟨s,rfl⟩ := hh
  change transvection ((a2Kernel% root_ne) r) t*transvection ((a2Kernel% root_ne) r) s=
    transvection ((a2Kernel% root_ne) r) s*transvection ((a2Kernel% root_ne) r) t
  rw [← transvection_add,← transvection_add,add_comm t s]

private theorem simple_roots_not_commute : rt (F := F) 0 1*rt 1 1 ≠ rt 1 1*rt 0 1 := by
  intro h
  have hh := congrArg (fun g : SL(3,F) => g 0 2) h
  change ((transvection (show (0:Fin 3) ≠ 1 by decide) (1:F)).val*
    (transvection (show (1:Fin 3) ≠ 2 by decide) 1).val : Matrix (Fin 3) (Fin 3) F) 0 2=
    ((transvection (show (1:Fin 3) ≠ 2 by decide) (1:F)).val*
    (transvection (show (0:Fin 3) ≠ 1 by decide) 1).val : Matrix (Fin 3) (Fin 3) F) 0 2 at hh
  simp [Matrix.mul_apply,Fin.sum_univ_succ,transvection_coe] at hh

/-- Genuine simple-root alignment or graph interchange for actual normalized
bare SL3 automorphisms. Both images are derived from actual torus kernel
orders and diagonal commutation. They cannot coincide, by the nontrivial
A2 root incidence. No subgroup-image choice is assumed. -/
theorem actual_normalized_simple_root_permutation [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) (alpha : MulAut SL(3,F))
    (hU : upperUnipotent.map alpha.toMonoidHom=upperUnipotent)
    (hT : diagonalTorus.map alpha.toMonoidHom=diagonalTorus)
    (hZ : (positiveRoot (F := F) 2).map alpha.toMonoidHom=positiveRoot 2) :
    ((positiveRoot 0).map alpha.toMonoidHom=positiveRoot (F := F) 0 ∧
      (positiveRoot 1).map alpha.toMonoidHom=positiveRoot (F := F) 1) ∨
    ((positiveRoot 0).map alpha.toMonoidHom=positiveRoot (F := F) 1 ∧
      (positiveRoot 1).map alpha.toMonoidHom=positiveRoot (F := F) 0) := by
  have h0 := simple_root_image hF alpha hU hT hZ 0
  have h1 := simple_root_image hF alpha hU hT hZ 1
  have hne : ∀ s : Fin 3, ¬ ((positiveRoot 0).map alpha.toMonoidHom=positiveRoot (F := F) s ∧
      (positiveRoot 1).map alpha.toMonoidHom=positiveRoot (F := F) s) := by
    rintro s ⟨hs0,hs1⟩
    have hm0 : alpha (rt 0 1) ∈ positiveRoot (F := F) s := by
      rw [← hs0]; exact Subgroup.mem_map_of_mem alpha.toMonoidHom ⟨1,rfl⟩
    have hm1 : alpha (rt 1 1) ∈ positiveRoot (F := F) s := by
      rw [← hs1]; exact Subgroup.mem_map_of_mem alpha.toMonoidHom ⟨1,rfl⟩
    apply simple_roots_not_commute (F := F)
    apply alpha.injective
    simpa only [map_mul] using same_root_commute s _ _ hm0 hm1
  rcases h0 with h0|h0 <;> rcases h1 with h1|h1
  · exact (hne 0 ⟨h0,h1⟩).elim
  · exact Or.inl ⟨h0,h1⟩
  · exact Or.inr ⟨h0,h1⟩
  · exact (hne 1 ⟨h0,h1⟩).elim

/-- Every bare SL3 automorphism admits ONE inner normalization preserving U,
T,Z and either preserving or interchanging the two literal simple roots.
The field-size bound is the actual cube-separation bound, not an oracle. -/
theorem actual_bare_SL3_root_normalization [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) (beta : MulAut SL(3,F)) :
    ∃ g : SL(3,F), let alpha := MulAut.conj g⁻¹*beta
      upperUnipotent.map alpha.toMonoidHom=upperUnipotent ∧
      (positiveRoot (F := F) 2).map alpha.toMonoidHom=positiveRoot 2 ∧
      (((positiveRoot 0).map alpha.toMonoidHom=positiveRoot (F := F) 0 ∧
        (positiveRoot 1).map alpha.toMonoidHom=positiveRoot (F := F) 1) ∨
       ((positiveRoot 0).map alpha.toMonoidHom=positiveRoot (F := F) 1 ∧
        (positiveRoot 1).map alpha.toMonoidHom=positiveRoot (F := F) 0)) := by
  obtain ⟨g,hU,hT,hZ⟩ := PartIIA2RootGeometry.actual_bare_SL3_U_T_central_root_normalization beta
  exact ⟨g,hU,hZ,actual_normalized_simple_root_permutation hF _ hU hT hZ⟩
end NikolovSegal.PartIIA2RootSeparation
