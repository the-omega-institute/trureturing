/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Reconstruction
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Readings]
   utility: none
   digest: Integral exceptional19 ZeroLattice Reconstruction on original physical labels. -/
/- UNCOMPILED source candidate. No torsion cancellation or group division. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Readings
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree base Qmask)
open MersenneExceptional19Stabilizer (floor_unique)
open MersenneExceptional19PermutationStabilizer
  (read block Annihilates aa bb ss eighth eighth_facts parameter_exact
    parameter_margins parameter_parities affineRange affine_digits affine_annihilates
    qLow qMid q8Low q8Mid q_readings q_zero physical_read)

variable {A : Type*} [AddCommGroup A]

/-- A unimodular presentation calculation, including its 2-primary part.
All divisions are integer coefficient divisions. This helper is consumed below. -/
private theorem solve_presentation (a s Q k t : ℤ) (u x y θ q : A)
    (hs : 2*k=s) (ha : a%2=1) (ht : 2*t=Q-a)
    (hx : x=a • q) (hy : y=(-k) • q)
    (hQ : u+t • q-θ=0) (h8 : (-Q) • q+(2 : ℤ) • θ=0) :
    ∃ c : A, u=a • c ∧ x=(2*a) • c ∧ y=(-s) • c ∧ θ=Q • c := by
  have h2u : (2 : ℤ) • u=a • q := by
    have he : a=Q-2*t := by omega
    rw [he]
    linear_combination (norm := module) (2 : ℤ) • hQ+h8
  let μ : ℤ := (a-1)/2
  have hμ : a=2*μ+1 := by dsimp [μ]; omega
  let c : A := u-μ • q
  have hqc : q=(2 : ℤ) • c := by
    symm
    calc
      (2 : ℤ) • c=(2 : ℤ) • u-(2*μ) • q := by dsimp [c]; module
      _=a • q-(2*μ) • q := by rw [h2u]
      _=q := by rw [← sub_smul,show a-2*μ=1 by omega]; simp
  have huc : u=a • c := by
    calc
      u=c+μ • q := by dsimp [c]; abel
      _=a • c := by rw [hqc,hμ]; module
  have hθc : θ=Q • c := by
    calc
      θ=u+t • q := by linear_combination (norm := abel) -hQ
      _=(a+2*t) • c := by rw [huc,hqc]; module
      _=Q • c := by rw [show a+2*t=Q by omega]
  refine ⟨c,huc,?_,?_,hθc⟩
  · rw [hx,hqc]
    module
  · rw [hy,hqc,← hs]
    module

/-- Every abelian-group annihilator of the original literal zero masks has
one generator with the primitive physical weights. All four terminal masks
are proved zero by the shared physical arithmetic, with no public premise. -/
theorem reconstructed_normal_form (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : Annihilates r X) :
    ∃ c : A,
      (∀ j, j<degree r → block X 0 j=
        first (degree r) (aa r • c) ((2*aa r) • c) 0 ((Qmask r : ℤ) • c) j) ∧
      (∀ j, j<degree r → block X 1 j=
        middle (degree r) ((-ss r) • c) ((Qmask r : ℤ) • c) j) ∧
      (∀ j, j<degree r → block X 2 j=
        last (degree r) (aa r • c) ((2*aa r) • c) ((-ss r) • c)
          0 ((Qmask r : ℤ) • c) j) := by
  obtain ⟨u,x,y,ρ,θ,hf,hg,hh⟩ := integral_normal_form r X hX
  obtain ⟨hB,he,hemod⟩ := eighth_facts r
  obtain ⟨ha0,ha1,hb0,hb1,hs0,hs1⟩ := parameter_margins r
  obtain ⟨hap,hbp,hsp⟩ := parameter_parities r
  obtain ⟨hae,hbe,hse⟩ := parameter_exact r
  have hs : ss r=aa r+bb r := rfl
  have hBp : (0 : ℤ)<base r := by omega
  have hU : (0 : ℤ)≤0 ∧ (0 : ℤ)<base r := ⟨le_rfl,hBp⟩
  let k : ℤ := ss r/2
  have hsk : 2*k=ss r := by dsimp [k]; omega
  have hunit : 4*k-5*aa r=1 := by omega
  have hread := integral_read r X u x y ρ θ hf hg hh
  obtain ⟨hLa,hMa,hUa,hCa⟩ := affine_digits r (aa r) (Or.inl rfl)
  have ar := affine_annihilates r X hX (aa r) (Or.inl rfl)
  have nr := hread (aa r+bb r) (aa r) (aa r-aa r) hLa hMa hUa
  have fs : 2*ss r/(base r : ℤ)=0 := by
    apply floor_unique hBp <;> omega
  have ps : ss r%2=0 := by omega
  rw [ar,hCa] at nr
  simp only [← hs] at nr
  have slope : k • x+aa r • y=0 := by
    simpa only [sub_self,Int.zero_emod,Int.zero_ediv,Int.mul_zero,sub_zero,
      ps,fs,zero_smul,zero_add,add_zero,k] using nr.symm
  have range3 : affineRange r (3*eighth r) :=
    Or.inr (Or.inl ⟨le_rfl,by omega⟩)
  obtain ⟨hL3,hM3,hU3,hC3⟩ := affine_digits r (3*eighth r) range3
  have a3 := affine_annihilates r X hX (3*eighth r) range3
  have n3 := hread (3*eighth r+bb r) (3*eighth r)
    (3*eighth r-aa r) hL3 hM3 hU3
  have e3 : (3*eighth r+bb r)%2-(3*eighth r-aa r)%2=0 := by omega
  have half3 : (3*eighth r+bb r)/2-(3*eighth r-aa r)/2=k := by
    dsimp [k]
    omega
  have k3L : 2*(3*eighth r+bb r)/(base r : ℤ)=1 := by
    apply floor_unique hBp <;> omega
  have k3U : 2*(3*eighth r-aa r)/(base r : ℤ)=0 := by
    apply floor_unique hBp <;> omega
  rw [a3,hC3,e3,half3,k3L,k3U,
    show 3*eighth r-(3*eighth r-aa r)=aa r by ring] at n3
  simp only [zero_smul,zero_add,add_zero,sub_zero,one_smul] at n3
  have hρ : ρ=0 := by linear_combination (norm := abel) n3.symm-slope
  obtain ⟨hL,hM,hL8,hM8,hp,hp8,hC,hC8,hG,hG8⟩ := q_readings r
  obtain ⟨hz,hz8⟩ := q_zero r
  have zread := hX _ hz
  have z8read := hX _ hz8
  rw [physical_read (d := degree r) (by dsimp [degree]; omega)] at zread z8read
  have nz := hread (qLow r) (qMid r) 0 hL hM hU
  have nz8 := hread (q8Low r) (q8Mid r) 0 hL8 hM8 hU
  rw [zread,hρ,hC,hp] at nz
  rw [z8read,hρ,hC8,hp8] at nz8
  simp only [Int.zero_emod,Int.zero_ediv,Int.mul_zero,sub_zero,
    zero_smul,one_smul,zero_add,add_zero,neg_one_zsmul] at nz nz8
  let q : A := -(5 : ℤ) • x-(4 : ℤ) • y
  have hx : x=aa r • q := by
    calc
      x=(4*k-5*aa r) • x := by rw [hunit]; simp
      _=(-5*aa r) • x+(-4*aa r) • y := by
        linear_combination (norm := module) (4 : ℤ) • slope
      _=aa r • q := by dsimp [q]; module
  have hy : y=(-k) • q := by
    calc
      y=(4*k-5*aa r) • y := by rw [hunit]; simp
      _=(4*k) • y+(5*k) • x := by
        linear_combination (norm := module) (-5 : ℤ) • slope
      _=(-k) • q := by dsimp [q]; module
  let t : ℤ := (qLow r/2)*aa r-qMid r*k
  have ht : 2*t=(Qmask r : ℤ)-aa r := by
    have hl : qLow r=2*(qLow r/2)+1 := by omega
    rw [← hsk,hl] at hG
    dsimp [t]
    nlinarith only [hG]
  have ht8 : (q8Low r/2)*aa r-q8Mid r*k= -(Qmask r : ℤ) := by
    have hl : q8Low r=2*(q8Low r/2) := by omega
    rw [← hsk,hl] at hG8
    nlinarith only [hG8]
  have eqQ : u+t • q-θ=0 := by
    rw [hx,hy] at nz
    dsimp [t]
    linear_combination (norm := module) nz.symm
  have eq8 : (-(Qmask r : ℤ)) • q+(2 : ℤ) • θ=0 := by
    rw [hx,hy] at nz8
    rw [← ht8]
    linear_combination (norm := module) nz8.symm
  obtain ⟨c,hu,hx',hy',hθ⟩ :=
    solve_presentation (aa r) (ss r) (Qmask r) k t u x y θ q
      hsk hap ht hx hy eqQ eq8
  refine ⟨c,?_,?_,?_⟩
  · simpa only [hu,hx',hρ,hθ] using hf
  · simpa only [hy',hθ] using hg
  · simpa only [hu,hx',hy',hρ,hθ] using hh

end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice
