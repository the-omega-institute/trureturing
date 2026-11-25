/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/CyclicArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:consumed-native-selection-arithmetic)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Native cyclic residues, dyadic masks and affine rectangle interpolation. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal.Certificates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal
open private grain reserve C A D L M Ln Mn E0 H0 pivot scaledMargin from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal.Certificates

-- The only forbidden start is the unique gap of length m-1.
private theorem euclidean_gap_hit (g m b : ℤ) (hg : 4≤g) (hm : 2≤m)
    (hb : 0≤b ∧ b<g*m+1) (hne : b≠(g-1)*m+2) :
    ∃ δ i ε : ℤ, 0 ≤ δ ∧ δ ≤ m - 2 ∧ 0 ≤ i ∧ i < g ∧
      (ε = 0 ∨ ε = 1) ∧ ((g * m + 1) ∣ b + δ - (i * m + ε)) := by
  by_cases hlarge : (g-1)*m+2<b
  · refine ⟨g*m+1-b,0,0,?_,?_,by omega,by omega,Or.inl rfl,?_⟩
    · omega
    · nlinarith only [hlarge]
    · refine ⟨1,?_⟩; ring
  · have hsmall : b≤(g-1)*m+1 := by omega
    let i := b/m
    let u := b%m
    have hu : 0≤u ∧ u<m :=
      ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩
    have he : b=u+m*i := (Int.emod_add_mul_ediv b m).symm
    have hi : 0≤ i := by
      by_contra hn
      have hp := mul_le_mul_of_nonneg_left (show i≤-1 by omega) (show 0≤m by omega)
      nlinarith only [hp,he,hu.2,hb.1]
    by_cases hlow : u≤1
    · have hig : i<g := by
        by_contra hn
        have hh := mul_le_mul_of_nonneg_right (show g≤ i by omega) (show 0≤m by omega)
        nlinarith only [hh,he,hsmall,hu.1,hm]
      refine ⟨0,i,u,by omega,by omega,hi,hig,by omega,?_⟩
      refine ⟨0,?_⟩; nlinarith only [he]
    · have hig : i≤g-2 := by
        by_contra hn
        have hh := mul_le_mul_of_nonneg_right (show g-1≤ i by omega) (show 0≤m by omega)
        nlinarith only [hh,he,hsmall,show 2≤u by omega]
      refine ⟨m-u,i+1,0,by omega,by omega,by omega,by omega,Or.inl rfl,?_⟩
      refine ⟨0,?_⟩; nlinarith only [he]

-- General even grain g=2G. No topology, finite group enumeration or real rotations.
private theorem cyclic_cover (G m τ : ℤ) (hG : 2≤G) (hm : 2≤m)
    (hex : ¬(2*G*m+1)∣τ) :
    ∃ n l : ℤ, -(2*G)≤n ∧ n<2*G ∧ G*m-m≤l ∧ l≤G*m-2 ∧
      (2*G*m+1)∣(τ+G*m-1+n*m-l) := by
  let β := 2*G*m+1
  let a0 := τ+G*m-1
  let start := G*m-m
  let b := (start-a0)%β
  have hβ : 0<β := by dsimp [β]; nlinarith
  have hb : 0≤b ∧ b<2*G*m+1 :=
    ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ hβ⟩
  have hdb : β∣((start-a0)-b) := by
    refine ⟨(start-a0)/β,?_⟩
    have he := Int.emod_add_mul_ediv (start-a0) β
    dsimp [b]; linarith only [he]
  have hne : b≠(2*G-1)*m+2 := by
    intro he
    apply hex
    obtain ⟨w,hw⟩ := hdb
    refine ⟨-w-1,?_⟩
    rw [he] at hw
    dsimp [start,a0,β] at hw ⊢
    linear_combination -hw
  obtain ⟨δ,i,ε,hδ0,hδ1,hi0,hi1,hε,hd⟩ :=
    euclidean_gap_hit (2*G) m b (by omega) hm hb hne
  have choose (n : ℤ) (hn0 : -(2*G)≤n) (hn1 : n<2*G)
      (hs : β∣(n*m-(i*m+ε))) :
      ∃ n l : ℤ, -(2*G)≤n ∧ n<2*G ∧ G*m-m≤l ∧ l≤G*m-2 ∧
        β∣(τ+G*m-1+n*m-l) := by
    refine ⟨n,start+δ,hn0,hn1,by dsimp [start]; omega,
      by dsimp [start]; omega,?_⟩
    have hh := dvd_sub (dvd_sub hs hdb) hd
    convert hh using 1 <;> dsimp [a0,start] <;> ring
  rcases hε with rfl|rfl
  · apply choose i (by omega) hi1
    simp
  · apply choose (i-2*G) (by omega) (by omega)
    refine ⟨-1,?_⟩; dsimp [β]; ring

private theorem odd_successor_not_dvd_pow (c e : ℕ) (hc : 1≤c) :
    ¬((2:ℤ)^c+1)∣(2:ℤ)^e := by
  have hz : (2:ℕ)^c=2*2^(c-1) := by
    conv_lhs => rw [show c=(c-1)+1 by omega,pow_succ]
    ring
  have hc2 : Nat.Coprime (2^c+1) 2 := by
    apply Nat.coprime_two_right.mpr
    exact ⟨2^(c-1),by omega⟩
  intro hd
  have hd' : (2^c+1:ℕ)∣2^e := by exact_mod_cast hd
  have h1 := (hc2.pow_right e).eq_one_of_dvd hd'
  have hp : 1≤(2:ℕ)^c := Nat.one_le_two_pow
  omega

-- The shifted complete residue system [-1,g-1], including the wrap to -1.
private theorem equality_residue (g τ : ℤ) (hg : 1≤g) :
    ∃ n : ℤ, -1≤n ∧ n<g ∧ (g+1)∣(τ+1+n) := by
  refine ⟨(-τ)%(g+1)-1,?_,?_,?_⟩
  · have := Int.emod_nonneg (-τ) (by omega : g+1≠0); omega
  · have := Int.emod_lt_of_pos (-τ) (by omega : 0<g+1); omega
  · refine ⟨-((-τ)/(g+1)),?_⟩
    have := Int.emod_add_mul_ediv (-τ) (g+1)
    nlinarith only [this]

private theorem native_hr (K J n : ℤ) (hK : 1≤K) (hJ : 1≤J)
    (hn : -grain K J≤n ∧ n<grain K J) :
    ∃ h r : ℤ, 0≤h ∧ 1≤r ∧ r≤grain K J ∧ n=2*J*h-r ∧
      ((n<0 ∧ h=0 ∧ r=-n) ∨ (0≤n ∧ 1≤h ∧ h≤2*K ∧ r≤2*J)) := by
  by_cases hneg : n<0
  · exact ⟨0,-n,by omega,by omega,by omega,by ring,Or.inl ⟨hneg,rfl,rfl⟩⟩
  · let h := n/(2*J)+1
    let r := 2*J*h-n
    have hmod : 0≤n%(2*J) ∧ n%(2*J)<2*J :=
      ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩
    have he := Int.emod_add_mul_ediv n (2*J)
    have hq : 0≤n/(2*J) := by
      by_contra hnq
      have hp := mul_le_mul_of_nonneg_left (show n/(2*J)≤-1 by omega) (show 0≤2*J by omega)
      nlinarith only [hp,he,hmod.2,show 0≤n by omega]
    have hq1 : n/(2*J)<2*K := by
      by_contra hh
      have hp := mul_le_mul_of_nonneg_right (show 2*K≤n/(2*J) by omega)
        (show 0≤2*J by omega)
      dsimp [grain] at hn
      nlinarith only [hp,he,hmod.1,hn.2]
    have hr : 1 ≤ r ∧ r ≤ 2 * J := by
      dsimp [r, h]
      constructor <;> nlinarith only [he, hmod.1, hmod.2]
    have hrg : r≤grain K J := by
      have hp := mul_nonneg (show 0≤2*K-1 by omega) (show 0≤2*J by omega)
      dsimp [grain]; nlinarith only [hp,hr.2]
    exact ⟨h,r,by dsimp [h]; omega,hr.1,hrg,by dsimp [r]; ring,
      Or.inr ⟨by omega,by dsimp [h]; omega,by dsimp [h]; omega,hr.2⟩⟩

private theorem linear_interval (u v l r x : ℤ) (hx : l≤x ∧ x≤r)
    (hl : 0≤u+l*v) (hr : 0≤u+r*v) : 0≤u+x*v := by
  rcases le_total 0 v with hv|hv
  · have hp := mul_nonneg (show 0≤x-l by omega) hv
    nlinarith only [hp,hl]
  · have hp := mul_nonneg (show 0≤r-x by omega) (show 0≤-v by omega)
    nlinarith only [hp,hr]

private theorem scaled_affine (K J m t lo hi h r : ℤ) (i : Fin 4) :
    scaledMargin K J m t lo hi h r i =
      scaledMargin K J m t lo hi 0 0 i
      +h*(scaledMargin K J m t lo hi 1 0 i-scaledMargin K J m t lo hi 0 0 i)
      +r*(scaledMargin K J m t lo hi 0 1 i-scaledMargin K J m t lo hi 0 0 i) := by
  fin_cases i <;> dsimp [scaledMargin,E0,H0,pivot,grain,reserve,C,A,D,L,M,Ln,Mn] <;> ring

private theorem scaled_rectangle (K J m t lo hi h1 h2 r1 r2 h r : ℤ)
    (hh : h1≤h ∧ h≤h2) (hr : r1≤r ∧ r≤r2)
    (h11 : ∀ i,0≤scaledMargin K J m t lo hi h1 r1 i)
    (h12 : ∀ i,0≤scaledMargin K J m t lo hi h1 r2 i)
    (h21 : ∀ i,0≤scaledMargin K J m t lo hi h2 r1 i)
    (h22 : ∀ i,0≤scaledMargin K J m t lo hi h2 r2 i) :
    ∀ i,0≤scaledMargin K J m t lo hi h r i := by
  intro i
  let u := scaledMargin K J m t lo hi 0 0 i
  let v := scaledMargin K J m t lo hi 1 0 i-u
  let w := scaledMargin K J m t lo hi 0 1 i-u
  have hf (h r : ℤ) : scaledMargin K J m t lo hi h r i=u+h*v+r*w :=
    scaled_affine K J m t lo hi h r i
  have h1r : 0≤u+h1*v+r*w := linear_interval (u+h1*v) w r1 r2 r hr
    (by rw [←hf]; exact h11 i) (by rw [←hf]; exact h12 i)
  have h2r : 0≤u+h2*v+r*w := linear_interval (u+h2*v) w r1 r2 r hr
    (by rw [←hf]; exact h21 i) (by rw [←hf]; exact h22 i)
  have hhr := linear_interval (u+r*w) v h1 h2 h hh
    (by linarith only [h1r]) (by linarith only [h2r])
  rw [hf]; linarith only [hhr]

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal
