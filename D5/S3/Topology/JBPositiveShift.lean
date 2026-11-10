/- GID: D5/S3/Topology/JBPositiveShift
   generality: G
   mirror-B: D5/B/S3/Topology/JBPositiveShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Ring.Units]
   utility: none
   digest: Positive shifts of squares have original-norm generated inverses and ambient quadratic inverses. -/

module

public import D5.S3.Topology.JBAlgebra
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-! Original-norm positive square shifts and their ambient quadratic inverses. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

open D5.S3.Topology.JBAlgebra

namespace D5.S3.Topology.JBPositiveShift
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {u : X}

def quadratic (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (a v : X) : X :=
  (2 : ℝ) • S a (S a v) - S (S a a) v
private lemma jlinear (A : Data X S u) (a b c d : X) :
  (S a (S (S b c) d) - S (S b c) (S a d)) +
  (S b (S (S c a) d) - S (S c a) (S b d)) +
  (S c (S (S a b) d) - S (S a b) (S c d)) = 0 := by
  simpa only [bracket] using polarized A a b c d

theorem fundamental_identity (A : Data X S u) (a b v : X) :
    quadratic S (quadratic S a b) v = quadratic S a (quadratic S b (quadratic S a v)) := by
  have h0 := jlinear A (S (S (S a a) a) a) b b v
  have h1 := jlinear A (S (S (S a a) a) a) b v b
  have h2 := jlinear A (S (S (S a a) v) b) a b a
  have h3 := jlinear A (S (S (S a b) a) b) a a v
  have h4 := jlinear A (S (S (S a v) a) b) a b a
  have h5 := jlinear A (S (S a a) (S a a)) b b v
  have h6 := jlinear A (S (S a a) (S a a)) b v b
  have h7 := jlinear A (S (S a a) a) (S a b) b v
  have h8 := jlinear A (S (S a a) a) (S a b) v b
  have h9 := jlinear A (S (S a a) a) (S a v) b b
  have h10 := jlinear A (S (S a a) a) (S b b) v a
  have h11 := jlinear A (S (S a a) a) (S b v) b a
  have h12 := jlinear A (S (S a a) a) a b (S b v)
  have h13 := jlinear A (S (S a a) a) a v (S b b)
  have h14 := jlinear A (S (S a a) a) b b (S a v)
  have h15 := jlinear A (S (S a a) a) b v (S a b)
  have h16 := jlinear A (S (S a a) b) (S a a) b v
  have h17 := jlinear A (S (S a a) b) (S a a) v b
  have h18 := jlinear A (S (S a a) b) (S a b) a v
  have h19 := jlinear A (S (S a a) b) (S a b) v a
  have h20 := jlinear A (S (S a a) b) (S a v) a b
  have h21 := jlinear A (S (S a a) b) (S a v) b a
  have h22 := jlinear A (S (S a a) b) a a (S b v)
  have h23 := jlinear A (S (S a a) b) a b (S a v)
  have h24 := jlinear A (S (S a a) b) a v (S a b)
  have h25 := jlinear A (S (S a a) b) b v (S a a)
  have h26 := jlinear A (S (S a a) v) (S a a) b b
  have h27 := jlinear A (S (S a a) v) (S a b) a b
  have h28 := jlinear A (S (S a a) v) (S a b) b a
  have h29 := jlinear A (S (S a a) v) a a (S b b)
  have h30 := jlinear A (S (S a a) v) a b (S a b)
  have h31 := jlinear A (S (S a a) v) b b (S a a)
  have h32 := jlinear A (S (S a b) a) (S a a) b v
  have h33 := jlinear A (S (S a b) a) (S a a) v b
  have h34 := jlinear A (S (S a b) a) (S a b) a v
  have h35 := jlinear A (S (S a b) a) (S a b) v a
  have h36 := jlinear A (S (S a b) a) (S a v) a b
  have h37 := jlinear A (S (S a b) a) (S a v) b a
  have h38 := jlinear A (S (S a b) a) (S b v) a a
  have h39 := jlinear A (S (S a b) a) a a (S b v)
  have h40 := jlinear A (S (S a b) a) a b (S a v)
  have h41 := jlinear A (S (S a b) a) a v (S a b)
  have h42 := jlinear A (S (S a b) a) b v (S a a)
  have h43 := jlinear A (S (S a b) b) (S a a) a v
  have h44 := jlinear A (S (S a b) b) (S a a) v a
  have h45 := jlinear A (S (S a b) b) (S a v) a a
  have h46 := jlinear A (S (S a b) b) a a (S a v)
  have h47 := jlinear A (S (S a b) b) a v (S a a)
  have h48 := jlinear A (S (S a b) v) (S a a) a b
  have h49 := jlinear A (S (S a b) v) (S a a) b a
  have h50 := jlinear A (S (S a b) v) (S a b) a a
  have h51 := jlinear A (S (S a b) v) a a (S a b)
  have h52 := jlinear A (S (S a b) v) a b (S a a)
  have h53 := jlinear A (S (S a v) a) (S a a) b b
  have h54 := jlinear A (S (S a v) a) (S a b) a b
  have h55 := jlinear A (S (S a v) a) (S a b) b a
  have h56 := jlinear A (S (S a v) a) (S b b) a a
  have h57 := jlinear A (S (S a v) a) a a (S b b)
  have h58 := jlinear A (S (S a v) a) a b (S a b)
  have h59 := jlinear A (S (S a v) a) b b (S a a)
  have h60 := jlinear A (S (S a v) b) (S a a) a b
  have h61 := jlinear A (S (S a v) b) (S a a) b a
  have h62 := jlinear A (S (S a v) b) (S a b) a a
  have h63 := jlinear A (S (S a v) b) a a (S a b)
  have h64 := jlinear A (S (S a v) b) a b (S a a)
  have h65 := jlinear A (S (S b b) a) (S a a) a v
  have h66 := jlinear A (S (S b b) a) (S a a) v a
  have h67 := jlinear A (S (S b b) a) (S a v) a a
  have h68 := jlinear A (S (S b b) a) a a (S a v)
  have h69 := jlinear A (S (S b b) a) a v (S a a)
  have h70 := jlinear A (S (S b v) a) (S a a) a b
  have h71 := jlinear A (S (S b v) a) (S a a) b a
  have h72 := jlinear A (S (S b v) a) (S a b) a a
  have h73 := jlinear A (S (S b v) a) a b (S a a)
  have h74 := jlinear A (S (S b v) b) (S a a) a a
  have h75 := jlinear A (S (S b v) b) a a (S a a)
  have h76 := jlinear A (S a a) (S a a) (S b b) v
  have h77 := jlinear A (S a a) (S a a) (S b v) b
  have h78 := jlinear A (S a a) (S a a) b (S b v)
  have h79 := jlinear A (S a a) (S a a) v (S b b)
  have h80 := jlinear A (S a a) (S a b) (S a b) v
  have h81 := jlinear A (S a a) (S a b) (S a v) b
  have h82 := jlinear A (S a a) (S a b) (S b v) a
  have h83 := jlinear A (S a a) (S a b) a (S b v)
  have h84 := jlinear A (S a a) (S a b) b (S a v)
  have h85 := jlinear A (S a a) (S a b) v (S a b)
  have h86 := jlinear A (S a a) (S a v) (S b b) a
  have h87 := jlinear A (S a a) (S a v) a (S b b)
  have h88 := jlinear A (S a a) (S a v) b (S a b)
  have h89 := jlinear A (S a a) (S b b) a (S a v)
  have h90 := jlinear A (S a a) (S b v) a (S a b)
  have h91 := jlinear A (S a a) (S b v) b (S a a)
  have h92 := jlinear A (S a a) a a (S (S b b) v)
  have h93 := jlinear A (S a a) a a (S (S b v) b)
  have h94 := jlinear A (S a a) a b (S (S a b) v)
  have h95 := jlinear A (S a a) a b (S (S a v) b)
  have h96 := jlinear A (S a a) a b (S (S b v) a)
  have h97 := jlinear A (S a a) a v (S (S a b) b)
  have h98 := jlinear A (S a a) b b (S (S a a) v)
  have h99 := jlinear A (S a a) b v (S (S a a) b)
  have h100 := jlinear A (S a a) b v (S (S a b) a)
  have h101 := jlinear A (S a b) (S a b) (S a v) a
  have h102 := jlinear A (S a b) (S a b) a (S a v)
  have h103 := jlinear A (S a b) (S a b) v (S a a)
  have h104 := jlinear A (S a b) (S a v) a (S a b)
  have h105 := jlinear A (S a b) (S a v) b (S a a)
  have h106 := jlinear A (S a b) (S b v) a (S a a)
  have h107 := jlinear A (S a b) a a (S (S a b) v)
  have h108 := jlinear A (S a b) a a (S (S a v) b)
  have h109 := jlinear A (S a b) a a (S (S b v) a)
  have h110 := jlinear A (S a b) a v (S (S a a) b)
  have h111 := jlinear A (S a b) a v (S (S a b) a)
  have h112 := jlinear A (S a b) b v (S (S a a) a)
  have h113 := jlinear A (S a v) (S b b) a (S a a)
  have h114 := jlinear A (S a v) a a (S (S a b) b)
  have h115 := jlinear A (S a v) a a (S (S b b) a)
  have h116 := jlinear A (S a v) b b (S (S a a) a)
  have h117 := jlinear A (S b b) a a (S (S a v) a)
  have h118 := jlinear A (S b b) a v (S (S a a) a)
  have h119 := jlinear A (S b v) a a (S (S a b) a)
  have h120 := jlinear A (S b v) a b (S (S a a) a)
  have h121 := jlinear A a a a (S (S (S a b) b) v)
  have h122 := jlinear A a a a (S (S (S a b) v) b)
  have h123 := jlinear A a a a (S (S (S a v) b) b)
  have h124 := jlinear A a a a (S (S (S b b) a) v)
  have h125 := jlinear A a a a (S (S (S b v) a) b)
  have h126 := jlinear A a a a (S (S (S b v) b) a)
  have h127 := jlinear A a a a (S (S a b) (S b v))
  have h128 := jlinear A a a a (S (S a v) (S b b))
  have h129 := jlinear A a a b (S (S (S a a) b) v)
  have h130 := jlinear A a a b (S (S (S a a) v) b)
  have h131 := jlinear A a a b (S (S (S a b) a) v)
  have h132 := jlinear A a a b (S (S (S a b) v) a)
  have h133 := jlinear A a a b (S (S (S a v) a) b)
  have h134 := jlinear A a a b (S (S (S a v) b) a)
  have h135 := jlinear A a a b (S (S (S b v) a) a)
  have h136 := jlinear A a a b (S (S a a) (S b v))
  have h137 := jlinear A a a b (S (S a b) (S a v))
  have h138 := jlinear A a a v (S (S (S a a) b) b)
  have h139 := jlinear A a a v (S (S (S a b) a) b)
  have h140 := jlinear A a a v (S (S (S a b) b) a)
  have h141 := jlinear A a a v (S (S (S b b) a) a)
  have h142 := jlinear A a a v (S (S a a) (S b b))
  have h143 := jlinear A a a v (S (S a b) (S a b))
  have h144 := jlinear A a b b (S (S (S a a) a) v)
  have h145 := jlinear A a b b (S (S (S a a) v) a)
  have h146 := jlinear A a b b (S (S (S a v) a) a)
  have h147 := jlinear A a b b (S (S a a) (S a v))
  have h148 := jlinear A a b v (S (S (S a a) a) b)
  have h149 := jlinear A a b v (S (S (S a a) b) a)
  have h150 := jlinear A a b v (S (S (S a b) a) a)
  have h151 := jlinear A a b v (S (S a a) (S a b))
  have h152 := jlinear A b b v (S (S (S a a) a) a)
  have h153 := jlinear A b b v (S (S a a) (S a a))
  have h154 := congrArg (fun z : X => (S z v)) (jlinear A (S a a) (S a a) b b)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h154
  have h155 := congrArg (fun z : X => (S z v)) (jlinear A (S a a) (S a b) b a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h155
  have h156 := congrArg (fun z : X => (S z v)) (jlinear A (S a a) a a (S b b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h156
  have h157 := congrArg (fun z : X => (S z v)) (jlinear A (S a a) a b (S a b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h157
  have h158 := congrArg (fun z : X => (S z v)) (jlinear A (S a a) b b (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h158
  have h159 := congrArg (fun z : X => (S z v)) (jlinear A (S a b) a a (S a b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h159
  have h160 := congrArg (fun z : X => (S z v)) (jlinear A (S a b) a b (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h160
  have h161 := congrArg (fun z : X => (S z v)) (jlinear A a a a (S (S a b) b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h161
  have h162 := congrArg (fun z : X => (S z v)) (jlinear A a a a (S (S b b) a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h162
  have h163 := congrArg (fun z : X => (S z v)) (jlinear A a a b (S (S a b) a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h163
  have h164 := congrArg (fun z : X => (S z b)) (jlinear A (S (S a a) v) a b a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h164
  have h165 := congrArg (fun z : X => (S z b)) (jlinear A (S (S a v) a) a b a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h165
  have h166 := congrArg (fun z : X => (S z b)) (jlinear A (S a a) (S a b) v a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h166
  have h167 := congrArg (fun z : X => (S z b)) (jlinear A (S a a) (S a v) b a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h167
  have h168 := congrArg (fun z : X => (S z b)) (jlinear A (S a a) a a (S b v))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h168
  have h169 := congrArg (fun z : X => (S z b)) (jlinear A (S a a) a b (S a v))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h169
  have h170 := congrArg (fun z : X => (S z b)) (jlinear A (S a a) a v (S a b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h170
  have h171 := congrArg (fun z : X => (S z b)) (jlinear A (S a a) b v (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h171
  have h172 := congrArg (fun z : X => (S z b)) (jlinear A (S a b) a a (S a v))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h172
  have h173 := congrArg (fun z : X => (S z b)) (jlinear A (S a b) a v (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h173
  have h174 := congrArg (fun z : X => (S z b)) (jlinear A (S a v) a a (S a b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h174
  have h175 := congrArg (fun z : X => (S z b)) (jlinear A (S a v) a b (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h175
  have h176 := congrArg (fun z : X => (S z b)) (jlinear A (S b v) a a (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h176
  have h177 := congrArg (fun z : X => (S z b)) (jlinear A a a a (S (S a b) v))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h177
  have h178 := congrArg (fun z : X => (S z b)) (jlinear A a a a (S (S a v) b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h178
  have h179 := congrArg (fun z : X => (S z b)) (jlinear A a a a (S (S b v) a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h179
  have h180 := congrArg (fun z : X => (S z b)) (jlinear A a a b (S (S a v) a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h180
  have h181 := congrArg (fun z : X => (S z b)) (jlinear A a a v (S (S a a) b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h181
  have h182 := congrArg (fun z : X => (S z b)) (jlinear A a a v (S (S a b) a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h182
  have h183 := congrArg (fun z : X => (S (S b v) z)) (jlinear A (S a a) a b a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h183
  have h184 := congrArg (fun z : X => (S (S b v) z)) (jlinear A (S a b) a a a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h184
  have h185 := congrArg (fun z : X => (S (S z b) v)) (jlinear A a a a (S a b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h185
  have h186 := congrArg (fun z : X => (S (S z v) b)) (jlinear A a a a (S a b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h186
  have h187 := congrArg (fun z : X => (S (S b v) z)) (jlinear A a a a (S a b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h187
  have h188 := congrArg (fun z : X => (S (S b v) z)) (jlinear A a a b (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h188
  have h189 := congrArg (fun z : X => (S (S z b) b)) (jlinear A (S a a) a v a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h189
  have h190 := congrArg (fun z : X => (S (S b b) z)) (jlinear A (S a a) a v a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h190
  have h191 := congrArg (fun z : X => (S (S z b) b)) (jlinear A (S a v) a a a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h191
  have h192 := congrArg (fun z : X => (S (S b b) z)) (jlinear A (S a v) a a a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h192
  have h193 := congrArg (fun z : X => (S (S z b) b)) (jlinear A a a a (S a v))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h193
  have h194 := congrArg (fun z : X => (S (S b b) z)) (jlinear A a a a (S a v))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h194
  have h195 := congrArg (fun z : X => (S (S z b) b)) (jlinear A a a v (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h195
  have h196 := congrArg (fun z : X => (S (S b b) z)) (jlinear A a a v (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h196
  have h197 := congrArg (fun z : X => (S (S (S z b) b) v)) (jlinear A a a a a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h197
  have h198 := congrArg (fun z : X => (S (S (S z b) v) b)) (jlinear A a a a a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h198
  have h199 := congrArg (fun z : X => (S (S (S z v) b) b)) (jlinear A a a a a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h199
  have h200 := congrArg (fun z : X => (S (S (S b b) v) z)) (jlinear A a a a a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h200
  have h201 := congrArg (fun z : X => (S (S z b) (S b v))) (jlinear A a a a a)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h201
  have h202 := congrArg (fun z : X => (S z a)) (jlinear A (S a a) b b (S a v))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h202
  have h203 := congrArg (fun z : X => (S z a)) (jlinear A (S a a) b v (S a b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h203
  have h204 := congrArg (fun z : X => (S z a)) (jlinear A (S a b) a b (S a v))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h204
  have h205 := congrArg (fun z : X => (S z a)) (jlinear A (S a b) a v (S a b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h205
  have h206 := congrArg (fun z : X => (S z a)) (jlinear A (S a b) b v (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h206
  have h207 := congrArg (fun z : X => (S z a)) (jlinear A (S a v) a b (S a b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h207
  have h208 := congrArg (fun z : X => (S z a)) (jlinear A (S a v) b b (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h208
  have h209 := congrArg (fun z : X => (S z a)) (jlinear A (S b v) a a (S a b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h209
  have h210 := congrArg (fun z : X => (S z a)) (jlinear A (S b v) a b (S a a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h210
  have h211 := congrArg (fun z : X => (S z a)) (jlinear A a a b (S (S a b) v))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h211
  have h212 := congrArg (fun z : X => (S z a)) (jlinear A a a b (S (S b v) a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h212
  have h213 := congrArg (fun z : X => (S z a)) (jlinear A a a v (S (S a b) b))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h213
  have h214 := congrArg (fun z : X => (S z a)) (jlinear A a a v (S (S b b) a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h214
  have h215 := congrArg (fun z : X => (S z a)) (jlinear A a b b (S (S a a) v))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h215
  have h216 := congrArg (fun z : X => (S z a)) (jlinear A a b v (S (S a b) a))
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h216
  have h217 := congrArg (fun z : X => (S (S z v) a)) (jlinear A (S a b) a a b)
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, RingHom.id_apply] at h217
  simp only [quadratic, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, RingHom.id_apply]
  simp only [A.symm] at *
  linear_combination (norm := module) ((((((((-10 : ℝ) • h0 + ((2 : ℝ) • h1 + (4 : ℝ) • h2)) +
    ((16 : ℝ) • h3 + ((-8 : ℝ) • h4 + (10 : ℝ) • h5))) + (((-4 : ℝ) • h6 + ((2 : ℝ) • h7 + (2 : ℝ)
    • h8)) + (((2 : ℝ) • h9 + (1 : ℝ) • h10) + ((2 : ℝ) • h11 + (-2 : ℝ) • h12)))) + ((((-1 : ℝ) •
    h13 + ((-1 : ℝ) • h14 + (-2 : ℝ) • h15)) + (((1 : ℝ) • h16 + (1 : ℝ) • h17) + ((-2 : ℝ) • h18
    + (2 : ℝ) • h19))) + (((-2 : ℝ) • h20 + ((2 : ℝ) • h21 + (1 : ℝ) • h22)) + (((-2 : ℝ) • h23 +
    (-2 : ℝ) • h24) + ((-5 : ℝ) • h25 + (-1 : ℝ) • h26))))) + (((((-14 : ℝ) • h27 + ((2 : ℝ) • h28
    + (5/2 : ℝ) • h29)) + ((2 : ℝ) • h30 + ((-1/2 : ℝ) • h31 + (10 : ℝ) • h32))) + (((-14 : ℝ) •
    h33 + ((4 : ℝ) • h34 + (-28 : ℝ) • h35)) + (((4 : ℝ) • h36 + (20 : ℝ) • h37) + ((24 : ℝ) • h38
    + (-14 : ℝ) • h39)))) + ((((-12 : ℝ) • h40 + ((4 : ℝ) • h41 + (10 : ℝ) • h42)) + (((-2 : ℝ) •
    h43 + (-10 : ℝ) • h44) + ((-4 : ℝ) • h45 + (-6 : ℝ) • h46))) + (((2 : ℝ) • h47 + ((-2 : ℝ) •
    h48 + (14 : ℝ) • h49)) + (((-4 : ℝ) • h50 + (10 : ℝ) • h51) + ((-6 : ℝ) • h52 + (-2 : ℝ) •
    h53)))))) + ((((((12 : ℝ) • h54 + ((-12 : ℝ) • h55 + (4 : ℝ) • h56)) + ((-3 : ℝ) • h57 + ((-4
    : ℝ) • h58 + (1 : ℝ) • h59))) + (((6 : ℝ) • h60 + ((-2 : ℝ) • h61 + (12 : ℝ) • h62)) + (((-6 :
    ℝ) • h63 + (2 : ℝ) • h64) + ((-1 : ℝ) • h65 + (5 : ℝ) • h66)))) + ((((-2 : ℝ) • h67 + ((2 : ℝ)
    • h68 + (-4 : ℝ) • h69)) + (((-2 : ℝ) • h70 + (2 : ℝ) • h71) + ((-4 : ℝ) • h72 + (-4 : ℝ) •
    h73))) + (((-4 : ℝ) • h74 + ((2 : ℝ) • h75 + (1/4 : ℝ) • h76)) + (((1/2 : ℝ) • h77 + (-1/2 :
    ℝ) • h78) + ((3/4 : ℝ) • h79 + (1 : ℝ) • h80))))) + (((((2 : ℝ) • h81 + ((2 : ℝ) • h82 + (2 :
    ℝ) • h83)) + (((-18 : ℝ) • h84 + (-10 : ℝ) • h85) + ((1 : ℝ) • h86 + (-3 : ℝ) • h87))) + (((14
    : ℝ) • h88 + ((2 : ℝ) • h89 + (8 : ℝ) • h90)) + (((-2 : ℝ) • h91 + (1/2 : ℝ) • h92) + ((3 : ℝ)
    • h93 + (-4 : ℝ) • h94)))) + ((((-4 : ℝ) • h95 + ((4 : ℝ) • h96 + (12 : ℝ) • h97)) + (((2 : ℝ)
    • h98 + (2 : ℝ) • h99) + ((-4 : ℝ) • h100 + (2 : ℝ) • h101))) + (((-2 : ℝ) • h102 + ((11 : ℝ)
    • h103 + (-4 : ℝ) • h104)) + (((-2 : ℝ) • h105 + (-16 : ℝ) • h106) + ((-20 : ℝ) • h107 + (4 :
    ℝ) • h108))))))) + (((((((16 : ℝ) • h109 + ((16 : ℝ) • h110 + (16 : ℝ) • h111)) + ((-4 : ℝ) •
    h112 + ((-2 : ℝ) • h113 + (4 : ℝ) • h114))) + (((2 : ℝ) • h115 + ((2 : ℝ) • h116 + (-2 : ℝ) •
    h117)) + (((-1 : ℝ) • h118 + (-12 : ℝ) • h119) + ((-2 : ℝ) • h120 + (-10/3 : ℝ) • h121)))) +
    ((((14/3 : ℝ) • h122 + ((-2/3 : ℝ) • h123 + (5/3 : ℝ) • h124)) + (((2/3 : ℝ) • h125 + (-4/3 :
    ℝ) • h126) + ((2/3 : ℝ) • h127 + (1/3 : ℝ) • h128))) + (((1 : ℝ) • h129 + ((-3 : ℝ) • h130 +
    (-14 : ℝ) • h131)) + (((-2 : ℝ) • h132 + (2 : ℝ) • h133) + ((6 : ℝ) • h134 + (-2 : ℝ) •
    h135))))) + (((((1 : ℝ) • h136 + ((2 : ℝ) • h137 + (1 : ℝ) • h138)) + ((-6 : ℝ) • h139 + ((-2
    : ℝ) • h140 + (-1 : ℝ) • h141))) + (((1/2 : ℝ) • h142 + ((1 : ℝ) • h143 + (1 : ℝ) • h144)) +
    (((-7 : ℝ) • h145 + (6 : ℝ) • h146) + ((1 : ℝ) • h147 + (2 : ℝ) • h148)))) + ((((-2 : ℝ) •
    h149 + ((4 : ℝ) • h150 + (2 : ℝ) • h151)) + (((1 : ℝ) • h152 + (3/4 : ℝ) • h153) + ((2 : ℝ) •
    h154 + (4 : ℝ) • h155))) + (((-1/2 : ℝ) • h156 + ((-2 : ℝ) • h157 + (-1/2 : ℝ) • h158)) +
    (((10 : ℝ) • h159 + (6 : ℝ) • h160) + ((4/3 : ℝ) • h161 + (-5/3 : ℝ) • h162)))))) + ((((((4 :
    ℝ) • h163 + ((-4 : ℝ) • h164 + (8 : ℝ) • h165)) + ((4 : ℝ) • h166 + ((-4 : ℝ) • h167 + (-1 :
    ℝ) • h168))) + (((6 : ℝ) • h169 + ((-2 : ℝ) • h170 + (3 : ℝ) • h171)) + (((-6 : ℝ) • h172 +
    (-10 : ℝ) • h173) + ((10 : ℝ) • h174 + (-2 : ℝ) • h175)))) + ((((2 : ℝ) • h176 + ((-4/3 : ℝ) •
    h177 + (4/3 : ℝ) • h178)) + (((-2 : ℝ) • h179 + (-4 : ℝ) • h180) + ((-4 : ℝ) • h181 + (-4 : ℝ)
    • h182))) + (((-2 : ℝ) • h183 + ((-10 : ℝ) • h184 + (-4/3 : ℝ) • h185)) + (((-4/3 : ℝ) • h186
    + (-2/3 : ℝ) • h187) + ((1 : ℝ) • h188 + (4 : ℝ) • h189))))) + (((((-7 : ℝ) • h190 + ((-4 : ℝ)
    • h191 + (1 : ℝ) • h192)) + (((8/3 : ℝ) • h193 + (-13/3 : ℝ) • h194) + ((-2 : ℝ) • h195 +
    (13/2 : ℝ) • h196))) + (((-2/3 : ℝ) • h197 + ((20/3 : ℝ) • h198 + (-2 : ℝ) • h199)) + (((3 :
    ℝ) • h200 + (-4 : ℝ) • h201) + ((1 : ℝ) • h202 + (18 : ℝ) • h203)))) + ((((20 : ℝ) • h204 +
    ((-12 : ℝ) • h205 + (-6 : ℝ) • h206)) + (((-12 : ℝ) • h207 + (-3 : ℝ) • h208) + ((4 : ℝ) •
    h209 + (4 : ℝ) • h210))) + (((8 : ℝ) • h211 + ((-2 : ℝ) • h212 + (-8 : ℝ) • h213)) + (((1 : ℝ)
    • h214 + (-2 : ℝ) • h215) + ((-24 : ℝ) • h216 + (-16 : ℝ) • h217))))))))


private lemma unit_mem (a : X) : u ∈ generated S u a :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨0, rfl⟩)
private lemma self_mem (A : Data X S u) (a : X) : a ∈ generated S u a := by
  have hp : npow S u a 1 ∈ generated S u a :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, rfl⟩)
  simpa only [npow, A.symm a u, A.unit_mul] using hp
private lemma generated_square_le (A : Data X S u) (z : X) :
    generated S u (S z z) ≤ generated S u z := by
  have hm := (generated_algebra A z).1
  have hz := self_mem A z
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    induction n with
    | zero => exact unit_mem z
    | succ n ih => exact hm _ (hm z hz z hz) _ ih
  · exact Submodule.isClosed_topologicalClosure _
private lemma shift_lower (A : Data X S u) (z x : X) (hx : x ∈ generated S u z)
    (t : ℝ) (ht : 0 < t) :
    t * ‖x‖ ≤ ‖S (S z z + t • u) x‖ := by
  have hz := self_mem A z
  obtain ⟨hm,ha,_⟩ := generated_algebra A z
  have hzx := hm z hz x hx
  have h1 : S (S z x) (S z x) = S (S (S z z) x) x := by
    rw [← ha (S z x) hzx z hz x hx, A.symm (S z x) z,
      ← ha z hz z hz x hx]
  have h2 : S ((Real.sqrt t) • x) ((Real.sqrt t) • x) = t • S x x := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul, ← pow_two, Real.sq_sqrt ht.le]
  have h3 : S ((Real.sqrt t) • x) ((Real.sqrt t) • x) + S (S z x) (S z x) =
      S (S (S z z + t • u) x) x := by
    rw [h1,h2]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, A.unit_mul]
    abel
  have hn : ‖S ((Real.sqrt t) • x) ((Real.sqrt t) • x)‖ = t * ‖x‖ ^ 2 := by
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos ht, A.square_norm]
  have hb := A.square_mono ((Real.sqrt t) • x) (S z x)
  rw [hn,h3] at hb
  have hc := hb.trans (A.product_norm (S (S z z + t • u) x) x)
  by_cases hzero : x = 0
  · simp [hzero]
  · have hpos := norm_pos_iff.mpr hzero
    apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith only [hc]
private lemma unit_norm_le (A : Data X S u) : ‖u‖ ≤ 1 := by
  have h := A.square_norm u
  rw [A.unit_mul] at h
  nlinarith [norm_nonneg u]

section OperatorContinuation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
private lemma inverse_bound (B : E →L[ℝ] E)
    (hb : ∀ (s : ℝ), 0 < s → ∀ x : E, s * ‖x‖ ≤ ‖(B + s • 1) x‖)
    (s : ℝ) (hs : 0 < s) (w : (E →L[ℝ] E)ˣ)
    (hw : (w : E →L[ℝ] E) = B + s • 1) :
    ‖(↑w⁻¹ : E →L[ℝ] E)‖ ≤ s⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hs.le)
  intro x
  have h := hb s hs ((↑w⁻¹ : E →L[ℝ] E) x)
  rw [← hw] at h
  have hh : (w : E →L[ℝ] E) ((↑w⁻¹ : E →L[ℝ] E) x) = x := by
    exact congrArg (fun T : E →L[ℝ] E => T x) w.val_inv
  rw [hh] at h
  exact (le_inv_mul_iff₀ hs).mpr h
private lemma positive_shift_unit (B : E →L[ℝ] E)
    (hb : ∀ (s : ℝ), 0 < s → ∀ x : E, s * ‖x‖ ≤ ‖(B + s • 1) x‖)
    (t : ℝ) (ht : 0 < t) : IsUnit (B + t • 1) := by
  have descend : ∀ n : ℕ, ∀ w : (E →L[ℝ] E)ˣ,
      (w : E →L[ℝ] E) = B + (t + (n : ℝ) * t) • 1 → IsUnit (B + t • 1) := by
    intro n
    induction n with
    | zero =>
      intro w hw
      have hw' : (w : E →L[ℝ] E) = B + t • 1 := by simpa using hw
      rw [← hw']
      exact w.isUnit
    | succ n ih =>
      intro w hw
      have hs : 0 < t + ((n + 1 : ℕ) : ℝ) * t := by positivity
      have hinv := inverse_bound B hb _ hs w hw
      have hsmall : ‖t • (↑w⁻¹ : E →L[ℝ] E)‖ < 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        calc
          _ ≤ t * (t + ((n + 1 : ℕ) : ℝ) * t)⁻¹ := mul_le_mul_of_nonneg_left hinv ht.le
          _ < 1 := by
            rw [← div_eq_mul_inv, div_lt_one hs]
            have : 0 < ((n + 1 : ℕ) : ℝ) * t := mul_pos (by positivity) ht
            linarith
      let v := w * Units.oneSub (t • (↑w⁻¹ : E →L[ℝ] E)) hsmall
      apply ih v
      change (w : E →L[ℝ] E) * (1 - t • (↑w⁻¹ : E →L[ℝ] E)) = _
      rw [mul_sub, mul_one, mul_smul_comm, Units.mul_inv, hw]
      simp only [Nat.cast_add, Nat.cast_one]
      module
  obtain ⟨n, hn⟩ := exists_nat_gt (‖B‖ / t)
  have hn' : ‖B‖ < (n : ℝ) * t := (div_lt_iff₀ ht).mp hn
  let s := t + (n : ℝ) * t
  have hs : 0 < s := by dsimp [s]; positivity
  have hsB : ‖B‖ < s := by dsimp [s]; linarith
  have hsmall : ‖(-s⁻¹) • B‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hs)]
    rw [mul_comm, ← div_eq_mul_inv, div_lt_one hs]
    exact hsB
  have hsc : IsUnit (s • (1 : E →L[ℝ] E)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (isUnit_iff_ne_zero.mpr hs.ne').map (algebraMap ℝ (E →L[ℝ] E))
  have hunit := hsc.mul (Units.oneSub ((-s⁻¹) • B) hsmall).isUnit
  have heq : (s • (1 : E →L[ℝ] E)) * (1 - (-s⁻¹) • B) = B + s • 1 := by
    rw [mul_sub, mul_one, smul_mul_smul_comm, one_mul]
    have hh : s * -s⁻¹ = -1 := by field_simp
    rw [hh,neg_one_smul,sub_neg_eq_add,add_comm]
  rw [Units.val_oneSub, heq] at hunit
  obtain ⟨w,hw⟩ := hunit
  exact descend n w hw

end OperatorContinuation

private lemma quadratic_unit (A : Data X S u) (v : X) : quadratic S u v = v := by
  simp only [quadratic, A.unit_mul, two_smul, add_sub_cancel_right]

private theorem ambient_bijective (A : Data X S u) (z a c : X)
    (ha : a ∈ generated S u z) (hc : c ∈ generated S u z) (hinv : S a c = u) :
    Function.Bijective (quadratic S a) := by
  obtain ⟨hclosed,hassoc,_⟩ := generated_algebra A z
  have haa := hclosed a ha a ha
  have hacc : S a (S c c) = c := by
    rw [← hassoc a ha c hc c hc,hinv,A.unit_mul]
  have haac : S (S a a) c = a := by
    rw [hassoc a ha a ha c hc,hinv,A.symm a u,A.unit_mul]
  have haacc : S (S a a) (S c c) = u := by
    rw [← hassoc (S a a) haa c hc c hc,haac,hinv]
  have hu : quadratic S a (S c c) = u := by
    rw [quadratic,hacc,hinv,haacc,two_smul,add_sub_cancel_right]
  have hs (v : X) : quadratic S a (quadratic S (S c c) (quadratic S a v)) = v := by
    have h := fundamental_identity A a (S c c) v
    rw [hu,quadratic_unit A] at h
    exact h.symm
  constructor
  · intro x y hxy
    calc
      x = quadratic S a (quadratic S (S c c) (quadratic S a x)) := (hs x).symm
      _ = quadratic S a (quadratic S (S c c) (quadratic S a y)) := congrArg (fun v => quadratic S
        a (quadratic S (S c c) v)) hxy
      _ = y := hs y
  · intro y
    exact ⟨quadratic S (S c c) (quadratic S a y),hs y⟩

section Complete
variable [CompleteSpace X]
/-- The inverse lies in the original closed generated algebra and obeys the original norm bound. -/
theorem positive_shift_generated_inverse (A : Data X S u) (z : X) (t : ℝ) (ht : 0 < t) :
    ∃ b : X, b ∈ generated S u (S z z) ∧
      S (S z z + t • u) b = u ∧ ‖b‖ ≤ t⁻¹ := by
  let C := generated S u (S z z)
  let : CompleteSpace C := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hmul (x : X) (hx : x ∈ C) : S (S z z) x ∈ C :=
    (generated_algebra A (S z z)).1 _ (self_mem A _) x hx
  let B : C →L[ℝ] C := (lmul A (S z z)).restrict hmul
  have hcoer (s : ℝ) (hs : 0 < s) (x : C) :
      s * ‖x‖ ≤ ‖(B + s • 1) x‖ := by
    change s * ‖(x : X)‖ ≤ ‖S (S z z) (x : X) + s • (x : X)‖
    have h := shift_lower A z (x : X) ((generated_square_le A z) x.property) s hs
    simpa only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, A.unit_mul] using h
  have hu : IsUnit (B + t • 1) := positive_shift_unit B hcoer t ht
  obtain ⟨b,hb⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2 ⟨u,unit_mem _⟩
  have heq : S (S z z + t • u) (b : X) = u := by
    have h := congrArg (fun x : C => (x : X)) hb
    change S (S z z) (b : X) + t • (b : X) = u at h
    simpa only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, A.unit_mul] using h
  refine ⟨b,b.property,heq,?_⟩
  have hl := shift_lower A z (b : X) ((generated_square_le A z) b.property) t ht
  rw [heq] at hl
  have hb1 : t * ‖(b : X)‖ ≤ 1 := hl.trans (unit_norm_le A)
  rw [inv_eq_one_div]
  exact (le_div_iff₀ ht).mpr (by nlinarith only [hb1])

/-- Positive square shifts have bijective quadratic representations on the entire original
  carrier. -/
theorem positive_shift_quadratic_bijective (A : Data X S u) (z : X) (t : ℝ) (ht : 0 < t) :
    Function.Bijective (quadratic S (S z z + t • u)) := by
  obtain ⟨b,hb,hinv,_⟩ := positive_shift_generated_inverse A z t ht
  have hz := self_mem A z
  have hzz : S z z ∈ generated S u z := (generated_algebra A z).1 z hz z hz
  have ha : S z z + t • u ∈ generated S u z :=
    (generated S u z).add_mem hzz ((generated S u z).smul_mem t (unit_mem z))
  exact ambient_bijective A z _ b ha ((generated_square_le A z) hb) hinv

end Complete
#print axioms fundamental_identity
#print axioms positive_shift_generated_inverse
#print axioms positive_shift_quadratic_bijective
end D5.S3.Topology.JBPositiveShift
