/- GID: D5/S3/Arith/Congruence/ZhangLComplexityEventualStability
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/ZhangLComplexityEventualStability
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every positive-multiple orbit reaches permanent linear l-complexity growth. -/

/-
admission_basis: open-problem-resolution (#19862; Proved)
escape_witness: none (the settling result supplies the open-problem basis).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21973
The public value, complexity and A definitions express natural evaluation,
minimum leaf count and permanent linear growth. mem_A_iff identifies their
attainable leaf counts with the existing evaluator and complexity at modulus
zero, without substituting that owner in the claim.
The generic antitone chain condition is applied directly from pinned Mathlib.
Per-declaration proof_shape (same-delivery helpers inlined):
value: proof_shape: bind-only (source expression recursion);
  escape_witness: none; consumers: complexity, mem_A_iff.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.below sha256:8ae1b629a34aec18ef56b97654aa55479560cd07f2cf35fd2c8d3dc20e1c4516
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.brecOn sha256:328c96c96454be37fc79aa37cada7e5273c70e43981f5cec87dca80085cf882a
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.casesOn sha256:78c700daab30f76ffe09800d4b0588bd4ab467b77044df35cb629b2f4c128a6e
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.mul sha256:aa1e620f45aac38f6497aad7b8fba43cab607efe9873fbeed1e5f32222b3eede
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
complexity: proof_shape: bind-only (source minimum);
  escape_witness: none; consumers: A.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.below sha256:8ae1b629a34aec18ef56b97654aa55479560cd07f2cf35fd2c8d3dc20e1c4516
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.brecOn sha256:328c96c96454be37fc79aa37cada7e5273c70e43981f5cec87dca80085cf882a
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.casesOn sha256:78c700daab30f76ffe09800d4b0588bd4ab467b77044df35cb629b2f4c128a6e
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.leaves sha256:021be95ca29bae7bb0d05daefe11a481032440a597ba0cfafda410c77913ba89
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.mul sha256:aa1e620f45aac38f6497aad7b8fba43cab607efe9873fbeed1e5f32222b3eede
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
A: proof_shape: bind-only (source predicate);
  escape_witness: none; consumers: claim.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.below sha256:8ae1b629a34aec18ef56b97654aa55479560cd07f2cf35fd2c8d3dc20e1c4516
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.brecOn sha256:328c96c96454be37fc79aa37cada7e5273c70e43981f5cec87dca80085cf882a
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.casesOn sha256:78c700daab30f76ffe09800d4b0588bd4ab467b77044df35cb629b2f4c128a6e
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.leaves sha256:021be95ca29bae7bb0d05daefe11a481032440a597ba0cfafda410c77913ba89
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.mul sha256:aa1e620f45aac38f6497aad7b8fba43cab607efe9873fbeed1e5f32222b3eede
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
claim: proof_shape: bind-only (source question);
  escape_witness: none; consumers: result.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.below sha256:8ae1b629a34aec18ef56b97654aa55479560cd07f2cf35fd2c8d3dc20e1c4516
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.brecOn sha256:328c96c96454be37fc79aa37cada7e5273c70e43981f5cec87dca80085cf882a
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.casesOn sha256:78c700daab30f76ffe09800d4b0588bd4ab467b77044df35cb629b2f4c128a6e
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.leaves sha256:021be95ca29bae7bb0d05daefe11a481032440a597ba0cfafda410c77913ba89
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.mul sha256:aa1e620f45aac38f6497aad7b8fba43cab607efe9873fbeed1e5f32222b3eede
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
complexity_attained: proof_shape: content (sum-of-leaves construction after inlining; Nat.sInf_mem applied directly);
  escape_witness: none; consumers: complexity_mul_le, orbit_lower_bound.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.eval sha256:9867c01aa7794127f4c5fbefc7b6ac71e0b3449100ab24051ebf7c5179654cf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.leaves sha256:021be95ca29bae7bb0d05daefe11a481032440a597ba0cfafda410c77913ba89
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.complexity sha256:e32ade5c13c9992a30d431263f523982a3d74d7a4a311545cfa2dca933aa8d35
complexity_mul_le: proof_shape: content (one-leaf extension of a shortest expression after inlining);
  escape_witness: none; consumers: defect_antitone.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.eval sha256:9867c01aa7794127f4c5fbefc7b6ac71e0b3449100ab24051ebf7c5179654cf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.leaves sha256:021be95ca29bae7bb0d05daefe11a481032440a597ba0cfafda410c77913ba89
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.mul sha256:aa1e620f45aac38f6497aad7b8fba43cab607efe9873fbeed1e5f32222b3eede
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.complexity sha256:e32ade5c13c9992a30d431263f523982a3d74d7a4a311545cfa2dca933aa8d35
defect_antitone: proof_shape: content (expression extension after inlining);
  escape_witness: none; consumers: result.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.eval sha256:9867c01aa7794127f4c5fbefc7b6ac71e0b3449100ab24051ebf7c5179654cf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.leaves sha256:021be95ca29bae7bb0d05daefe11a481032440a597ba0cfafda410c77913ba89
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.mul sha256:aa1e620f45aac38f6497aad7b8fba43cab607efe9873fbeed1e5f32222b3eede
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.complexity sha256:e32ade5c13c9992a30d431263f523982a3d74d7a4a311545cfa2dca933aa8d35
defect_pos: proof_shape: content (exponential expression bound after inlining);
  escape_witness: none; consumers: result.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.eval sha256:9867c01aa7794127f4c5fbefc7b6ac71e0b3449100ab24051ebf7c5179654cf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.leaves sha256:021be95ca29bae7bb0d05daefe11a481032440a597ba0cfafda410c77913ba89
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.mul sha256:aa1e620f45aac38f6497aad7b8fba43cab607efe9873fbeed1e5f32222b3eede
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.rec sha256:7f480031c4db7b1b1088ede9794220c6a7c682d5167132d53379a246fc1c60ff
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.complexity sha256:e32ade5c13c9992a30d431263f523982a3d74d7a4a311545cfa2dca933aa8d35
exists_value: proof_shape: content (inductive sum-of-leaves construction);
  escape_witness: none; consumers: complexity_attained.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.eval sha256:9867c01aa7794127f4c5fbefc7b6ac71e0b3449100ab24051ebf7c5179654cf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
mem_A_iff: proof_shape: bind-only (structural evaluation and injective-cast normalization);
  escape_witness: none; consumers: result.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.below sha256:8ae1b629a34aec18ef56b97654aa55479560cd07f2cf35fd2c8d3dc20e1c4516
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.brecOn sha256:328c96c96454be37fc79aa37cada7e5273c70e43981f5cec87dca80085cf882a
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.casesOn sha256:78c700daab30f76ffe09800d4b0588bd4ab467b77044df35cb629b2f4c128a6e
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.eval sha256:9867c01aa7794127f4c5fbefc7b6ac71e0b3449100ab24051ebf7c5179654cf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.leaves sha256:021be95ca29bae7bb0d05daefe11a481032440a597ba0cfafda410c77913ba89
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.mul sha256:aa1e620f45aac38f6497aad7b8fba43cab607efe9873fbeed1e5f32222b3eede
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.rec sha256:7f480031c4db7b1b1088ede9794220c6a7c682d5167132d53379a246fc1c60ff
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.complexity sha256:e32ade5c13c9992a30d431263f523982a3d74d7a4a311545cfa2dca933aa8d35
orbit_lower_bound: proof_shape: content (exponential expression bound after inlining);
  escape_witness: none; consumers: defect_pos.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.eval sha256:9867c01aa7794127f4c5fbefc7b6ac71e0b3449100ab24051ebf7c5179654cf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.leaves sha256:021be95ca29bae7bb0d05daefe11a481032440a597ba0cfafda410c77913ba89
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.mul sha256:aa1e620f45aac38f6497aad7b8fba43cab607efe9873fbeed1e5f32222b3eede
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.rec sha256:7f480031c4db7b1b1088ede9794220c6a7c682d5167132d53379a246fc1c60ff
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.complexity sha256:e32ade5c13c9992a30d431263f523982a3d74d7a4a311545cfa2dca933aa8d35
result: proof_shape: content (expression constructions and structural bound after inlining; Mathlib antitone chain condition applied directly);
  escape_witness: none; consumers: settling result.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.below sha256:8ae1b629a34aec18ef56b97654aa55479560cd07f2cf35fd2c8d3dc20e1c4516
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.brecOn sha256:328c96c96454be37fc79aa37cada7e5273c70e43981f5cec87dca80085cf882a
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.casesOn sha256:78c700daab30f76ffe09800d4b0588bd4ab467b77044df35cb629b2f4c128a6e
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.eval sha256:9867c01aa7794127f4c5fbefc7b6ac71e0b3449100ab24051ebf7c5179654cf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.leaves sha256:021be95ca29bae7bb0d05daefe11a481032440a597ba0cfafda410c77913ba89
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.mul sha256:aa1e620f45aac38f6497aad7b8fba43cab607efe9873fbeed1e5f32222b3eede
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.rec sha256:7f480031c4db7b1b1088ede9794220c6a7c682d5167132d53379a246fc1c60ff
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.complexity sha256:e32ade5c13c9992a30d431263f523982a3d74d7a4a311545cfa2dca933aa8d35
value_bounds: proof_shape: content (structural induction with an exponential leaf bound);
  escape_witness: none; consumers: orbit_lower_bound.
  Direct frozen dependencies:
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr sha256:69771b80b8b10adc24c953af3e8258a5ebe51d35c4cfc4d8028ec2d34262adf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.add sha256:4e9edab25a615edb43cd13e32ad18b18b2d560c9b53d18242ef0700a24eea4de
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.eval sha256:9867c01aa7794127f4c5fbefc7b6ac71e0b3449100ab24051ebf7c5179654cf4
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.leaves sha256:021be95ca29bae7bb0d05daefe11a481032440a597ba0cfafda410c77913ba89
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.mul sha256:aa1e620f45aac38f6497aad7b8fba43cab607efe9873fbeed1e5f32222b3eede
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.rec sha256:7f480031c4db7b1b1088ede9794220c6a7c682d5167132d53379a246fc1c60ff
    D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr.x sha256:9cf39ae230ef233ea94f6ec839b52acd9610b2ffc1d11d551d39db7d0f76b054
-/

import D5.S3.Arith.Congruence.KumarPengTranModularComplexity

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.Congruence.ZhangLComplexityEventualStability
open D5.S3.Arith.Congruence.KumarPengTranModularComplexity

def value (l : ℕ) : Expr → ℕ
  | .x => l
  | .add e f => value l e + value l f
  | .mul e f => value l e * value l f

/-- `‖n‖_l`: the least number of `l`'s in an expression with value `n`. -/
noncomputable def complexity (l n : ℕ) : ℕ :=
  sInf {k | ∃ e : Expr, e.leaves = k ∧ value l e = n}

/-- `A_l = {n ∈ lℤ⁺ : ‖l^m · n‖_l = m + ‖n‖_l for all m ≥ 0}`. -/
def A (l : ℕ) : Set ℕ :=
  {n | 0 < n ∧ l ∣ n ∧ ∀ m : ℕ, complexity l (l ^ m * n) = m + complexity l n}

def claim : Prop :=
  ∀ l : ℕ, 1 < l → ∀ n : ℕ, 0 < n → l ∣ n → ∃ m₀ : ℕ, l ^ m₀ * n ∈ A l

private theorem mem_A_iff (l n : ℕ) : n ∈ A l ↔
    0 < n ∧ l ∣ n ∧ ∀ m : ℕ,
      KumarPengTranModularComplexity.complexity (l : ZMod 0) ((l ^ m * n : ℕ) : ZMod 0) =
        m + KumarPengTranModularComplexity.complexity (l : ZMod 0) (n : ZMod 0) := by
  let v : Expr → ℕ := value l
  let c : ℕ → ℕ := fun n => sInf {k | ∃ e : Expr, e.leaves = k ∧ v e = n}
  have hcast (e : Expr) : (Nat.cast (v e) : ZMod 0) = e.eval (l : ZMod 0) := by
    induction e with
    | x => rfl
    | add e f he hf =>
      change (Nat.cast (v e + v f) : ZMod 0) = e.eval (l : ZMod 0) + f.eval (l : ZMod 0)
      rw [Nat.cast_add, he, hf]
    | mul e f he hf =>
      change (Nat.cast (v e * v f) : ZMod 0) = e.eval (l : ZMod 0) * f.eval (l : ZMod 0)
      rw [Nat.cast_mul, he, hf]
  have hc (u : ℕ) : c u = KumarPengTranModularComplexity.complexity (l : ZMod 0) (u : ZMod 0) := by
    change sInf {k | ∃ e : Expr, e.leaves = k ∧ v e = u} =
      sInf {k | ∃ e : Expr, e.leaves = k ∧ e.eval (l : ZMod 0) = (u : ZMod 0)}
    apply congrArg sInf
    ext k
    constructor
    · rintro ⟨e, he, hv⟩
      exact ⟨e, he, (hcast e).symm.trans (congrArg (fun u : ℕ => (u : ZMod 0)) hv)⟩
    · rintro ⟨e, he, hv⟩
      have h : Int.ofNat (v e) = (u : ℤ) := (hcast e).trans hv
      exact ⟨e, he, Int.ofNat.inj h⟩
  change (0 < n ∧ l ∣ n ∧ ∀ m : ℕ, c (l ^ m * n) = m + c n) ↔ _
  simp only [hc]

private theorem exists_value (l n : ℕ) (hn : 0 < n) (hd : l ∣ n) :
    ∃ e : Expr, e.eval (l : ZMod 0) = (n : ZMod 0) := by
  have hex (k : ℕ) : ∃ e : Expr, e.eval (l : ZMod 0) = ((l * (k + 1) : ℕ) : ZMod 0) := by
    induction k with
    | zero => exact ⟨.x, by simp [Expr.eval]⟩
    | succ k ih =>
      obtain ⟨e, he⟩ := ih
      exact ⟨.add e .x, by simp [Expr.eval, he, Nat.mul_succ]⟩
  obtain ⟨k, rfl⟩ := hd
  cases k with
  | zero => simp at hn
  | succ k => exact hex k

private theorem complexity_attained (l n : ℕ) (hn : 0 < n) (hd : l ∣ n) :
    ∃ e : Expr, e.leaves = KumarPengTranModularComplexity.complexity (l : ZMod 0) (n : ZMod 0) ∧
      e.eval (l : ZMod 0) = (n : ZMod 0) := by
  obtain ⟨e, he⟩ := exists_value l n hn hd
  exact Nat.sInf_mem (s := {k | ∃ e : Expr, e.leaves = k ∧ e.eval (l : ZMod 0) = (n : ZMod 0)})
    ⟨e.leaves, e, rfl, he⟩

private theorem value_bounds (l : ℕ) (hl : 1 < l) (e : Expr) :
    (l : ℤ) ≤ (show ℤ from e.eval (l : ZMod 0)) ∧ (show ℤ from e.eval (l : ZMod 0)) ≤ (l : ℤ) ^ e.leaves := by
  induction e with
  | x => simp [Expr.eval, Expr.leaves]
  | add e f he hf =>
    change (l : ℤ) ≤ (show ℤ from e.eval (l : ZMod 0)) + (show ℤ from f.eval (l : ZMod 0)) ∧
      (show ℤ from e.eval (l : ZMod 0)) + (show ℤ from f.eval (l : ZMod 0)) ≤ (l : ℤ) ^ (e.leaves + f.leaves)
    constructor
    · exact he.1.trans (le_add_of_nonneg_right (by omega))
    · rw [pow_add]
      exact (add_le_mul (by omega) (by omega)).trans
        (mul_le_mul he.2 hf.2 (by omega) (pow_nonneg (by omega) _))
  | mul e f he hf =>
    change (l : ℤ) ≤ (show ℤ from e.eval (l : ZMod 0)) * (show ℤ from f.eval (l : ZMod 0)) ∧
      (show ℤ from e.eval (l : ZMod 0)) * (show ℤ from f.eval (l : ZMod 0)) ≤ (l : ℤ) ^ (e.leaves + f.leaves)
    constructor
    · exact he.1.trans (le_mul_of_one_le_right (by omega) (by omega))
    · rw [pow_add]
      exact mul_le_mul he.2 hf.2 (by omega) (pow_nonneg (by omega) _)

private theorem complexity_mul_le (l n : ℕ) (hn : 0 < n) (hd : l ∣ n) :
    KumarPengTranModularComplexity.complexity (l : ZMod 0) ((l * n : ℕ) : ZMod 0) ≤
      KumarPengTranModularComplexity.complexity (l : ZMod 0) (n : ZMod 0) + 1 := by
  obtain ⟨e, he, hv⟩ := complexity_attained l n hn hd
  apply Nat.sInf_le
  exact ⟨.mul e .x, by simp [Expr.leaves, he], by simp [Expr.eval, hv, mul_comm]⟩

private theorem orbit_lower_bound (l n : ℕ) (hl : 1 < l) (hn : 0 < n) (hd : l ∣ n)
    (m : ℕ) : m + 1 ≤ KumarPengTranModularComplexity.complexity (l : ZMod 0) ((l ^ m * n : ℕ) : ZMod 0) := by
  have hnlow : l ≤ n := Nat.le_of_dvd hn hd
  have hp : 0 < l ^ m * n := Nat.mul_pos (pow_pos (by omega) _) hn
  have hdiv : l ∣ l ^ m * n := dvd_mul_of_dvd_right hd _
  obtain ⟨e, he, hv⟩ := complexity_attained l _ hp hdiv
  have hg := (value_bounds l hl e).2
  rw [hv, he] at hg
  have hgNat : l ^ m * n ≤ l ^ KumarPengTranModularComplexity.complexity (l : ZMod 0) ((l ^ m * n : ℕ) : ZMod 0) := by
    apply Int.ofNat_le.mp
    simpa only [Nat.cast_mul, Nat.cast_pow] using hg
  have hh : l ^ (m + 1) ≤ l ^ KumarPengTranModularComplexity.complexity (l : ZMod 0) ((l ^ m * n : ℕ) : ZMod 0) := by
    calc
      l ^ (m + 1) = l ^ m * l := pow_succ l m
      _ ≤ l ^ m * n := Nat.mul_le_mul_left _ hnlow
      _ ≤ _ := hgNat
  exact (pow_le_pow_iff_right₀ hl).mp hh

private theorem defect_antitone (l n : ℕ) (hl : 1 < l) (hn : 0 < n) (hd : l ∣ n) :
    Antitone (fun m : ℕ => KumarPengTranModularComplexity.complexity (l : ZMod 0) ((l ^ m * n : ℕ) : ZMod 0) - m) := by
  apply antitone_nat_of_succ_le
  intro m
  have hp : 0 < l ^ m * n := Nat.mul_pos (pow_pos (by omega) _) hn
  have hdiv : l ∣ l ^ m * n := dvd_mul_of_dvd_right hd _
  have hh := complexity_mul_le l _ hp hdiv
  have hm : l ^ (m + 1) * n = l * (l ^ m * n) := by
    simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm]
  rw [← hm] at hh
  omega

private theorem defect_pos (l n : ℕ) (hl : 1 < l) (hn : 0 < n) (hd : l ∣ n) (m : ℕ) :
    1 ≤ KumarPengTranModularComplexity.complexity (l : ZMod 0) ((l ^ m * n : ℕ) : ZMod 0) - m := by
  have := orbit_lower_bound l n hl hn hd m
  omega

theorem result : claim := by
  intro l hl n hn hd
  let d : ℕ → ℕ := fun m => KumarPengTranModularComplexity.complexity (l : ZMod 0) ((l ^ m * n : ℕ) : ZMod 0) - m
  have hdanti : Antitone d := defect_antitone l n hl hn hd
  obtain ⟨m₀, hm₀⟩ := WellFoundedLT.antitone_chain_condition hdanti
  refine ⟨m₀, (mem_A_iff l _).2 ⟨Nat.mul_pos (pow_pos (by omega) _) hn,
    dvd_mul_of_dvd_right hd _, ?_⟩⟩
  intro r
  have hconst : d (m₀ + r) = d m₀ := (hm₀ (m₀ + r) (by omega)).symm
  have hpos₀ := defect_pos l n hl hn hd m₀
  have hposr := defect_pos l n hl hn hd (m₀ + r)
  have hid : l ^ r * (l ^ m₀ * n) = l ^ (m₀ + r) * n := by
    simp [pow_add, Nat.mul_assoc, Nat.mul_comm]
  rw [hid]
  dsimp [d] at hconst
  omega

end D5.S3.Arith.Congruence.ZhangLComplexityEventualStability
