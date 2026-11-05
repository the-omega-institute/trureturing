/- GID: D5/S3/Quantum/ResolvedCountWeakValue
   generality: I
   mirror-B: D5/B/S3/Quantum/ResolvedCountWeakValue
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The resolved-count coherent-state weak-value identity. -/
/-
admission_basis: open-problem-resolution (#17772; Proved)
Direct frozen dependencies use declaration identities from the merged baseline report.
inputAmplitude_smul: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none.
  Consumers: ResolvedCountWeakValue.M4, ResolvedCountWeakValue.inputAmplitude_mul, ResolvedCountWeakValue.insertion_ratio_scaling.
weighted_exp_hasSum: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none.
  Consumers: ResolvedCountWeakValue.numberExponential_inner;
    KummerModulusLowerBound.Result.second_exp_hasSum; KummerModulusLowerBound.Result.complex_closed.
numberExponential_inner: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.createdSingle_inner.
createdSingle_inner: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.created_inner.
mul_createdSingle: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.number_coherent_created.
createdSingle_apply: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.exponential_created_resolved.
created_inner: proof_shape: content; escape_witness: created_inner.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.exponential_created_inner, ResolvedCountWeakValue.gamma_created.
gamma_created: proof_shape: content; escape_witness: PassiveFockModel.exponential_total.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.M1.
created_zero: proof_shape: content; escape_witness: created_zero.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.number_coherent_created.
number_coherent_created: proof_shape: content; escape_witness: created_zero.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.M1.
M1: proof_shape: content; escape_witness: PassiveFockModel.exponential_total.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.coherent_number_numerator.
onePhoton_zero: proof_shape: content; escape_witness: onePhoton_zero.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.onePhoton_inputAmplitude.
tail_inputAmplitude: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none.
  Consumers: ResolvedCountWeakValue.number_coherent_created, ResolvedCountWeakValue.onePhoton_inputAmplitude.
onePhoton_inputAmplitude: proof_shape: content; escape_witness: onePhoton_zero.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.number_onePhoton.
number_onePhoton: proof_shape: content; escape_witness: onePhoton_zero.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.M3.
singleFinal_eq: proof_shape: content; escape_witness: PassiveFockModel.exponential_total.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.singleProbability_ne_zero_iff.
singleProbability_ne_zero_iff: proof_shape: content; escape_witness: PassiveFockModel.exponential_total.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.result, ResolvedCountWeakValue.M3, ResolvedCountWeakValue.M4.
M3: proof_shape: content; escape_witness: PassiveFockModel.exponential_total.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.result.
exponential_created_inner: proof_shape: content; escape_witness: created_inner.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.exponential_created_resolved.
exponential_created_resolved: proof_shape: content; escape_witness: created_inner.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.coherent_number_numerator.
coherent_number_numerator: proof_shape: content; escape_witness: created_inner.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.M2.
M2: proof_shape: content; escape_witness: created_inner.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.result.
exponential_ne_zero: proof_shape: content; escape_witness: PassiveFockModel.exponential_inner.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.resolved_coherent_ne_zero_iff, ResolvedCountWeakValue.singleProbability_ne_zero_iff.
coherentFinal_eq: proof_shape: content; escape_witness: PassiveFockModel.exponential_total.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.coherentProbability_ne_zero_iff.
resolved_coherent_ne_zero_iff: proof_shape: content; escape_witness: PassiveFockModel.exponential_inner.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.coherentProbability_ne_zero_iff.
coherentProbability_ne_zero_iff: proof_shape: content; escape_witness: PassiveFockModel.exponential_inner.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.result, ResolvedCountWeakValue.M4.
M4: proof_shape: content; escape_witness: PassiveFockModel.exponential_inner.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: ResolvedCountWeakValue.result.
inputAmplitude_mul: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none.
  Consumers: ResolvedCountWeakValue.insertion_ratio_scaling.
insertion_ratio_scaling: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none.
  Consumers: ResolvedCountWeakValue.result.
result: proof_shape: content; escape_witness: created_inner.
  Direct frozen dependencies: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject sha256:39eb7f33890ab484cd80f4c337cf9f69000cc10b250aee4e7254568b2ecb208d; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.carrier sha256:51e2312a9194513a3488a635ca97c4da7d93d56b5a114cc6a62c8f9dca1b74ba; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.complete sha256:26caa7b1a91b12394c829b82a8eb30c89c3cd3a52d9abafdc344c45ba7fa6569; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.innerProduct sha256:9d8d79026655bb8ba6d67dbc52fe269a1f0c22824c56284fce630ebeb3d6c2b4; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.mk sha256:7c13e01a41bc690e53a9a3493ef74385c0ce41afc0f546a44b61de53f4d45b0a; D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject.normed sha256:8db2feee9e17068bc5aeab2b971e916ad9a46404a879f9cd6902e0c3bcda085c; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: none.
The public claim contains every count and each nonzero-probability condition of #17772.
The four-slot escape audit is unfinished: https://github.com/the-omega-institute/trureturing/issues/18878.
-/

import D5.S3.Quantum.PassiveFockModel


noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace D5.S3.Quantum.ResolvedCountWeakValue
open D5.S3.Quantum.PassiveFockModel
open D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter (exponentialCoeff exponentialVector)

private lemma inputAmplitude_smul (k : ℕ) (α : ℂ) :
    (EuclideanSpace.single (0 : Fin (k+1))) α = α • (EuclideanSpace.single (0 : Fin (k+1))) 1 := by
  apply PiLp.ext
  change ∀ i : Fin (k+1), Pi.single (M := fun _ : Fin (k+1) => ℂ) 0 α i =
    (α • Pi.single (M := fun _ : Fin (k+1) => ℂ) 0 (1 : ℂ)) i
  exact congrFun (by simpa only [smul_eq_mul, mul_one] using
    (Pi.single_smul (f := fun _ : Fin (k+1) => ℂ) (0 : Fin (k+1)) α (1 : ℂ)))

lemma weighted_exp_hasSum (t : ℂ) :
    HasSum (fun n : ℕ => (n : ℂ) * t ^ n / (n.factorial : ℂ))
      (t * Complex.exp t) := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, zero_div, sub_zero, Complex.exp_eq_exp_ℂ]
  apply HasSum.congr_fun ((NormedSpace.expSeries_div_hasSum_exp t).mul_left t)
  intro n
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ, Complex.exp_eq_exp_ℂ]
  have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  field_simp
  <;> ring

private lemma numberExponential_inner (α β : ℂ) :
    inner ℂ (numberExponential α) (exponentialVector β) =
      ((starRingEnd ℂ) α * β) * Complex.exp ((starRingEnd ℂ) α * β) := by
  rw [lp.inner_eq_tsum]
  convert (weighted_exp_hasSum ((starRingEnd ℂ) α * β)).tsum_eq using 1
  apply tsum_congr
  intro n
  change inner ℂ ((n : ℂ) * exponentialCoeff α n) (exponentialCoeff β n) = _
  rw [← smul_eq_mul, inner_smul_left, single_exponentialCoeff_inner]
  simp only [map_natCast]
  ring

private def createdSingle (α : ℂ) : lp (fun _ : ℕ => ℂ) 2 :=
  if α = 0 then lp.single 2 1 1 else α⁻¹ • numberExponential α

private lemma createdSingle_inner (α β : ℂ) :
    inner ℂ (createdSingle α) (exponentialVector β) =
      β * Complex.exp ((starRingEnd ℂ) α * β) := by
  by_cases h : α = 0
  · subst α
    simp [createdSingle, lp.inner_single_left, exponentialVector, exponentialCoeff,
      RCLike.inner_apply]
  · simp only [createdSingle, if_neg h, inner_smul_left, numberExponential_inner,
      map_inv₀]
    have hc : (starRingEnd ℂ) α ≠ 0 := (map_ne_zero _).mpr h
    field_simp

private lemma mul_createdSingle (α : ℂ) : α • createdSingle α = numberExponential α := by
  by_cases h : α = 0
  · subst α
    apply lp.ext
    funext n
    by_cases hn : n = 0
    · subst n; simp [numberExponential]
    · simp [numberExponential, exponentialCoeff, hn]
  · simp [createdSingle, h, smul_smul]

private lemma createdSingle_apply (α : ℂ) (h : α ≠ 0) (m : ℕ) :
    createdSingle α m = (m : ℂ) / α * exponentialCoeff α m := by
  simp only [createdSingle, if_neg h]
  change α⁻¹ * ((m : ℂ) * exponentialCoeff α m) = _
  ring

private def created : (k : ℕ) → EuclideanSpace ℂ (Fin k) → EuclideanSpace ℂ (Fin k) → Fock k
  | 0, _, _ => 0
  | k+1, β, v => headTensor (createdSingle (β 0)) ((v 0) • exponential k (tail β)) +
      headTensor (exponentialVector (β 0)) (created k (tail β) (tail v))

private lemma created_inner (k : ℕ) (β v δ : EuclideanSpace ℂ (Fin k)) :
    inner ℂ (created k β v) (exponential k δ) =
      inner ℂ v δ * Complex.exp (inner ℂ β δ) := by
  induction k with
  | zero => simp [created, PiLp.inner_apply]
  | succ k ih =>
    rw [created, exponential, inner_add_left, headTensor_inner, headTensor_inner,
      createdSingle_inner, inner_smul_left, exponential_inner, single_exponential_inner, ih]
    simp only [PiLp.inner_apply, Fin.sum_univ_succ, tail, Fin.tail, RCLike.inner_apply,
      WithLp.ofLp_toLp, Complex.exp_add]
    ring

private lemma gamma_created {k : ℕ} (B : (EuclideanSpace ℂ (Fin k) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin k))) (β v : EuclideanSpace ℂ (Fin k)) :
    gamma B (created k β v) = created k (B β) (B v) := by
  apply sub_eq_zero.mp
  apply exponential_total k
  intro δ
  rw [inner_sub_left, (gamma B).inner_map_eq_flip]
  have he : (gamma B).symm (exponential k δ) = exponential k (B.symm δ) := by
    apply (gamma B).injective
    simp [gamma_exponential]
  rw [he, created_inner, created_inner]
  have hβ := B.inner_map_map β (B.symm δ)
  have hv := B.inner_map_map v (B.symm δ)
  simp only [B.apply_symm_apply] at hβ hv
  rw [hβ, hv, sub_self]

private lemma created_zero (k : ℕ) (β : EuclideanSpace ℂ (Fin k)) : created k β 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    apply lp.ext
    funext n
    change createdSingle (β 0) n • ((0 : ℂ) • exponential k (tail β)) +
      exponentialVector (β 0) n • created k (tail β) 0 = 0
    rw [ih]
    simp

private lemma tail_inputAmplitude (k : ℕ) (α : ℂ) : tail ((EuclideanSpace.single (0 : Fin (k+1))) α) = 0 := by
  exact PiLp.ext (congrFun rfl)

private lemma number_coherent_created {k : ℕ} (β : EuclideanSpace ℂ (Fin (k+1)))
    (h : NumberDomain (coherent (k+1) β)) :
    number (coherent (k+1) β) h =
      (Real.exp (-‖β‖ ^ 2 / 2) : ℂ) •
        created (k+1) β ((EuclideanSpace.single (0 : Fin (k+1))) (β 0)) := by
  have ht : tail ((EuclideanSpace.single (0 : Fin (k+1))) (β 0)) = 0 := by
    exact tail_inputAmplitude k (β 0)
  have hz : (EuclideanSpace.single (0 : Fin (k+1))) (β 0) 0 = β 0 := rfl
  rw [created, ht, created_zero, headTensor]
  apply lp.ext
  funext n
  change (n : ℂ) • ((Real.exp (-‖β‖ ^ 2 / 2) : ℂ) •
      (exponentialCoeff (β 0) n • exponential k (tail β))) =
    (Real.exp (-‖β‖ ^ 2 / 2) : ℂ) •
      (createdSingle (β 0) n • (((EuclideanSpace.single (0 : Fin (k+1))) (β 0) 0) • exponential k (tail β)) +
      (exponentialVector (β 0) n • (0 : Fock k)))
  rw [hz, smul_zero, add_zero]
  have hc := congrArg (fun u : lp (fun _ : ℕ => ℂ) 2 => u n)
    (mul_createdSingle (β 0))
  change β 0 * createdSingle (β 0) n = (n : ℂ) * exponentialCoeff (β 0) n at hc
  simp only [smul_smul]
  congr 1
  rw [mul_left_comm, mul_comm (createdSingle (β 0) n), hc]

/-- M1: propagation of the genuine number insertion, characterized by exponential kernels. -/
private lemma M1 {k : ℕ} (B : (EuclideanSpace ℂ (Fin (k+1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (k+1)))) (β : EuclideanSpace ℂ (Fin (k+1)))
    (h : NumberDomain (coherent (k+1) β)) :
    gamma B (number (coherent (k+1) β) h) =
      (Real.exp (-‖β‖ ^ 2 / 2) : ℂ) •
        created (k+1) (B β) (B ((EuclideanSpace.single (0 : Fin (k+1))) (β 0))) := by
  rw [number_coherent_created, map_smul, gamma_created]
end D5.S3.Quantum.ResolvedCountWeakValue
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace D5.S3.Quantum.ResolvedCountWeakValue
open D5.S3.Quantum.PassiveFockModel

private lemma onePhoton_zero (k : ℕ) : onePhoton k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (lp.single 2 1 ((0 : ℂ) • vacuum k) : Fock (k+1)) +
      lp.single 2 0 (onePhoton k 0) = 0
    rw [ih]
    simp

private lemma onePhoton_inputAmplitude (k : ℕ) (α : ℂ) :
    onePhoton (k+1) ((EuclideanSpace.single (0 : Fin (k+1))) α) = lp.single 2 1 (α • vacuum k) := by
  rw [onePhoton, tail_inputAmplitude, onePhoton_zero]
  simp [EuclideanSpace.single]

private lemma number_onePhoton {k : ℕ} (β : EuclideanSpace ℂ (Fin (k+1)))
    (h : NumberDomain (onePhoton (k+1) β)) :
    number (onePhoton (k+1) β) h =
      onePhoton (k+1) ((EuclideanSpace.single (0 : Fin (k+1))) (β 0)) := by
  rw [onePhoton_inputAmplitude]
  apply lp.ext
  funext n
  change (n : ℂ) •
      ((lp.single 2 1 ((β 0) • vacuum k) : lp (fun _ : ℕ => Fock k) 2) n +
        (lp.single 2 0 (onePhoton k (tail β)) : lp (fun _ : ℕ => Fock k) 2) n) = _
  by_cases h1 : n = 1
  · subst n; simp [onePhoton, lp.single_apply, Pi.single_apply]
  · by_cases h0 : n = 0
    · subst n; simp [onePhoton, lp.single_apply, Pi.single_apply]
    · simp [onePhoton, lp.single_apply, Pi.single_apply, h1, h0]

private lemma singleFinal_eq {k : ℕ} (A B : (EuclideanSpace ℂ (Fin (k+1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (k+1)))) :
    singleFinal A B = onePhoton (k+1) (B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1))) := by
  unfold singleFinal singleInput
  rw [gamma_onePhoton, gamma_onePhoton]

private lemma exponential_ne_zero (k : ℕ) (β : EuclideanSpace ℂ (Fin k)) : exponential k β ≠ 0 := by
  intro h
  have hi := exponential_inner k β β
  rw [h, inner_zero_left] at hi
  exact Complex.exp_ne_zero _ hi.symm

private lemma singleProbability_ne_zero_iff {k : ℕ} (A B : (EuclideanSpace ℂ (Fin (k+1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (k+1)))) :
    singleProbability A B 1 ≠ 0 ↔ B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0 ≠ 0 := by
  have hv : vacuum k ≠ 0 := by
    unfold vacuum
    exact exponential_ne_zero k (0 : EuclideanSpace ℂ (Fin k))
  simp only [singleProbability, resolvedProbability, singleFinal_eq]
  change ‖(lp.single 2 1 ((B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0) • vacuum k) :
      lp (fun _ : ℕ => Fock k) 2) 1 +
    (lp.single 2 0 (onePhoton k (tail (B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1))))) :
      lp (fun _ : ℕ => Fock k) 2) 1‖ ^ 2 ≠ 0 ↔ _
  simp [onePhoton, lp.single_apply, Pi.single_apply, norm_smul, hv]

/-- M3: the single-photon weak value is the transition-amplitude ratio. -/
private lemma M3 {k : ℕ} (A B : (EuclideanSpace ℂ (Fin (k+1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (k+1))))
    (h1 : singleProbability A B 1 ≠ 0) :
    singleWeakValue A B 1 h1 =
      B ((EuclideanSpace.single (0 : Fin (k+1))) (A ((EuclideanSpace.single (0 : Fin (k+1))) 1) 0)) 0 /
        B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0 := by
  have hd := (singleProbability_ne_zero_iff A B).mp h1
  have hdc : (starRingEnd ℂ) (B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0) ≠ 0 :=
    (map_ne_zero _).mpr hd
  have hdom := singleProbeDomain A
  change NumberDomain (gamma A (onePhoton (k+1) ((EuclideanSpace.single (0 : Fin (k+1))) 1))) at hdom
  rw [gamma_onePhoton] at hdom
  have hn : number (gamma A (singleInput k)) (singleProbeDomain A) =
      onePhoton (k+1) ((EuclideanSpace.single (0 : Fin (k+1))) (A ((EuclideanSpace.single (0 : Fin (k+1))) 1) 0)) := by
    convert number_onePhoton (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) hdom using 1
    congr 1
    exact gamma_onePhoton _ _
  unfold singleWeakValue generalizedWeakValue effectWeight
  rw [hn, gamma_onePhoton]
  simp only [singleInput, gamma_onePhoton A ((EuclideanSpace.single (0 : Fin (k+1))) 1),
    gamma_onePhoton B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1))]
  change inner ℂ (onePhoton (k+1) (B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1))))
    (lp.single 2 1 (onePhoton (k+1)
      (B ((EuclideanSpace.single (0 : Fin (k+1))) (A ((EuclideanSpace.single (0 : Fin (k+1))) 1) 0))) 1)) /
    inner ℂ (onePhoton (k+1) (B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1))))
      (lp.single 2 1 (onePhoton (k+1) (B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1))) 1)) = _
  rw [lp.inner_single_right, lp.inner_single_right]
  change inner ℂ
    ((lp.single 2 1 ((B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0) • vacuum k) :
        lp (fun _ : ℕ => Fock k) 2) 1 +
      (lp.single 2 0 (onePhoton k (tail (B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1))))) :
        lp (fun _ : ℕ => Fock k) 2) 1)
    ((lp.single 2 1 ((B ((EuclideanSpace.single (0 : Fin (k+1))) (A ((EuclideanSpace.single (0 : Fin (k+1))) 1) 0)) 0) • vacuum k) :
        lp (fun _ : ℕ => Fock k) 2) 1 +
      (lp.single 2 0 (onePhoton k (tail (B ((EuclideanSpace.single (0 : Fin (k+1))) (A ((EuclideanSpace.single (0 : Fin (k+1))) 1) 0))))) :
        lp (fun _ : ℕ => Fock k) 2) 1) /
    inner ℂ
      ((lp.single 2 1 ((B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0) • vacuum k) :
          lp (fun _ : ℕ => Fock k) 2) 1 +
        (lp.single 2 0 (onePhoton k (tail (B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1))))) :
          lp (fun _ : ℕ => Fock k) 2) 1)
      ((lp.single 2 1 ((B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0) • vacuum k) :
          lp (fun _ : ℕ => Fock k) 2) 1 +
        (lp.single 2 0 (onePhoton k (tail (B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1))))) :
          lp (fun _ : ℕ => Fock k) 2) 1) = _
  simp only [onePhoton, lp.single_apply, Pi.single_apply,
    ite_true, Nat.one_ne_zero, ite_false, add_zero,
    inner_smul_left, inner_smul_right]
  have hvv : inner ℂ (vacuum k) (vacuum k) = 1 := vacuum_exponential_inner k 0
  rw [hvv]
  field_simp
end D5.S3.Quantum.ResolvedCountWeakValue
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace D5.S3.Quantum.ResolvedCountWeakValue
open D5.S3.Quantum.PassiveFockModel
open D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter (exponentialCoeff exponentialVector)

private lemma exponential_created_inner (k : ℕ) (β v : EuclideanSpace ℂ (Fin k)) :
    inner ℂ (exponential k β) (created k β v) =
      inner ℂ β v * Complex.exp (inner ℂ β β) := by
  rw [← inner_conj_symm, created_inner]
  simp only [map_mul, ← Complex.exp_conj, inner_conj_symm]

private lemma exponential_created_resolved {k : ℕ} (γ v : EuclideanSpace ℂ (Fin (k+1))) (m : ℕ)
    (hd : γ 0 ≠ 0) :
    inner ℂ (exponential (k+1) γ) (numberProjector m (created (k+1) γ v)) =
      inner ℂ (exponential (k+1) γ) (numberProjector m (exponential (k+1) γ)) *
        ((m : ℂ) * v 0 / γ 0 + inner ℂ (tail γ) (tail v)) := by
  change inner ℂ (exponential (k+1) γ) (lp.single 2 m (created (k+1) γ v m)) =
    inner ℂ (exponential (k+1) γ) (lp.single 2 m (exponential (k+1) γ m)) * _
  rw [lp.inner_single_right, lp.inner_single_right]
  change inner ℂ (exponentialCoeff (γ 0) m • exponential k (tail γ))
    (createdSingle (γ 0) m • ((v 0) • exponential k (tail γ)) +
      exponentialCoeff (γ 0) m • created k (tail γ) (tail v)) =
    inner ℂ (exponentialCoeff (γ 0) m • exponential k (tail γ))
      (exponentialCoeff (γ 0) m • exponential k (tail γ)) * _
  rw [createdSingle_apply _ hd, inner_add_right, inner_smul_left,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
    inner_smul_right, inner_smul_right, exponential_inner, exponential_created_inner]
  ring

private lemma coherent_number_numerator {k : ℕ} (B : (EuclideanSpace ℂ (Fin (k+1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (k+1)))) (β : EuclideanSpace ℂ (Fin (k+1)))
    (h : NumberDomain (coherent (k+1) β)) (m : ℕ) (hd : B β 0 ≠ 0) :
    inner ℂ (gamma B (coherent (k+1) β))
      (numberProjector m (gamma B (number (coherent (k+1) β) h))) =
    inner ℂ (gamma B (coherent (k+1) β))
      (numberProjector m (gamma B (coherent (k+1) β))) *
      ((m : ℂ) * B ((EuclideanSpace.single (0 : Fin (k+1))) (β 0)) 0 / B β 0 +
        inner ℂ (tail (B β)) (tail (B ((EuclideanSpace.single (0 : Fin (k+1))) (β 0))))) := by
  rw [M1, gamma_coherent]
  simp only [coherent, B.norm_map, map_smul, inner_smul_left, inner_smul_right]
  rw [exponential_created_resolved _ _ m hd]
  ring

/-- M2: all-count evaluation after canceling the physical nonzero denominator. -/
private lemma M2 {k : ℕ} (A B : (EuclideanSpace ℂ (Fin (k+1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (k+1)))) (α : ℂ) (m : ℕ)
    (hm : coherentProbability A B α m ≠ 0)
    (hd : B (A ((EuclideanSpace.single (0 : Fin (k+1))) α)) 0 ≠ 0) :
    coherentWeakValue A B α m hm =
      (m : ℂ) * B ((EuclideanSpace.single (0 : Fin (k+1))) (A ((EuclideanSpace.single (0 : Fin (k+1))) α) 0)) 0 /
        B (A ((EuclideanSpace.single (0 : Fin (k+1))) α)) 0 +
      inner ℂ (tail (B (A ((EuclideanSpace.single (0 : Fin (k+1))) α))))
        (tail (B ((EuclideanSpace.single (0 : Fin (k+1))) (A ((EuclideanSpace.single (0 : Fin (k+1))) α) 0)))) := by
  unfold coherentWeakValue generalizedWeakValue
  have hdom := coherentProbeDomain A α
  change NumberDomain (gamma A (coherent (k+1) ((EuclideanSpace.single (0 : Fin (k+1))) α))) at hdom
  rw [gamma_coherent] at hdom
  have hn : number (gamma A (coherentInput k α)) (coherentProbeDomain A α) =
      number (coherent (k+1) (A ((EuclideanSpace.single (0 : Fin (k+1))) α))) hdom := by
    congr 1
    exact gamma_coherent _ _
  have hz : effectWeight (gamma A) (gamma B) (numberProjector m) (coherentInput k α) ≠ 0 := by
    rw [effectWeight, projector_weight]
    exact_mod_cast hm
  rw [hn]
  simp only [coherentInput, gamma_coherent A ((EuclideanSpace.single (0 : Fin (k+1))) α)]
  rw [coherent_number_numerator B _ hdom m hd]
  unfold effectWeight at hz ⊢
  simp only [coherentInput, gamma_coherent A ((EuclideanSpace.single (0 : Fin (k+1))) α),
    gamma_coherent B (A ((EuclideanSpace.single (0 : Fin (k+1))) α))] at hz ⊢
  exact mul_div_cancel_left₀ _ hz
end D5.S3.Quantum.ResolvedCountWeakValue
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace D5.S3.Quantum.ResolvedCountWeakValue
open D5.S3.Quantum.PassiveFockModel
open D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter (exponentialCoeff exponentialVector)

private lemma coherentFinal_eq {k : ℕ} (A B : (EuclideanSpace ℂ (Fin (k+1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (k+1)))) (α : ℂ) :
    coherentFinal A B α = coherent (k+1) (B (A ((EuclideanSpace.single (0 : Fin (k+1))) α))) := by
  unfold coherentFinal coherentInput
  rw [gamma_coherent, gamma_coherent]

private lemma resolved_coherent_ne_zero_iff {k : ℕ} (γ : EuclideanSpace ℂ (Fin (k+1))) (m : ℕ) :
    resolvedProbability m (coherent (k+1) γ) ≠ 0 ↔ γ 0 ≠ 0 ∨ m = 0 := by
  have hs : (Real.sqrt (m.factorial : ℝ) : ℂ) ≠ 0 := by
    norm_cast
    exact (Real.sqrt_pos.mpr (by positivity : 0 < (m.factorial : ℝ))).ne'
  change ‖(Real.exp (-‖γ‖ ^ 2 / 2) : ℂ) •
    (exponentialCoeff (γ 0) m • exponential k (tail γ))‖ ^ 2 ≠ 0 ↔ _
  simp [exponentialCoeff, norm_smul, hs, Real.exp_ne_zero, exponential_ne_zero,
    Nat.factorial_ne_zero, imp_iff_not_or]

private lemma coherentProbability_ne_zero_iff {k : ℕ} (A B : (EuclideanSpace ℂ (Fin (k+1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (k+1)))) (α : ℂ) (m : ℕ) :
    coherentProbability A B α m ≠ 0 ↔
      B (A ((EuclideanSpace.single (0 : Fin (k+1))) α)) 0 ≠ 0 ∨ m = 0 := by
  unfold coherentProbability
  rw [coherentFinal_eq, resolved_coherent_ne_zero_iff]

/-- M4: the zero-count denominator always exists, and positive resolved counts
certify the single-photon click denominator. -/
private lemma M4 {k : ℕ} (A B : (EuclideanSpace ℂ (Fin (k+1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (k+1)))) (α : ℂ) (m : ℕ)
    (hm : coherentProbability A B α m ≠ 0) :
    coherentProbability A B α 0 ≠ 0 ∧
      (m ≠ 0 → singleProbability A B 1 ≠ 0) := by
  constructor
  · exact (coherentProbability_ne_zero_iff A B α 0).mpr (Or.inr rfl)
  · intro hmn
    have hd := ((coherentProbability_ne_zero_iff A B α m).mp hm).resolve_right hmn
    apply (singleProbability_ne_zero_iff A B).mpr
    rw [inputAmplitude_smul k α, map_smul, map_smul] at hd
    change α * B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0 ≠ 0 at hd
    exact (mul_ne_zero_iff.mp hd).2
end D5.S3.Quantum.ResolvedCountWeakValue
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace D5.S3.Quantum.ResolvedCountWeakValue
open D5.S3.Quantum.PassiveFockModel

private lemma inputAmplitude_mul (k : ℕ) (α β : ℂ) :
    (EuclideanSpace.single (0 : Fin (k+1))) (α * β) = α • (EuclideanSpace.single (0 : Fin (k+1))) β := by
  rw [inputAmplitude_smul k (α * β), inputAmplitude_smul k β, smul_smul]

private lemma insertion_ratio_scaling {k : ℕ} (A B : (EuclideanSpace ℂ (Fin (k+1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (k+1)))) (α : ℂ)
    (ha : α ≠ 0) (hd : B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0 ≠ 0) :
    B ((EuclideanSpace.single (0 : Fin (k+1))) (A ((EuclideanSpace.single (0 : Fin (k+1))) α) 0)) 0 /
        B (A ((EuclideanSpace.single (0 : Fin (k+1))) α)) 0 =
      B ((EuclideanSpace.single (0 : Fin (k+1))) (A ((EuclideanSpace.single (0 : Fin (k+1))) 1) 0)) 0 /
        B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0 := by
  rw [inputAmplitude_smul k α, map_smul, map_smul]
  change B ((EuclideanSpace.single (0 : Fin (k+1))) (α * A ((EuclideanSpace.single (0 : Fin (k+1))) 1) 0)) 0 /
    (α * B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0) = _
  rw [inputAmplitude_mul, map_smul]
  change (α * B ((EuclideanSpace.single (0 : Fin (k+1))) (A ((EuclideanSpace.single (0 : Fin (k+1))) 1) 0)) 0) /
    (α * B (A ((EuclideanSpace.single (0 : Fin (k+1))) 1)) 0) = _
  field_simp

def claim : Prop :=
  ∀ (k : ℕ) (A B : (EuclideanSpace ℂ (Fin (k+1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (k+1)))) (α : ℂ), α ≠ 0 →
    ∀ (m : ℕ) (hₘ : coherentProbability A B α m ≠ 0),
      ∃ h₀ : coherentProbability A B α 0 ≠ 0,
        if m = 0 then
          coherentWeakValue A B α m hₘ - coherentWeakValue A B α 0 h₀ = 0
        else
          ∃ h₁ : singleProbability A B 1 ≠ 0,
            coherentWeakValue A B α m hₘ - coherentWeakValue A B α 0 h₀ =
              (m : ℂ) * singleWeakValue A B 1 h₁



/-- The resolved-count identity, including all denominator clauses. -/
theorem result : claim := by
  intro k A B α ha m hm
  obtain ⟨h0, hpos⟩ := M4 A B α m hm
  refine ⟨h0, ?_⟩
  by_cases hmn : m = 0
  · subst m
    simp
  · rw [if_neg hmn]
    have h1 := hpos hmn
    refine ⟨h1, ?_⟩
    have hd := ((coherentProbability_ne_zero_iff A B α m).mp hm).resolve_right hmn
    rw [M2 A B α m hm hd, M2 A B α 0 h0 hd, M3 A B h1]
    simp only [Nat.cast_zero, zero_mul, zero_div, zero_add, add_sub_cancel_right]
    rw [mul_div_assoc, insertion_ratio_scaling A B α ha
      ((singleProbability_ne_zero_iff A B).mp h1)]

end D5.S3.Quantum.ResolvedCountWeakValue
