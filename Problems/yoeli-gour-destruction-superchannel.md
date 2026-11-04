---
slug: yoeli-gour-destruction-superchannel
bibkey: yoeligour2026instability
doi: 10.48550/arXiv.2602.18323
url: https://arxiv.org/abs/2602.18323v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.result
---

# Destruction covariance need not be a superchannel fixed set

## Problem

Goni Yoeli and Gilad Gour, *Instability as a Quantum Resource*, arXiv:2602.18323v1, Open directions, PDF page 5 after Eq. (29), ask:

> Moreover, a key open question is whether destruction-covariant channels themselves arise as fixed points of an idempotent superchannel.

The affirmative universal assertion quantifies over positive finite dimensions $a,b$ and admissible destruction channels $\Delta_A,\Delta_B$. Admissibility means CPTP, idempotent, and fixing a positive definite density matrix of trace one. It asks for a deterministic complex-linear superchannel $\Theta$ on the entire channel-map space, idempotent there, such that every CPTP $N$ satisfies $\Theta(N)=N$ if and only if $N\circ\Delta_A=\Delta_B\circ N$.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Finite-dimensional nonzero systems | Positive natural dimensions in `claim` | Input and output dimensions separately quantified |
| Channel means CPTP | Existing `EntanglementAssistedCommunicationValue.IsChannel` | No alternative channel predicate |
| Idempotent destruction channel fixing a full-rank state | `IsDestruction` | CPTP, composition equality, positive definite trace-one fixed state |
| Eq. (1), destruction covariance | Composition equality written literally in `claim` | No duplicate covariance definition |
| Deterministic superchannel | Existing `DalySuperchannelMinimalExtension.IsQuantumSuperchannel` | Complete CP preservation with arbitrary auxiliaries and TP preservation |
| Idempotent superchannel | Global linear-map composition equality | No restriction to states or channels |
| Channels themselves arise as fixed points | Equivalence for every CPTP $N$ | Exact fixed set within CPTP maps |
| Negative answer | `YoeliGourDestructionSuperchannelRefutation.result` | Refutes the universal assertion using $a=b=3$ |

## Motivation

An idempotent map can select a distinguished set of objects. The question asks whether the free dynamical objects defined by destruction covariance admit a physical selector at the superchannel level. The distinction from Eq. (29) is substantive: pre/post-dephasing selects classical channels, whereas covariance includes all channels commuting with dephasing.

## Gap

The universal assertion is refuted by the equal-dimension qutrit instance. Arbitrary destruction maps, unequal dimensions, and a dimension-uniform Lean obstruction for all $d\ge3$ remain outside this result.

## Route

Use the existing complete-dephasing owner `PostprocessedImprovementUnfaithful.dephase`. The private facts `dephase_channel`, `dephase_idem`, and `faithful_fixed` establish its admissibility at dimension three. The depolarizing channel has Choi matrix $I/3$ and commutes with dephasing. Fixing it makes the induced CP Choi map unital. Sixteen normalized Choi vectors of monomial-unitary channels span $\mathbb C^9$ and have connected nonzero-overlap graph (`v_normalized`, `spanning`, `connected`).

The proof applies `ProbeComponentRigidity.connected_probability_preserving_identity`, the CP Kraus representation, and Choi transport to establish `fixes_dio_identity`. The rational unitary with $2\times2$ block $\left(\begin{smallmatrix}3/5&-4/5\\4/5&3/5\end{smallmatrix}\right)$ yields a CPTP channel that does not commute with dephasing (`R_unitary`, `R_not_covariant`). Identity fixes this channel, contradicting exactness in `result`. All these auxiliary declarations are private in the settling module.

## Falsifier

A deterministic qutrit superchannel with exactly the dephasing-covariant CPTP fixed maps would contradict the kernel-checked negation. A change from exact fixed-set equality to containment or from physical deterministic superchannels to arbitrary linear projectors changes the question.

## Evidence

The settling declaration is `D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.result : ¬ claim`. Its admission basis is `open-problem-resolution (#24013; Refuted)`; the source and ordinary argument are preregistered in [#24013](https://github.com/the-omega-institute/trureturing/issues/24013).

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The six published owner declarations have unfinished four-slot escape audits in [#25799](https://github.com/the-omega-institute/trureturing/issues/25799). No Reg mirror or validated registration is claimed for them. They are `CoherenceBreakingAmendment.monomial_unitary`, `CoherenceBreakingAmendment.monomial_projection`, `ProductUnitaryChoiSpectrum.depol_single_eq_dmat`, `ChannelTimeReversalNoGo.unitaryChannel_cptp`, `DalySuperchannelMinimalExtension.choi_induced_apply`, and `DalySuperchannelMinimalExtension.preserving_cp_induced`.

### Exact finite experiment

The experiment is [the pinned report directory](https://github.com/the-omega-institute/trureturing-experiments/tree/b44213ea6ad71c525c5482eed0f6bf87ffc99db7/docs/reports/yoeli-gour-destruction-superchannel). Program: `check.py`; SHA-256 `3c78372a0bf35b7b8ac9c17fca121bad2fa7319a5f1c0aa04e98093a84068c61`. Command: `python3 /Users/auric/trureturing-experiments/docs/reports/yoeli-gour-destruction-superchannel/check.py`; exit 0, final result `ALL_CHECKS_OK`. The executed program equals the blob at commit `b44213ea6ad71c525c5482eed0f6bf87ffc99db7`.

At $d=1,2,3$, the checker verifies dephaser CPTP, idempotence and a full-rank fixed state, Eq. (29) as complete Choi dephasing, identity covariance, and the depolarizing Choi matrix $I/d$. At $d=2,3,4$, its monomial families have respectively $6,24,120$ vectors, spans $4,9,16$, and overlap component sizes $[3,3]$, $[24]$, $[120]$. The exact commutator ranks are $14$ of $16$ at $d=2$ and $80$ of $81$ at $d=3$. It verifies the physical qubit involution twirl and exact DIO fixed space. At $d=3$, the Choi quadratic form of $2\Delta-\mathrm{id}$ on $\operatorname{vec}(I)$ is $-3$, excluding complete positivity of that attempted involution. These computations certify only the stated finite scope.

## Triage

### What the settlement shows

1. **Proved in prose from kernel-checked facts:** at equal dimension three, no deterministic superchannel has exactly the dephasing-covariant CPTP fixed maps; superchannel idempotence is unnecessary. `fixes_dio_identity` assumes only deterministic superchannelhood and fixation of all covariant CPTP maps. It forces identity, which fixes the CPTP channel from `R_unitary`; `R_not_covariant` excludes that channel from the desired fixed set. The universal idempotent assertion is negated by `result`.
2. **Kernel-checked mechanism:** the proof of `fixes_dio_identity` uses `depol_channel`, `depol_covariant`, and `depol_choi` to force unitality of the induced Choi map; `v_normalized`, `spanning`, `connected`, and connected-probe rigidity then force identity. Trace preservation on arbitrary Choi matrices is not assumed.
3. **Computed:** the pinned experiment verifies the qubit involution twirl with exact DIO fixed space, and computes overlap components $[3,3]$ at $d=2$, $[24]$ at $d=3$, and $[120]$ at $d=4$. The command, exit, immutable program reference and SHA-256 are in Evidence. The computational family at $d=3$ has 24 vectors; the Lean argument uses a sufficient 16-vector subfamily.
4. **Computed:** the pinned experiment verifies Eq. (29) as complete Choi dephasing at $d=1,2,3$. This classical-channel selector is distinct from the exact DIO selector refuted here. The source's state-level framework and its displayed construction incur no contradiction from this witness; generalized probabilistic extensions are not settled here.
5. **Open:** a dimension-uniform Lean theorem for every $d\ge3$ is not delivered. The preregistration gives an ordinary route through monomial Choi probes and overlap connectivity; this module certifies the sufficient $d=3$ witness.
6. **Open:** classification for arbitrary admissible destruction maps and unequal dimensions is not settled by this witness. The qubit computation is a surviving special case, not such a classification.

### Literature status

The target is the v1 question, which is absent from the v2 Open directions passage. The bounded screen in #24013 found no settlement in inspected material. Ahnefeld, Theurer and Plenio, arXiv:2609.40186v1, Theorem 10, Appendix C and Section VI discuss compatible higher-order DIO supermaps without asserting this exact fixed-set selector or its obstruction. Literature completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Completeness of prior-art searches is not established. The accepted journal manuscript and final Cambridge resource-theory book have not been compared with the v1 question. Blocked Google and OpenAlex requests and phrase scans do not supply exhaustive coverage. The finite experiment does not certify the infinite-dimensional family of dimensions. Physical or empirical claims beyond the finite-dimensional superchannel model are not asserted. The six owner escape registrations are unfinished in #25799.
