/- GID: D5/S1/Words/EvilOdious/DyadicPrefixBounds
   generality: I
   mirror-B: D5/B/S1/Words/EvilOdious/DyadicPrefixBounds
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/EvilOdious/SixfoldMonotonicity.tail_positive; instance=D5/S1/Words/EvilOdious/DyadicPrefixBounds.prefixcertificate_0
   digest: Sixfold Thue-Morse counts are controlled by dyadic coefficient states. -/

/-
admission_basis: escape-witness
Module escape_witness: state_dyadic_bound
Direct frozen dependencies: aliases below denote declaration identities, not module pins.
none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15228.
Declaration rows: name | proof_shape | frozen dependencies | escape_witness | consumers.
Definitions carry bind-only as an organization label; no proof content is claimed for them.
tableH | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.tableError, DyadicPrefixBounds.seedH, DyadicPrefixBounds.tableH_sound, DyadicPrefixBounds.tableError_sound, DyadicPrefixBounds.h_seed, DyadicPrefixBounds.seedH_exact
tableError | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.initial_r, SixfoldMonotonicity.initial_s, DyadicPrefixBounds.tableError_sound, DyadicPrefixBounds.initialChunk
seedH | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.error_prefix, DyadicPrefixBounds.prefixB, DyadicPrefixBounds.h_seed, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.seedH_exact, DyadicPrefixBounds.h_dyadic
seedC | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.error_prefix, DyadicPrefixBounds.prefixB, DyadicPrefixBounds.c_seed, DyadicPrefixBounds.c_prefix, DyadicPrefixBounds.seedC_exact, DyadicPrefixBounds.c_dyadic
prefixB | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.prefix_certificate, SixfoldMonotonicity.error_prefix, SixfoldMonotonicity.tail_positive, DyadicPrefixBounds.prefixChunk
tableH_sound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.tableError_sound, DyadicPrefixBounds.h_seed, DyadicPrefixBounds.seedH_exact
tableC_sound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.tableError_sound, DyadicPrefixBounds.c_seed, DyadicPrefixBounds.seedC_exact
tableError_sound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.initial_r, SixfoldMonotonicity.initial_s
prefixChunk | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_0, DyadicPrefixBounds.prefixcertificate_1, DyadicPrefixBounds.prefixcertificate_2, DyadicPrefixBounds.prefixcertificate_3, DyadicPrefixBounds.prefixcertificate_4, DyadicPrefixBounds.prefixcertificate_5, DyadicPrefixBounds.prefixcertificate_6, DyadicPrefixBounds.prefixcertificate_7, DyadicPrefixBounds.prefixcertificate_8, DyadicPrefixBounds.prefixcertificate_9, DyadicPrefixBounds.prefixcertificate_10, DyadicPrefixBounds.prefixcertificate_11, DyadicPrefixBounds.prefixcertificate_12, DyadicPrefixBounds.prefixcertificate_13, DyadicPrefixBounds.prefixcertificate_14, DyadicPrefixBounds.prefixcertificate_15, DyadicPrefixBounds.prefixcertificate_16, DyadicPrefixBounds.prefixcertificate_17, DyadicPrefixBounds.prefixcertificate_18, DyadicPrefixBounds.prefixcertificate_19, DyadicPrefixBounds.prefixcertificate_20, DyadicPrefixBounds.prefixcertificate_21, DyadicPrefixBounds.prefixcertificate_22, DyadicPrefixBounds.prefixcertificate_23, DyadicPrefixBounds.prefixcertificate_24, DyadicPrefixBounds.prefixcertificate_25, DyadicPrefixBounds.prefixcertificate_26, DyadicPrefixBounds.prefixcertificate_27, DyadicPrefixBounds.prefixcertificate_28, DyadicPrefixBounds.prefixcertificate_29, DyadicPrefixBounds.prefixcertificate_30, DyadicPrefixBounds.prefixcertificate_31, DyadicPrefixBounds.prefixcertificate_32, DyadicPrefixBounds.prefixcertificate_33, DyadicPrefixBounds.prefixcertificate_34, DyadicPrefixBounds.prefixcertificate_35, DyadicPrefixBounds.prefixcertificate_36, DyadicPrefixBounds.prefixcertificate_37, DyadicPrefixBounds.prefixcertificate_38, DyadicPrefixBounds.prefixcertificate_39, DyadicPrefixBounds.prefixcertificate_40, DyadicPrefixBounds.prefixcertificate_41, DyadicPrefixBounds.prefixcertificate_42, DyadicPrefixBounds.prefixcertificate_43, DyadicPrefixBounds.prefixcertificate_44, DyadicPrefixBounds.prefixcertificate_45, DyadicPrefixBounds.prefixcertificate_46, DyadicPrefixBounds.prefixcertificate_47, DyadicPrefixBounds.prefixcertificate_48, DyadicPrefixBounds.prefixcertificate_49, DyadicPrefixBounds.prefixcertificate_50, DyadicPrefixBounds.prefixcertificate_51, DyadicPrefixBounds.prefixcertificate_52, DyadicPrefixBounds.prefixcertificate_53, DyadicPrefixBounds.prefixcertificate_54, DyadicPrefixBounds.prefixcertificate_55, DyadicPrefixBounds.prefixcertificate_56, DyadicPrefixBounds.prefixcertificate_57, DyadicPrefixBounds.prefixcertificate_58, DyadicPrefixBounds.prefixcertificate_59, DyadicPrefixBounds.prefixcertificate_60, DyadicPrefixBounds.prefixcertificate_61, DyadicPrefixBounds.prefixcertificate_62, DyadicPrefixBounds.prefixcertificate_63, DyadicPrefixBounds.prefixcertificate_checked
initialChunk | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.initialr_0, SixfoldMonotonicity.initialr_1, SixfoldMonotonicity.initialr_2, SixfoldMonotonicity.initialr_3, SixfoldMonotonicity.initialr_4, SixfoldMonotonicity.initialr_5, SixfoldMonotonicity.initialr_6, SixfoldMonotonicity.initialr_7, SixfoldMonotonicity.initialr_8, SixfoldMonotonicity.initialr_9, SixfoldMonotonicity.initialr_10, SixfoldMonotonicity.initialr_11, SixfoldMonotonicity.initialr_12, SixfoldMonotonicity.initialr_13, SixfoldMonotonicity.initialr_14, SixfoldMonotonicity.initialr_15, SixfoldMonotonicity.initialr_16, SixfoldMonotonicity.initialr_17, SixfoldMonotonicity.initialr_18, SixfoldMonotonicity.initialr_19, SixfoldMonotonicity.initialr_20, SixfoldMonotonicity.initialr_21, SixfoldMonotonicity.initialr_22, SixfoldMonotonicity.initialr_23, SixfoldMonotonicity.initialr_24, SixfoldMonotonicity.initialr_25, SixfoldMonotonicity.initialr_26, SixfoldMonotonicity.initialr_27, SixfoldMonotonicity.initialr_28, SixfoldMonotonicity.initialr_29, SixfoldMonotonicity.initialr_30, SixfoldMonotonicity.initialr_31, SixfoldMonotonicity.initialr_32, SixfoldMonotonicity.initialr_33, SixfoldMonotonicity.initialr_34, SixfoldMonotonicity.initialr_35, SixfoldMonotonicity.initialr_36, SixfoldMonotonicity.initialr_37, SixfoldMonotonicity.initialr_38, SixfoldMonotonicity.initialr_39, SixfoldMonotonicity.initialr_40, SixfoldMonotonicity.initialr_41, SixfoldMonotonicity.initialr_42, SixfoldMonotonicity.initialr_43, SixfoldMonotonicity.initialr_44, SixfoldMonotonicity.initialr_45, SixfoldMonotonicity.initialr_46, SixfoldMonotonicity.initialr_47, SixfoldMonotonicity.initialr_48, SixfoldMonotonicity.initialr_49, SixfoldMonotonicity.initialr_50, SixfoldMonotonicity.initialr_51, SixfoldMonotonicity.initialr_52, SixfoldMonotonicity.initialr_53, SixfoldMonotonicity.initialr_54, SixfoldMonotonicity.initialr_55, SixfoldMonotonicity.initialr_56, SixfoldMonotonicity.initialr_57, SixfoldMonotonicity.initialr_58, SixfoldMonotonicity.initialr_59, SixfoldMonotonicity.initialr_60, SixfoldMonotonicity.initialr_61, SixfoldMonotonicity.initialr_62, SixfoldMonotonicity.initialr_63, SixfoldMonotonicity.initialr_checked, SixfoldMonotonicity.initials_0, SixfoldMonotonicity.initials_1, SixfoldMonotonicity.initials_2, SixfoldMonotonicity.initials_3, SixfoldMonotonicity.initials_4, SixfoldMonotonicity.initials_5, SixfoldMonotonicity.initials_6, SixfoldMonotonicity.initials_7, SixfoldMonotonicity.initials_8, SixfoldMonotonicity.initials_9, SixfoldMonotonicity.initials_10, SixfoldMonotonicity.initials_11, SixfoldMonotonicity.initials_12, SixfoldMonotonicity.initials_13, SixfoldMonotonicity.initials_14, SixfoldMonotonicity.initials_15, SixfoldMonotonicity.initials_16, SixfoldMonotonicity.initials_17, SixfoldMonotonicity.initials_18, SixfoldMonotonicity.initials_19, SixfoldMonotonicity.initials_20, SixfoldMonotonicity.initials_21, SixfoldMonotonicity.initials_22, SixfoldMonotonicity.initials_23, SixfoldMonotonicity.initials_24, SixfoldMonotonicity.initials_25, SixfoldMonotonicity.initials_26, SixfoldMonotonicity.initials_27, SixfoldMonotonicity.initials_28, SixfoldMonotonicity.initials_29, SixfoldMonotonicity.initials_30, SixfoldMonotonicity.initials_31, SixfoldMonotonicity.initials_32, SixfoldMonotonicity.initials_33, SixfoldMonotonicity.initials_34, SixfoldMonotonicity.initials_35, SixfoldMonotonicity.initials_36, SixfoldMonotonicity.initials_37, SixfoldMonotonicity.initials_38, SixfoldMonotonicity.initials_39, SixfoldMonotonicity.initials_40, SixfoldMonotonicity.initials_41, SixfoldMonotonicity.initials_42, SixfoldMonotonicity.initials_43, SixfoldMonotonicity.initials_44, SixfoldMonotonicity.initials_45, SixfoldMonotonicity.initials_46, SixfoldMonotonicity.initials_47, SixfoldMonotonicity.initials_48, SixfoldMonotonicity.initials_49, SixfoldMonotonicity.initials_50, SixfoldMonotonicity.initials_51, SixfoldMonotonicity.initials_52, SixfoldMonotonicity.initials_53, SixfoldMonotonicity.initials_54, SixfoldMonotonicity.initials_55, SixfoldMonotonicity.initials_56, SixfoldMonotonicity.initials_57, SixfoldMonotonicity.initials_58, SixfoldMonotonicity.initials_59, SixfoldMonotonicity.initials_60, SixfoldMonotonicity.initials_61, SixfoldMonotonicity.initials_62, SixfoldMonotonicity.initials_63, SixfoldMonotonicity.initials_checked
prefixcertificate_0 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_1 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_2 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_3 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_4 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_5 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_6 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_7 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_8 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_9 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_10 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_11 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_12 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_13 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_14 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_15 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_16 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_17 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_18 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_19 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_20 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_21 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_22 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_23 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_24 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_25 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_26 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_27 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_28 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_29 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_30 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_31 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_32 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_33 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_34 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_35 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_36 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_37 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_38 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_39 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_40 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_41 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_42 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_43 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_44 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_45 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_46 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_47 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_48 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_49 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_50 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_51 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_52 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_53 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_54 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_55 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_56 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_57 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_58 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_59 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_60 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_61 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_62 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_63 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.prefixcertificate_checked
prefixcertificate_checked | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.prefix_certificate
appendValue | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.prefix_exists, SixfoldMonotonicity.prefix_scale_lower, SixfoldMonotonicity.error_prefix, SixfoldMonotonicity.tail_positive, DyadicPrefixBounds.appendValue_cons, DyadicPrefixBounds.appendValue_ge, DyadicPrefixBounds.state_word, DyadicPrefixBounds.vector_prefix_bound, DyadicPrefixBounds.appendValue_decompose, DyadicPrefixBounds.lowWord_bound, DyadicPrefixBounds.word_for_low, DyadicPrefixBounds.state_dyadic_bound, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.c_prefix, DyadicPrefixBounds.h_dyadic, DyadicPrefixBounds.c_dyadic, DyadicPrefixBounds.appendValue_cons
appendValue_cons | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.prefix_exists, SixfoldMonotonicity.prefix_scale_lower, DyadicPrefixBounds.appendValue_ge, DyadicPrefixBounds.state_word, DyadicPrefixBounds.word_for_low
appendValue_ge | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.c_prefix
state_word | proof_shape: content | frozen: none | escape_witness: state_word | consumers: DyadicPrefixBounds.vector_prefix_bound
vector_prefix_bound | proof_shape: content | frozen: none | escape_witness: vector_prefix_bound | consumers: DyadicPrefixBounds.state_dyadic_bound
word_bound_of_step | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.h_prefix
appendValue_decompose | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.error_prefix, DyadicPrefixBounds.state_dyadic_bound, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.c_prefix, DyadicPrefixBounds.h_dyadic, DyadicPrefixBounds.c_dyadic
lowWord_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.error_prefix, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.c_prefix
word_for_low | proof_shape: content | frozen: none | escape_witness: word_for_low | consumers: DyadicPrefixBounds.state_dyadic_bound, DyadicPrefixBounds.h_dyadic, DyadicPrefixBounds.c_dyadic
h_step_norm | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.h_prefix
h_state_step | proof_shape: content | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.h_prefix
h_seed | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.h_prefix
c_seed | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.c_prefix
state_dyadic_bound | proof_shape: content | frozen: none | escape_witness: state_dyadic_bound | consumers: DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.c_prefix
h_prefix | proof_shape: content | frozen: none | escape_witness: h_prefix | consumers: DyadicPrefixBounds.h_dyadic
c_prefix | proof_shape: content | frozen: none | escape_witness: c_prefix | consumers: DyadicPrefixBounds.c_dyadic
seedH_exact | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.error_prefix, DyadicPrefixBounds.h_dyadic
seedC_exact | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.error_prefix, DyadicPrefixBounds.c_dyadic
h_dyadic | proof_shape: content | frozen: none | escape_witness: h_dyadic | consumers: SixfoldMonotonicity.error_prefix
c_dyadic | proof_shape: content | frozen: none | escape_witness: c_dyadic | consumers: SixfoldMonotonicity.error_prefix
Utility checker: all certificates are kernel-checked and used by the named consumer.
-/

import D5.S1.Words.EvilOdious.DyadicStatesLastThree
import D5.S1.Words.EvilOdious.CoefficientTableChecker

namespace D5.S1.Words.EvilOdious.DyadicPrefixBounds
open D5.S1.Words.EvilOdious.SequenceCoefficients
open D5.S1.Words.EvilOdious.MatrixBounds
open D5.S1.Words.EvilOdious.DyadicStatesFirstThree
open D5.S1.Words.EvilOdious.DyadicStatesLastThree
open D5.S1.Words.EvilOdious.CoefficientTableChecker

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Finset

def tableH (j n : ℕ) : ℤ :=
  match j with
  | 1 => (tableValue table1) n
  | 2 => (tableValue table2) n
  | 3 => (tableValue table3) n
  | 4 => (tableValue table4) n
  | _ => (tableValue table5) n


def tableError (sigma : ℤ) (n : ℕ) : ℤ :=
  (∑ j ∈ Finset.Icc 1 5, sigma ^ j * (Nat.choose 6 j : ℤ) * tableH j n) + (tableValue table6) n - (tableValue table6) (n-1)

def seedH (j n : ℕ) : ℕ := (Finset.range 5).sup (fun i => (tableH j (n-i)).natAbs)
def seedC (n : ℕ) : ℕ := (Finset.range 6).sup (fun i => ((tableValue table6) (n-i)).natAbs)
def prefixB (n : ℕ) : ℕ := (∑ j ∈ Finset.Icc 1 5, Nat.choose 6 j * seedH j n) + 4 * seedC n

theorem tableH_sound (j n : ℕ) (hj : j ∈ Finset.Icc 1 5) (hn : n < 4096) :
    (recur (p j) n) = tableH j n := by
  rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
  interval_cases j
  · exact table1_sound n hn
  · exact table2_sound n hn
  · exact table3_sound n hn
  · exact table4_sound n hn
  · exact table5_sound n hn

private theorem tableC_sound (n : ℕ) (hn : n < 4096) : (recur (p 6) n) = (tableValue table6) n := table6_sound n hn

theorem tableError_sound (sigma : ℤ) (n : ℕ) (hn : n < 4096) :
    errorTerm sigma n = tableError sigma n := by
  unfold errorTerm tableError
  rw [tableC_sound n hn, tableC_sound (n-1) (by omega)]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [tableH_sound j n hj hn]

def prefixChunk (base len : ℕ) : Bool :=
  (List.range len).all (fun k => decide (24 * prefixB (base+k) < (base+k)^4))

def initialChunk (sigma : ℤ) (lower base len : ℕ) : Bool :=
  (List.range len).all (fun k => decide
    (lower ≤ base+k → 0 < ((Nat.descFactorial (base+k+4) 4 / 24 : ℕ) : ℤ) + tableError sigma (base+k)))



set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option profiler true in
set_option profiler.threshold 10 in
theorem prefixcertificate_0 : prefixChunk 2048 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_1 : prefixChunk 2080 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_2 : prefixChunk 2112 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_3 : prefixChunk 2144 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_4 : prefixChunk 2176 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_5 : prefixChunk 2208 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_6 : prefixChunk 2240 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_7 : prefixChunk 2272 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_8 : prefixChunk 2304 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_9 : prefixChunk 2336 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_10 : prefixChunk 2368 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_11 : prefixChunk 2400 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_12 : prefixChunk 2432 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_13 : prefixChunk 2464 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_14 : prefixChunk 2496 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_15 : prefixChunk 2528 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_16 : prefixChunk 2560 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_17 : prefixChunk 2592 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_18 : prefixChunk 2624 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_19 : prefixChunk 2656 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_20 : prefixChunk 2688 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_21 : prefixChunk 2720 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_22 : prefixChunk 2752 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_23 : prefixChunk 2784 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_24 : prefixChunk 2816 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_25 : prefixChunk 2848 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_26 : prefixChunk 2880 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_27 : prefixChunk 2912 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_28 : prefixChunk 2944 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_29 : prefixChunk 2976 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_30 : prefixChunk 3008 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_31 : prefixChunk 3040 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_32 : prefixChunk 3072 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_33 : prefixChunk 3104 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_34 : prefixChunk 3136 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_35 : prefixChunk 3168 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_36 : prefixChunk 3200 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_37 : prefixChunk 3232 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_38 : prefixChunk 3264 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_39 : prefixChunk 3296 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_40 : prefixChunk 3328 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_41 : prefixChunk 3360 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_42 : prefixChunk 3392 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_43 : prefixChunk 3424 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_44 : prefixChunk 3456 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_45 : prefixChunk 3488 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_46 : prefixChunk 3520 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_47 : prefixChunk 3552 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_48 : prefixChunk 3584 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_49 : prefixChunk 3616 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_50 : prefixChunk 3648 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_51 : prefixChunk 3680 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_52 : prefixChunk 3712 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_53 : prefixChunk 3744 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_54 : prefixChunk 3776 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_55 : prefixChunk 3808 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_56 : prefixChunk 3840 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_57 : prefixChunk 3872 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_58 : prefixChunk 3904 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_59 : prefixChunk 3936 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_60 : prefixChunk 3968 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_61 : prefixChunk 4000 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_62 : prefixChunk 4032 32 = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 10 in
private theorem prefixcertificate_63 : prefixChunk 4064 32 = true := by decide +kernel
theorem prefixcertificate_checked (block : Fin 64) : prefixChunk (2048 + 32 * block.val) 32 = true := by
  fin_cases block
  · exact prefixcertificate_0
  · exact prefixcertificate_1
  · exact prefixcertificate_2
  · exact prefixcertificate_3
  · exact prefixcertificate_4
  · exact prefixcertificate_5
  · exact prefixcertificate_6
  · exact prefixcertificate_7
  · exact prefixcertificate_8
  · exact prefixcertificate_9
  · exact prefixcertificate_10
  · exact prefixcertificate_11
  · exact prefixcertificate_12
  · exact prefixcertificate_13
  · exact prefixcertificate_14
  · exact prefixcertificate_15
  · exact prefixcertificate_16
  · exact prefixcertificate_17
  · exact prefixcertificate_18
  · exact prefixcertificate_19
  · exact prefixcertificate_20
  · exact prefixcertificate_21
  · exact prefixcertificate_22
  · exact prefixcertificate_23
  · exact prefixcertificate_24
  · exact prefixcertificate_25
  · exact prefixcertificate_26
  · exact prefixcertificate_27
  · exact prefixcertificate_28
  · exact prefixcertificate_29
  · exact prefixcertificate_30
  · exact prefixcertificate_31
  · exact prefixcertificate_32
  · exact prefixcertificate_33
  · exact prefixcertificate_34
  · exact prefixcertificate_35
  · exact prefixcertificate_36
  · exact prefixcertificate_37
  · exact prefixcertificate_38
  · exact prefixcertificate_39
  · exact prefixcertificate_40
  · exact prefixcertificate_41
  · exact prefixcertificate_42
  · exact prefixcertificate_43
  · exact prefixcertificate_44
  · exact prefixcertificate_45
  · exact prefixcertificate_46
  · exact prefixcertificate_47
  · exact prefixcertificate_48
  · exact prefixcertificate_49
  · exact prefixcertificate_50
  · exact prefixcertificate_51
  · exact prefixcertificate_52
  · exact prefixcertificate_53
  · exact prefixcertificate_54
  · exact prefixcertificate_55
  · exact prefixcertificate_56
  · exact prefixcertificate_57
  · exact prefixcertificate_58
  · exact prefixcertificate_59
  · exact prefixcertificate_60
  · exact prefixcertificate_61
  · exact prefixcertificate_62
  · exact prefixcertificate_63




set_option autoImplicit false
open Finset Matrix

-- A general prefix theorem separates matrix estimates from sequence evaluation.
def appendValue (q : ℕ) (w : List Bool) : ℕ :=
  Nat.ofDigits 2 (w.map Bool.toNat ++ [q])

theorem appendValue_cons (q : ℕ) (b : Bool) (w : List Bool) :
    appendValue q (b :: w) = 2 * appendValue q w + (if b then 1 else 0) := by
  cases b <;> simp [appendValue, Nat.ofDigits_cons, Nat.add_comm]

private theorem appendValue_ge (p : ℕ) (w : List Bool) : p ≤ appendValue p w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [appendValue_cons]
    omega

private theorem state_word {d : ℕ} (q : List ℤ) (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (step : ∀ n, ∀ b, stateZ d q (2*n+(if b then 1 else 0)) = (M b).mulVec (stateZ d q n))
    (p : ℕ) (w : List Bool) :
    stateZ d q (appendValue p w) = (wordMatrix M w).mulVec (stateZ d q p) := by
  induction w with
  | nil => simp [appendValue, wordMatrix]
  | cons b w ih =>
    rw [appendValue_cons, step _, ih, Matrix.mulVec_mulVec]
    simp only [wordMatrix, List.map_cons, List.prod_cons]

private theorem vector_prefix_bound {d : ℕ} (q : List ℤ) (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (step : ∀ n, ∀ b, stateZ d q (2*n+(if b then 1 else 0)) = (M b).mulVec (stateZ d q n))
    (K : ℕ) (norm : ∀ w, matrixBound (wordMatrix M w) (K * 16 ^ w.length))
    (p : ℕ) (w : List Bool) (B : ℕ) (seed : vectorBound (stateZ d q p) B) :
    vectorBound (stateZ d q (appendValue p w)) (K * 16 ^ w.length * B) := by
  rw [state_word q M step p w]
  exact matrix_apply_bound _ _ _ _ (norm w) seed

private theorem word_bound_of_step {d : ℕ} (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (hb : ∀ b, matrixBound (M b) 16) (w : List Bool) :
    matrixBound (wordMatrix M w) (16 ^ w.length) := by
  induction w with
  | nil => intro i; simp [wordMatrix, Matrix.one_apply, apply_ite]
  | cons b w ih =>
    have hh := matrix_mul_bound _ _ _ _ (hb b) ih
    simpa [wordMatrix, Nat.pow_succ, Nat.mul_comm] using hh




set_option autoImplicit false

theorem appendValue_decompose (p0 : ℕ) (w : List Bool) :
    appendValue p0 w = p0 * 2 ^ w.length + appendValue 0 w := by
  simp only [appendValue, Nat.ofDigits_append, Nat.ofDigits_singleton, List.length_map,
    mul_zero, add_zero]
  ring

theorem lowWord_bound (w : List Bool) : appendValue 0 w < 2 ^ w.length := by
  simp only [appendValue, Nat.ofDigits_append, Nat.ofDigits_singleton, List.length_map,
    mul_zero, add_zero]
  have hd : ∀ d ∈ w.map Bool.toNat, d < 2 := by
    intro d hd
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
    cases b <;> decide
  simpa only [List.length_map] using
    Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2) hd

private theorem word_for_low (m low : ℕ) (hlow : low < 2 ^ m) :
    ∃ w : List Bool, w.length = m ∧ appendValue 0 w = low := by
  induction m generalizing low with
  | zero => exact ⟨[],rfl,by simpa [appendValue] using (show low = 0 by simpa using hlow).symm⟩
  | succ m ih =>
    have hh : low/2 < 2^m := by simp only [Nat.pow_succ] at hlow; omega
    obtain ⟨w,hw,hv⟩ := ih (low/2) hh
    rcases Nat.mod_two_eq_zero_or_one low with hb | hb
    · refine ⟨false::w, by simp [hw], ?_⟩
      simp only [appendValue_cons, Bool.false_eq_true, if_false, Nat.add_zero, hv]
      omega
    · refine ⟨true::w, by simp [hw], ?_⟩
      simp only [appendValue_cons, if_true, hv]
      omega




set_option autoImplicit false
open Finset Matrix

private theorem h_step_norm (j : ℕ) (hj : j ∈ Finset.Icc 1 5) (b : Bool) :
    matrixBound (stateMatrix 5 (p j) b) 16 := by
  rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
  rcases h_matrix_bound with ⟨h1f,h1t,h2f,h2t,h3f,h3t,h4f,h4t,h5f,h5t⟩
  interval_cases j <;> cases b <;> intro i
  · exact (h1f i).trans (by decide)
  · exact (h1t i).trans (by decide)
  · exact (h2f i).trans (by decide)
  · exact (h2t i).trans (by decide)
  · exact (h3f i).trans (by decide)
  · exact (h3t i).trans (by decide)
  · exact (h4f i).trans (by decide)
  · exact (h4t i).trans (by decide)
  · exact h5f i
  · exact h5t i

private theorem h_state_step (j : ℕ) (hj : j ∈ Finset.Icc 1 5) (n : ℕ) (b : Bool) :
    stateZ 5 (p j) (2*n+(if b then 1 else 0)) =
      (stateMatrix 5 (p j) b).mulVec (stateZ 5 (p j) n) := by
  rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
  interval_cases j
  · exact stateZ_step_1 n b
  · exact stateZ_step_2 n b
  · exact stateZ_step_3 n b
  · exact stateZ_step_4 n b
  · exact stateZ_step_5 n b

private theorem h_seed (j p0 : ℕ) (hj : j ∈ Finset.Icc 1 5) (hl : 2048 ≤ p0) (hu : p0 < 4096) :
    vectorBound (stateZ 5 (p j) p0) (seedH j p0) := by
  rw [stateZ_eq_state 5 (by decide) (p j) p0 (by omega)]
  intro i
  simp only [state]
  change ((recur (p j) (p0-i))).natAbs ≤ seedH j p0
  rw [tableH_sound j (p0-i) hj (by omega)]
  exact Finset.le_sup (f := fun a => (tableH j (p0-a)).natAbs) (by simpa using i.isLt)

private theorem c_seed (p0 : ℕ) (hl : 2048 ≤ p0) (hu : p0 < 4096) :
    vectorBound (stateZ 6 (p 6) p0) (seedC p0) := by
  rw [stateZ_eq_state 6 (by decide) (p 6) p0 (by omega)]
  intro i
  simp only [state]
  change ((recur (p 6) (p0-i))).natAbs ≤ seedC p0
  rw [tableC_sound (p0-i) (by omega)]
  exact Finset.le_sup (f := fun a => ((tableValue table6) (p0-a)).natAbs) (by simpa using i.isLt)

private theorem state_dyadic_bound {d : ℕ} (q : List ℤ) (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (step : ∀ n b, stateZ d q (2*n+(if b then 1 else 0)) = (M b).mulVec (stateZ d q n))
    (K : ℕ) (norm : ∀ w, matrixBound (wordMatrix M w) (K * 16 ^ w.length))
    (p0 m low : ℕ) (hlow : low < 2 ^ m) :
    vectorBound (stateZ d q (p0*2^m+low))
      (K * 16 ^ m * (Finset.range d).sup (fun i => (zrecur q ((p0:ℤ)-i)).natAbs)) := by
  obtain ⟨w,hw,hv⟩ := word_for_low m low hlow
  have hs : vectorBound (stateZ d q p0)
      ((Finset.range d).sup (fun i => (zrecur q ((p0:ℤ)-i)).natAbs)) := by
    intro i
    exact Finset.le_sup (s := Finset.range d) (b := i.val)
      (f := fun a => (zrecur q ((p0:ℤ)-a)).natAbs) (Finset.mem_range.mpr i.isLt)
  have hb := vector_prefix_bound q M step K norm p0 w _ hs
  rw [appendValue_decompose, hw, hv] at hb
  exact hb

private theorem h_prefix (j p0 : ℕ) (hj : j ∈ Finset.Icc 1 5)
    (hl : 2048 ≤ p0) (hu : p0 < 4096) (w : List Bool) :
    ((recur (p j) (appendValue p0 w))).natAbs ≤ 16 ^ w.length * seedH j p0 := by
  have hmax : (Finset.range 5).sup (fun i => (zrecur (p j) ((p0:ℤ)-i)).natAbs) ≤ seedH j p0 := by
    apply Finset.sup_le
    intro i hi
    exact h_seed j p0 hj hl hu ⟨i, by simpa using hi⟩
  have hb := state_dyadic_bound (p j) (stateMatrix 5 (p j))
    (fun n b => h_state_step j hj n b) 1
    (fun w => by simpa using word_bound_of_step _ (h_step_norm j hj) w)
    p0 w.length (appendValue 0 w) (lowWord_bound w)
  rw [← appendValue_decompose] at hb
  have hb' : vectorBound (stateZ 5 (p j) (appendValue p0 w)) (16 ^ w.length * seedH j p0) := by
    intro i
    exact (hb i).trans (by simpa using Nat.mul_le_mul_left (16 ^ w.length) hmax)
  have hb := hb'
  have hh := hb 0
  have hn : 6 ≤ appendValue p0 w := by have := appendValue_ge p0 w; omega
  rw [stateZ_eq_state 5 (by decide) (p j) _ hn] at hh
  simpa [state] using hh

theorem c_prefix (p0 : ℕ) (hl : 2048 ≤ p0) (hu : p0 < 4096) (w : List Bool) :
    ((recur (p 6) (appendValue p0 w))).natAbs ≤ 2 * 16 ^ w.length * seedC p0 ∧
    ((recur (p 6) (appendValue p0 w - 1))).natAbs ≤ 2 * 16 ^ w.length * seedC p0 := by
  have hmax : (Finset.range 6).sup (fun i => (zrecur (p 6) ((p0:ℤ)-i)).natAbs) ≤ seedC p0 := by
    apply Finset.sup_le
    intro i hi
    exact c_seed p0 hl hu ⟨i, by simpa using hi⟩
  have hb := state_dyadic_bound (p 6) (stateMatrix 6 (p 6)) (fun n b => stateZ_step_6 n b)
    2 c_word_bound p0 w.length (appendValue 0 w) (lowWord_bound w)
  rw [← appendValue_decompose] at hb
  have hb' : vectorBound (stateZ 6 (p 6) (appendValue p0 w)) (2 * 16 ^ w.length * seedC p0) := by
    intro i
    exact (hb i).trans (Nat.mul_le_mul_left (2 * 16 ^ w.length) hmax)
  have hb := hb'
  have hn : 6 ≤ appendValue p0 w := by have := appendValue_ge p0 w; omega
  rw [stateZ_eq_state 6 (by decide) (p 6) _ hn] at hb
  exact ⟨by simpa [state] using hb 0, by simpa [state] using hb 1⟩




set_option autoImplicit false
open Finset

theorem seedH_exact (j p0 : ℕ) (hj : j ∈ Finset.Icc 1 5) (hu : p0 < 4096) :
    seedH j p0 = (Finset.range 5).sup (fun i => ((recur (p j) (p0-i))).natAbs) := by
  unfold seedH
  congr 1
  funext i
  rw [tableH_sound j (p0-i) hj (by omega)]

theorem seedC_exact (p0 : ℕ) (hu : p0 < 4096) :
    seedC p0 = (Finset.range 6).sup (fun i => ((recur (p 6) (p0-i))).natAbs) := by
  unfold seedC
  congr 1
  funext i
  rw [tableC_sound (p0-i) (by omega)]

theorem h_dyadic (j p0 m low : ℕ) (hj : j ∈ Finset.Icc 1 5)
    (hl : 2048 ≤ p0) (hu : p0 < 4096) (hlow : low < 2 ^ m) :
    ((recur (p j) (p0*2^m+low))).natAbs ≤
      16 ^ m * (Finset.range 5).sup (fun i => ((recur (p j) (p0-i))).natAbs) := by
  obtain ⟨w,hw,hv⟩ := word_for_low m low hlow
  have hh := h_prefix j p0 hj hl hu w
  rw [appendValue_decompose, hw, hv, seedH_exact j p0 hj hu] at hh
  exact hh

theorem c_dyadic (p0 m low : ℕ) (hl : 2048 ≤ p0) (hu : p0 < 4096) (hlow : low < 2 ^ m) :
    ((recur (p 6) (p0*2^m+low))).natAbs ≤
        2 * 16 ^ m * (Finset.range 6).sup (fun i => ((recur (p 6) (p0-i))).natAbs) ∧
    ((recur (p 6) (p0*2^m+low-1))).natAbs ≤
        2 * 16 ^ m * (Finset.range 6).sup (fun i => ((recur (p 6) (p0-i))).natAbs) := by
  obtain ⟨w,hw,hv⟩ := word_for_low m low hlow
  have hh := c_prefix p0 hl hu w
  rw [appendValue_decompose, hw, hv, seedC_exact p0 hu] at hh
  exact hh

end D5.S1.Words.EvilOdious.DyadicPrefixBounds
