using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedGrothendieckCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full signed raw restriction splitting and Grothendieck sequence criteria.",
        H("Signed raw splitting and clopen oscillation"),
        Blocks(
            Paragraph(Text(
                "The intended ambient space K is compact Hausdorff with its Borel measurable structure, in an arbitrary universe. "
                + "The sufficient criterion concerns every sequence in the real continuous dual of C(K,Real), every pointwise limit and every continuous functional on that dual. "
                + "Its additional diagonal total-variation condition ranges over all uniformly variation-bounded regular signed weak-star-zero sequences and all actual pairwise disjoint Borel sets. "
                + "The unconditional raw split is consumed by the sufficient criterion below. The diagonal condition for a CH construction remains open.")),
            Paragraph(Text(
                "For arbitrary signed measures s(n), let rho be the countable sum of their total variations and let mu be rho.toFinite. "
                + "Only SFinite rho is used. The measure mu is finite and has the same null sets as rho; it is zero when all s(n) are zero. "
                + "Each original total variation is absolutely continuous with respect to mu. SignedMeasure.absolutelyContinuous_ennreal_iff gives the actual vector absolute continuity required by Radon-Nikodym reconstruction. "
                + "The real densities q(n)=s(n).rnDeriv(mu) are integrable, reconstruct s(n) through withDensity-v, and define actual Integrable.toL1 classes. "
                + "The norm of each class equals the original real total-variation mass. No regularity is asserted for mu.")),
            Paragraph(Text(
                "For every measurable E, the scalar density indicator(E,q) defines exactly the restriction of the signed density measure to E, by equality on measurable sets and setIntegral_indicator. "
                + "For an original RN density this gives s.restrict(E), and its total-variation mass is the norm of the actual indicator L1 class. "
                + "The same formulas apply to E-complement. The two signed restrictions add to s, and their total-variation masses add exactly to the original mass. "
                + "Regularity of these restrictions follows from variation_restrict and Regular.restrict_of_measure_ne_top applied to the original regular finite total variation. "
                + "It does not follow from a regularity assumption on the common controlling measure.")),
            Paragraph(Text(
                "The bounded linear map J from real L1(mu) to the continuous dual of C(K,Real) is the L1-Linfinity lpPairing precomposed with ContinuousMap.toLp at infinity. "
                + "Its value is the integral of f(x)g(x). The Holder estimate, the L1 integral bound and the continuous-function inclusion bound give operator norm at most one. "
                + "For actual toL1 densities J agrees with signedFunctional of the density measure, and therefore gives exactly the signed functionals of the original measures and their literal restrictions. "
                + "No injectivity, isometry or surjectivity of J is used. For every double-dual functional Phi, the composition Phi.comp(J) is an actual continuous L1 test. "
                + "Thus any supplied all-functional L1 weak convergence transfers through J. SignedRieszRepresentation.signed_riesz_markov_kakutani supplies an actual regular signed representative of J applied to the weak limit, with exact variation norm. "
                + "The particular density measure of that L1 limit is not asserted regular.")),
            Paragraph(Text(
                "Given arbitrary F(n) and FInf in the real continuous dual with pointwise convergence on C(K,Real), the centered values (F(n)-FInf)(g) converge to zero for every g. "
                + "Each scalar range is bounded. Banach-Steinhaus on the complete space C(K,Real) gives a uniform operator-norm bound for the centered functionals. "
                + "Signed RMK then chooses regular signed representatives with exact total-variation norm and pointwise-zero convergence. "
                + "Signed-functional additivity and the total-variation operator bound give the decomposition and small-part estimates used by the criterion. "
                + "Evaluation through inclusionInDoubleDual identifies an all-functional weak limit as zero whenever its continuous-function evaluations converge to zero. "
                + "Empty K, zero measures and constant sequences require no additional premise.")),
            Describe.Lean(
                DescribeId.Create("exists-signed-raw-restriction-splitting"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/SignedGrothendieckCriterion.exists_signed_raw_restriction_splitting"),
                H("Unconditional signed raw restriction splitting"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "Assume only that every s(n) has regular total variation and that its real total-variation mass has a common finite real upper bound. "
                        + "There exist a strictly increasing selector j, actual measurable sets E(n) pairwise disjoint as sets, r >= 0 and a regular signed measure sInf. "
                        + "Define a(n)=s(j(n)).restrict(E(n)) and b(n)=s(j(n)).restrict(E(n)-complement). These are literal restrictions of the same original input. "
                        + "For every n, s(j(n))=a(n)+b(n), both total variations are regular, and TV(a(n))(K)+TV(b(n))(K)=TV(s(j(n)))(K). "
                        + "The captured masses TV(a(n))(K) tend to r. For every continuous real functional Phi on the entire dual of C(K,Real), "
                        + "Phi(signedFunctional(b(n))) tends to Phi(signedFunctional(sInf)). No weak or splitting premise is assumed.")),
                    Paragraph(Text(
                        "Apply L1RawSplitting.exists_raw_restriction_splitting to the actual RN classes over mu. "
                        + "L1Restriction.coe_restrict and the toL1 representative identities identify its indicators with the actual signed restrictions. "
                        + "The density norm identity transfers the captured norm limit. Variation restriction and the original regularity supply both regular TVs and exact mass additivity. "
                        + "Compose each Phi with J to transfer all L1 weak tests. Signed RMK represents J(v) by an actual regular signed measure sInf; "
                        + "no regularity of mu or of mu.withDensity-v(v) is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weak-of-disjoint-diagonal-variation"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/SignedGrothendieckCriterion.weak_of_disjoint_diagonal_variation"),
                H("The full signed sufficient criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "H ranges over every signed sequence s with regular TVs, a uniform TV mass bound and weak-star-zero continuous-function evaluations. "
                        + "For every actual pairwise disjoint measurable sequence E, H requires TV(s(n).restrict(E(n)))(K) to tend to zero. "
                        + "Given H, any F(n) and FInf in StrongDual Real C(K,Real) that converge pointwise on every continuous real function "
                        + "converge against every Phi in StrongDual Real (StrongDual Real C(K,Real)) to Phi(FInf). "
                        + "The public theorem has no operator-norm bound premise. Banach-Steinhaus derives the centered bound and signed RMK supplies representatives with exact norms.")),
                    Paragraph(Text(
                        "For each Phi, Filter.tendsto_of_subseq_tendsto accepts any ns tending to infinity, whether or not ns is strictly increasing. "
                        + "Apply the unconditional raw theorem to s composed with ns, then use H on the selected original signed sequence s(ns(j(n))) and these same E(n). "
                        + "H makes the captured part small in total variation, hence in dual norm and under every continuous functional. "
                        + "The complementary part already converges Banach-weakly. Subtract captured evaluations from the original weak-star-zero evaluations. "
                        + "Testing its weak limit with the actual inclusionInDoubleDual evaluation at every g identifies that limit as the zero functional. "
                        + "Signed-functional additivity now gives Phi(F(ns(j(n)))-FInf) tending to zero. The subsequence criterion gives the original centered limit; adding Phi(FInf) proves the result.")),
                    Paragraph(Text(
                        "This is a reusable sufficient implication, assembled from classical splitting, signed representation and uniform boundedness. "
                        + "It assumes neither positivity, nonempty K, metrizability, separability, atomlessness, countable generation nor a nonzero measure. "
                        + "It establishes no CH instance of H, no transfinite induction or capture/global endpoint, and no solution or official acceptance of Problem 8.2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weak-of-signed-clopen-oscillation"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/SignedGrothendieckCriterion.weak_of_signed_clopen_oscillation"),
                H("Grothendieck convergence from signed clopen oscillation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "Let K be any compact Hausdorff zero-dimensional Borel space, in any universe. The property O quantifies over regular signed measures t(n) and pairwise disjoint nonempty clopens W(n). "
                        + "If TV(t(n))(K)=1, the positive Jordan mass is at least one half, and TV(t(n))(W(n)-complement)=0, O supplies a single clopen Z for which both sets of indices t(n)(Z)>=1/6 and t(n)(Z)=0 are infinite. "
                        + "Under exactly O, every pointwise-convergent sequence F(n) in the real continuous dual of C(K,Real) converges to the same limit under every continuous double-dual test. "
                        + "There is no norm-bound premise on F, nor any nonempty, metric, separable, countable-base or positivity assumption on K or F.")),
                    Paragraph(Text(
                        "First consider regular signed norm-one measures carried by actual pairwise disjoint Borel sets and suppose their continuous-function evaluations converge. "
                        + "ClopenDisjointization.exists_signed_clopen_disjointization with parameter 1/96 supplies two strictly increasing selectors, norm-one clopen-carried approximants and one constant sign. "
                        + "Apply that sign to the approximants and selected originals together. The signed approximants have positive Jordan mass at least one half and their total-variation error from the signed originals is strictly less than 1/48. "
                        + "Property O gives one clopen Z with infinitely recurring high and zero values. Its continuous indicator tests the convergent signed originals. "
                        + "At the high indices their evaluations exceed 7/48; at the zero indices their absolute evaluations are below 1/48. "
                        + "Convergence is impossible: a real limit below 1/12 contradicts a sufficiently late high index, while a limit at least 1/12 contradicts a sufficiently late zero index. "
                        + "The error is fixed. Neither convergence of the approximants, convergence of the retained mass to one, nor a vanishing approximation error is asserted.")),
                    Paragraph(Text(
                        "Center the arbitrary dual sequence and use Banach-Steinhaus and signed RMK to obtain bounded regular signed representatives with all continuous evaluations tending to zero. "
                        + "For every initial selector tending to infinity, apply exists_signed_raw_restriction_splitting to the selected sequence. Its literal complementary restrictions are a(n) and b(n), with pairwise disjoint measurable carriers for a, captured masses q(n) tending to r>=0, and b converging under all double-dual tests. "
                        + "Evaluation tests show that a converges weak-star to the negative of the b limit. If r>0, choose a finite tail with q(n)>r/2 and normalize a(n) by q(n) inverse. "
                        + "These measures remain regular, retain the same disjoint Borel carriers, and have TV norm exactly one. Reciprocal continuity at nonzero r and signed-functional scalar linearity give a genuine weak-star limit for this normalized tail. "
                        + "The preceding fixed-error contradiction excludes that limit, forcing r=0.")),
                    Paragraph(Text(
                        "Now a tends to zero in TV and hence in dual norm. The b limit has zero evaluation at every continuous function by uniqueness of scalar limits, so weak_limit_zero_of_evaluation identifies it as the zero functional. "
                        + "For each double-dual Phi, the selected centered sequence therefore tends to zero under Phi. Filter.tendsto_of_subseq_tendsto applies because the initial selector was arbitrary; adding back Phi(FInf) proves full weak convergence. "
                        + "This is a generic analytic implication using classical signed representation, uniform boundedness, raw splitting and clopen selection. It does not assume the earlier diagonal-TV hypothesis H. "
                        + "No CH construction or instance of O is supplied, and neither the full signed-ball endpoint nor an anti-homeomorphism conclusion nor a solution of Problem 8.2 follows here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eventually-eq-of-signed-clopen-oscillation"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/SignedGrothendieckCriterion.eventually_eq_of_signed_clopen_oscillation"),
                H("Every convergent point sequence is eventually its limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "Let K be an arbitrary compact Hausdorff zero-dimensional space with its Borel measurable structure, and assume exactly the signed clopen oscillation property O above. "
                        + "For every sequence x from the natural numbers to K and every p in K, if x tends to p then x(n)=p for all sufficiently large n. "
                        + "There is no metrizability, first-countability, injectivity or distinctness premise on x.")),
                    Paragraph(Text(
                        "If x is injective, use the actual positive Dirac measures at x(n), converted to signed measures, and the measurable singletons E(n)={x(n)}. "
                        + "Their total variations are exactly those Dirac measures, are regular, have mass one, and vanish outside their pairwise disjoint carriers. "
                        + "Regularity follows by pushing the regular Dirac measure on Unit along the constant map, using inner regularity and finiteness. "
                        + "The signed functional of the Dirac measure at a evaluates every continuous g as g(a). Continuity therefore gives scalar convergence to evaluation at p. "
                        + "The disjoint norm-one contradiction used by the oscillation criterion excludes this injective convergent sequence.")),
                    Paragraph(Text(
                        "If the range of a convergent sequence were infinite, embed the natural numbers in that range and choose an original index for each embedded value. "
                        + "The index selector and the selected point sequence are injective. An injective natural-number selector tends to infinity, so the selected sequence still tends to p, contradicting the injective case. "
                        + "The range is thus finite. Its difference with {p} is closed in the Hausdorff space, and its complement is a neighborhood of p. "
                        + "Eventually x lies in that complement and in its own range, forcing x(n)=p. "
                        + "This implication assumes O; it supplies no instance of O or CH construction."))),
                DescribeRole.Theorem))));
}
