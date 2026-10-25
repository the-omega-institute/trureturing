using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedGrothendieckCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full signed raw restriction splitting and a sufficient Grothendieck sequence criterion.",
        H("Signed raw splitting and the disjoint-variation criterion"),
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
                DescribeRole.Theorem))));
}
