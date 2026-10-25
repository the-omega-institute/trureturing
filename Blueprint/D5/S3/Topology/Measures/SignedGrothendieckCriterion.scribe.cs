using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedGrothendieckCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed density, literal restriction and dual-transfer bridges for a disjoint-variation sufficient criterion.",
        H("Signed bridges for the disjoint-variation criterion"),
        Blocks(
            Paragraph(Text(
                "The intended ambient space K is compact Hausdorff with its Borel measurable structure, in an arbitrary universe. "
                + "The sufficient criterion concerns every sequence in the real continuous dual of C(K,Real), every pointwise limit and every continuous functional on that dual. "
                + "Its additional diagonal total-variation condition ranges over all uniformly variation-bounded regular signed weak-star-zero sequences and all actual pairwise disjoint Borel sets. "
                + "This document describes the independent bridges. It asserts neither the raw splitting nor the full sufficient criterion, and does not establish the diagonal condition for a CH construction.")),
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
                + "Signed-functional additivity and the total-variation operator bound give the decomposition and small-part estimates used by the eventual criterion. "
                + "Evaluation through inclusionInDoubleDual identifies an all-functional weak limit as zero whenever its continuous-function evaluations converge to zero. "
                + "Empty K, zero measures and constant sequences require no additional premise.")))));
}
