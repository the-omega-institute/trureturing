using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class FixedScaleSpecializationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FixedScaleSpecialization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The third and fourth fixed-scale mixed-moment interfaces hold for the complete Chebyshev error.",
        H("Fixed-scale Chebyshev mixed moments"),
        Blocks(
            Paragraph(Text(
                "For X>1, H=X^theta, nonnegative prefix lengths c, and 1<=u<=v<=2, the normalized increment of psi-id is Z(H,0,c,x,X). "
                + "The logarithmic block moment is the weighted moment with weight "
                + "1_[u,v](t)/(t log 2), whose integral is the block probability mass and "
                + "whose supremum-plus-variation bound is 3/log 2. The exact identities "
                + "kappa(X,X^theta)=1-theta and W4(0,c)=brownianW4(c) identify the limits.")),
            Describe.Lean(
                DescribeId.Create("fixed-scale-third"),
                DeclarationHandle.Create(Prefix + "fixed_scale_third"),
                H("Third fixed-scale mixed moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let 0<theta<beta<1/3. Assume MeanSquareHL(3,concreteSS,beta) and IntervalCorrelations(concreteSS), the interval-correlation conclusions of Lemma 498.3 taken as a hypothesis. Then psi(x)-x satisfies the third fixed-scale mixed-moment interface of section 497 with zero limit. For each bounded family of nonnegative prefix lengths and each logarithmic dyadic block [u,v], the product of three increments at length X^theta, divided by (X^theta log X)^(3/2), has block expectation tending to zero. This is the cubic specialization of Theorem 498.1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-scale-fourth"),
                DeclarationHandle.Create(Prefix + "fixed_scale_fourth"),
                H("Fourth fixed-scale mixed moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let 0<theta<beta<1/4, and assume MeanSquareHL4(concreteSS,beta) and IntervalCorrelations(concreteSS). Then psi(x)-x satisfies the fourth fixed-scale mixed-moment interface of section 497 with limiting profile (1-theta)^2 times brownianW4. For four nonnegative prefix lengths c_i, brownianW4 is the sum of the three products min(c_i,c_j)*min(c_k,c_l). Each logarithmic dyadic block expectation converges to its block probability mass times this profile. This is the fourth-order specialization of Theorem 498.1; the centered correlation conclusions of Lemma 498.3 remain explicit hypotheses."))),
                DescribeRole.Theorem))));
}
