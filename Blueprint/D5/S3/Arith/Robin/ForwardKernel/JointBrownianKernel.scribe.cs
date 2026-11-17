using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class JointBrownianKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/JointBrownianKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed Brownian fourth integral factors into marginal energies and a squared cross form.",
        H("Mixed Brownian fourth kernel"),
        Blocks(
            Paragraph(Text(
                "Let g1 and g2 be measurable integrable real profiles on the unit interval, "
                + "and let C be a measurable real function on the plane, bounded in absolute "
                + "value by A>=0 on the closed unit square. The cross form is the integral "
                + "of g1(s)g2(t)C(s,t) over that square. For real kappa1 and kappa2, "
                + "the mixed fourth kernel is kappa1*kappa2*min(s0,s1)*min(s2,s3) "
                + "+ C(s0,s2)C(s1,s3) + C(s0,s3)C(s1,s2).")),
            Describe.Lean(
                DescribeId.Create("cross-kernel-form"),
                DeclarationHandle.Create(Prefix + "crossKernelForm"),
                H("Profile-weighted cross form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cross form of profiles g1 and g2 and a kernel C is the "
                    + "integral of g1(s)g2(t)C(s,t) over the unit square."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("brownian-w22"),
                DeclarationHandle.Create(Prefix + "brownianW22"),
                H("Mixed Brownian fourth kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real kappa1 and kappa2, brownianW22 is the sum "
                    + "kappa1*kappa2*min(s0,s1)*min(s2,s3) "
                    + "+ C(s0,s2)C(s1,s3) + C(s0,s3)C(s1,s2). "
                    + "The first term pairs the marginal coordinates, and the "
                    + "other two terms pair coordinates across the two profiles."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-brownian-fourth-interface"),
                DeclarationHandle.Create(Prefix + "JointBrownianFourthInterface"),
                H("Joint Brownian second and fourth limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every s in the closed unit square, the mixed moment with "
                    + "exponents (a,b) tends to c(r(a)+r(b))*C(s0,s1). For every s "
                    + "in the closed unit four-cube, the mixed moment with exponents "
                    + "(a,a,b,b) tends to c(kappa(a)+kappa(b)) times the mixed "
                    + "Brownian fourth kernel with marginal factors kappa(a),kappa(b). "
                    + "Here kappa(t)=1-t, r(t)=kappa(t)/2, and c(gamma) is the "
                    + "integral of u^gamma against du/(u*log(2)) on [1,2]. "
                    + "This conjunction specifies only pointwise limits; absolute "
                    + "moment bounds and regularity of C are separate hypotheses."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("brownian-w22-integral"),
                DeclarationHandle.Create(Prefix + "brownianW22_integral"),
                H("Integral of the mixed fourth kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The integral over the unit four-cube of "
                        + "g1(s0)g1(s1)g2(s2)g2(s3) times the mixed fourth kernel equals "
                        + "kappa1*kappa2*Q(g1)*Q(g2) plus twice the square of the cross form. "
                        + "No symmetry or positive definiteness of C is required.")),
                    Paragraph(Text(
                        "Boundedness of C and integrability of both profiles give absolute "
                        + "integrability of each cross pair. The common factorization of "
                        + "integrable functions on disjoint coordinate pairs then applies "
                        + "to all three terms. The marginal pairing contributes the product "
                        + "of the two min-kernel energies, and each cross pairing contributes "
                        + "the square of the cross form."))),
                DescribeRole.Theorem))));
}
