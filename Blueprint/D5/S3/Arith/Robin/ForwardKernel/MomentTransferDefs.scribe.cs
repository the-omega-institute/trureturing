using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MomentTransferDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized moving increments, mixed moments, and the fourth Brownian moment kernel.",
        H("Moment transfer definitions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cube-measure"),
                DeclarationHandle.Create(Prefix + "cubeMeasure"),
                H("Unit cube measure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The measure on real tuples indexed by Fin k is the product of k copies of Lebesgue measure restricted to (0,1]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kappa"),
                DeclarationHandle.Create(Prefix + "kappa"),
                H("Complementary exponent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real length exponent theta, kappa(theta)=1-theta."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dyadic-r"),
                DeclarationHandle.Create(Prefix + "dyadicR"),
                H("Response scale exponent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The macroscopic scale exponent r is kappa(theta)/2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dyadic-u"),
                DeclarationHandle.Create(Prefix + "dyadicU"),
                H("Macroscopic position"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The scaled position U_X(x) is x/X; for X>0 and x in [X,2X], it belongs to [1,2]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dyadic-b"),
                DeclarationHandle.Create(Prefix + "dyadicB"),
                H("Normalized moving increment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The normalized increment B(s,x) is (E(x+s*x^theta)-E(x))/sqrt(x^theta*log(x)). It depends on s and x, with no separate dyadic endpoint parameter."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dyadic-z"),
                DeclarationHandle.Create(Prefix + "dyadicZ"),
                H("Normalized profile response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The normalized response Z_X(x) is the price-weighted moving profile response divided by sqrt(X^(1-theta)*log(X))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dyadic-mixed-moment"),
                DeclarationHandle.Create(Prefix + "dyadicMixedMoment"),
                H("Weighted mixed moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a tuple s of length k, the mixed moment is the integral of U_X(x)^(k*r) times the product of B(s_i,x), against the dyadic logarithmic measure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("moment-interface"),
                DeclarationHandle.Create(Prefix + "MomentInterface"),
                H("Moment transfer interface"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is a nonnegative constant C such that, for all sufficiently large X and every s in [0,1], the integral of abs(B(s,x))^k is at most C. The specified limit function M is measurable, and each weighted mixed moment at a tuple in the unit cube converges to M at that tuple as X tends to infinity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("brownian-w4"),
                DeclarationHandle.Create(Prefix + "brownianW4"),
                H("Fourth Brownian kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For four real coordinates, W4 is min(s0,s1)*min(s2,s3) + min(s0,s2)*min(s1,s3) + min(s0,s3)*min(s1,s2), the three covariance pairings for the fourth Brownian moment on nonnegative times."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dyadic-moment-constant"),
                DeclarationHandle.Create(Prefix + "dyadicMomentConstant"),
                H("Fourth dyadic moment constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fourth-order macroscopic constant c4(theta) is (2^(2*kappa(theta))-1)/(2*kappa(theta)*log(2)). For nonzero kappa this is the integral of u^(2*kappa) against du/(u*log(2)) on [1,2]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dyadic-b-measurable"),
                DeclarationHandle.Create(Prefix + "dyadicB_measurable"),
                H("Joint measurability of normalized increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a locally bounded measurable error function E and any real exponent theta, the map (s,x) to B(s,x) is Borel measurable. Joint measurability of the moving increment and measurability of real powers, logarithm, square root, and division give the result on the whole real plane."))),
                DescribeRole.Theorem))));
}
