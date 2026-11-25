using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.PositiveT;

internal sealed class GeneratorIdentificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identification of the original positive T generator",
        H("Summation of finite positive T modes"),
        Blocks(
            Describe.Lean(DescribeId.Create("positive-t-finite-modes-has-sum"),
                DeclarationHandle.Create(Prefix + "positiveT_hasSum"),
                H("Sum of the finite candidate modes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For real 0 < r < 1 and complex u and v with ‖u‖ + √r < 1 and "
                        + "‖v‖ + √r < 1, the family t(p,q,(r : ℂ)) u^p v^q indexed by ℕ × ℕ has sum "
                        + "OriginalGaussianExternalAnalyticCandidate.candidateT(u,v,(r : ℂ)). "
                        + "Here t is the complete coefficient from OriginalGaussianFiniteCandidateModes, "
                        + "including the logarithmic period correction.")),
                    Paragraph(Text("The binomial estimates bound the two denominator families by a "
                        + "polynomial in the indices times (1 + √r)^(p+q). With the source weights, "
                        + "the two geometric ratios ‖u‖(1 + √r) and ‖v‖(1 + √r) are less than one. "
                        + "Summing the inverse stencils gives E(u,v,r) times the first sum equal to one "
                        + "and E(u,v,r) times the second sum equal to the first. This proves E ≠ 0 "
                        + "and identifies the sums as 1/E and 1/E². The rectangular Cauchy product "
                        + "with the two positive source generators and subtraction of the period term "
                        + "give the stated candidate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-t-original-generator-equality"),
                DeclarationHandle.Create(Prefix + "positiveT_eq_candidateT"),
                H("Equality for the literal positive T kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For real 0 < r < 1 and complex u and v with ‖u‖ + √r < 1 and "
                        + "‖v‖ + √r < 1, the original kernelMode(true,true,true,u,v,(√r : ℂ)) equals "
                        + "OriginalGaussianExternalAnalyticCandidate.candidateT(u,v,(r : ℂ)). "
                        + "The three true flags select the square resolvent and both positive source labels.")),
                    Paragraph(Text("For each p and q, OriginalGaussianFinitePositiveGerm."
                        + "externalT_positive_finite_germ gives equality between the literal positive "
                        + "externalT mode and the finite candidate near zero. Analyticity of both "
                        + "functions gives equality on the complex unit disk by "
                        + "AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq. At z = (√r : ℂ), "
                        + "z² = (r : ℂ), so this mode equality identifies every term of the literal "
                        + "kernel sum with the corresponding term of positiveT_hasSum, which evaluates the sum."))),
                DescribeRole.Theorem))));
}
