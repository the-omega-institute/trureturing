using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourPointChartGluingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic Gluing of the Four-Point Charts.",
        H("Analytic Gluing of the Four-Point Charts"),
        Blocks(
            Describe.Lean(DescribeId.Create("u-a-union-u-b"),
                DeclarationHandle.Create(Prefix + "U_A_union_U_B"),
                H("The two-chart cover"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The A and B chart domains cover the plane with zero and one removed. "
                    + "Their intersection is the connected double slit."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-gluing"),
                DeclarationHandle.Create(Prefix + "exists_gluing"),
                H("A/B gluing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A frequent equality at one interior point of the overlap extends throughout the overlap by the identity principle. "
                    + "The two holomorphic restrictions then define a single holomorphic function on the punctured plane."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-common-four-point-germ"),
                DeclarationHandle.Create(Prefix + "exists_common_four_point_germ"),
                H("Three punctured germs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A second interior accumulation of equalities compares the D chart with either A or B and identifies its restriction. "
                    + "The three native local equalities give the germs at one, zero, and inverse zero. "
                    + "A is reflected and B carries the factor 2¹²zᵏ."))),
                DescribeRole.Theorem))));
}
