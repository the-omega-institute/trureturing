using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMBivariateInverseJetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMBivariateInverseJets.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bivariate inverse jets at the four punctures",
        H("Independent inverse substitution"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-four-m-bivariate-inverse-jets-pair-coefficient"),
                DeclarationHandle.Create(Prefix + "coefficient_comp_pair_div_jac"),
                H("Inverse jet weights on both endpoints"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a complex function analytic at the origin in two variables and a real chart argument "
                    + "between zero and one, take arbitrary spatial degrees at two punctures. The iterated Taylor "
                    + "coefficient after inverse substitution and division by the two half-Jacobians is a finite "
                    + "double sum. Each native Taylor entry is multiplied by the inverse jet weight of each "
                    + "endpoint."))),
                DescribeRole.Theorem))));
}
