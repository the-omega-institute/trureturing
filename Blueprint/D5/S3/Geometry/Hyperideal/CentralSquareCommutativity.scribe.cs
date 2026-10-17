using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CentralSquareCommutativityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A central square-return word forces the two generators to commute.",
        H("Central square commutativity"),
        Blocks(
            Paragraph(Text("Let G be a group and let u,v be elements of G. If the element "
                + "v inverse times u squared commutes with every element of G, then u and v "
                + "commute. The proof applies centrality to u, cancels the common right factor "
                + "u squared, and multiplies the resulting equality by v on the left and right.")),
            Describe.Lean(
                DescribeId.Create("central-v-inv-square-implies-commute"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/CentralSquareCommutativity.central_v_inv_sq_implies_commute"),
                H("Central square-return commutativity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every group G and u,v in G, if v inverse times u squared "
                    + "is central, then u times v equals v times u."))),
                DescribeRole.Theorem))));
}
