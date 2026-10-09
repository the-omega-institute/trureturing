using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LocalDominatingStemBoundOmissionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Omitting a stem forces every one of its leaves and full internal domination of the residual graph.",
        H("Dominating sets omitting a stem"),
        Blocks(
            Node("omitted-stem-residual", "Internal residual domination", "omitted_stem_residual",
                "Selected leaves can dominate only themselves and the omitted stem, so residual vertices must be dominated internally.", DescribeRole.Theorem),
            Node("omitted-family-card", "Omitted-family size", "omitted_family_card",
                "Adjoining all leaf neighbours gives a bijection from residual dominating sets to dominating sets omitting the stem.", DescribeRole.Theorem),
            Node("omitted-card-sum", "Omitted-family cardinality sum", "omitted_card_sum",
                "Every omitted-stem set has all leaf neighbours and a disjoint residual dominating set.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
