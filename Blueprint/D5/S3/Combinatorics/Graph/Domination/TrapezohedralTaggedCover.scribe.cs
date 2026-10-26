using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TrapezohedralTaggedCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reversible classification of all labelled subsets", H("Reversible classification of all labelled subsets"), Blocks(
            Node("turn", "An actual graph automorphism", "turn", "Exchange alpha and beta, send a(i) to b(i), and send b(i) to a(i+1). The inverse sends a(i) to b(i-1) and b(i) to a(i). Both maps preserve exactly the original edge relation.", DescribeRole.Definition),
            Node("data", "Labelled cut covers", "CoverData", "A removed edge label j together with a minimal cover C of the remaining cyclic edges containing an endpoint. The tag and every label remain part of the data.", DescribeRole.Definition),
            Node("equivalence", "The complete apex encoding", "actualTaggedEquiv", "For every n>=3, the type of original admissible labelled subsets is equivalent to Bool times the dependent cut-cover family. The inverse reads the unique apex, unique opposite label, and selected same-type labels. Every tag decodes to an original minimal connected dominating subset. This theorem does not yet identify cut covers with ordered path covers or give the literal generating series.", DescribeRole.Definition)), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
