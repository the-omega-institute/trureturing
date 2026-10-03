using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicRoyalEncodingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalEncoding.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Upsteps and downsteps select the two occurrence orders of a doubled word.",
        H("Interleaving Along a Step Sequence"),
        Blocks(
            Node("nonnesting-nonnestingbasicroyalencoding-weave", "Interleaving two lists", "weave",
                "Traverse a step sequence, taking the next letter of the first list at each upstep and the next letter of the second list at each downstep. The interleaving is defined exactly when the traversal consumes both lists and the entire step sequence.", DescribeRole.Definition),
            Node("nonnesting-nonnestingbasicroyalencoding-select", "Selection by step type", "select",
                "Traverse a step sequence and a letter list together, retaining precisely the letters paired with the chosen step type and stopping when either list is exhausted.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
