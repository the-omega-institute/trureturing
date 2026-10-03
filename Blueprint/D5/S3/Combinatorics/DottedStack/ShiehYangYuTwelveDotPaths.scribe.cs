using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DottedStack;

internal sealed class ShiehYangYuTwelveDotPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotPaths.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/yangshiehyu2025dotted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Colored Dyck excursions correspond bijectively to balanced words of up and down steps.",
        H("Signed Excursions and Balanced Bridges"),
        Blocks(
            Node("syy-twelve-dot-bridge-first-return-theorem", "The first return of an upward bridge", "bridge_first_return",
                "For every balanced word of up and down steps beginning with an up step, "
                + "there is a unique pair consisting of a Dyck path and a balanced suffix "
                + "such that the word is that path enclosed between an up step and a down "
                + "step, followed by the suffix. Balanced means that the numbers of up and "
                + "down steps are equal; no nonnegativity condition is imposed on the "
                + "suffix. The enclosed prefix ends at the first return to height zero.",
                DescribeRole.Theorem),
            Node("syy-twelve-dot-signed-bridge-equivalence-definition", "Reflect colored excursions", "signed_bridge_equiv",
                "For every natural number m, signed_bridge_equiv is a bijection from finite "
                + "lists of pairs consisting of a Boolean color and a Dyck path, with the "
                + "sum of the path semilengths plus one for each pair equal to m, to words "
                + "with exactly m up steps and m down steps. Each path is enclosed between "
                + "an up step and a down step. A false color leaves this excursion unchanged; "
                + "a true color exchanges all up and down steps. Concatenating these signed "
                + "excursions gives the bridge. The inverse splits at successive returns "
                + "to height zero, reflects excursions that begin with a down step, and "
                + "removes the enclosing steps.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
