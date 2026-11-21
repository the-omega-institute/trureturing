using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming.Families;

internal sealed class HeawoodConnectedCoverParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");

    private static DocumentBlock Node(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete binary-lift parameter dichotomy", H("The complete binary-lift parameter dichotomy"),
        Blocks(
            Paragraph(Text(
                "The six similarity types N1, N2, S, J, C and K reduce to the same matching construction. " +
                "Their ordered bases have Fano labels (2, 4, 1) for N1, (4, 1, 2) for N2 and (1, 4, 2) for the other four. " +
                "The pairs (u, v) in these bases are (0, 0), (0, 0), (0, 1), (0, 1), (0, 0) and (1, 0). " +
                "Every pair enables an additional line, so the matching gives beta at least fifteen. " +
                "The star-forming maximum is sixteen for every signing and bounds beta above. " +
                "Disconnected signings have beta fourteen. The bound leaves the exact values for N1, N2, C and K open here.")),
            Node("connected_beta", "Dissociation bounds for connected lifts",
                "Every connected binary lift of the Heawood graph has beta between fifteen and sixteen."),
            Node("parameters", "The complete dichotomy",
                "Every binary lift of the Heawood graph has SF equal to sixteen. Its beta is fourteen exactly when " +
                "the lift is disconnected. A connected lift has beta fifteen or sixteen and gap at most one.")), []));
}
