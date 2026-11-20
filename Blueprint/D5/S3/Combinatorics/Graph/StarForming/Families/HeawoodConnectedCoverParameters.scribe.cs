using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming.Families;

internal sealed class HeawoodConnectedCoverParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(
            "The six similarity types N1, N2, S, J, C and K reduce to the same matching construction. " +
            "Their ordered bases have Fano labels (2, 4, 1) for N1, (4, 1, 2) for N2 and (1, 4, 2) for the other four. " +
            "The pairs (u, v) in these bases are (0, 0), (0, 0), (0, 1), (0, 1), (0, 0) and (1, 0). " +
            "Every pair enables an additional line, so the matching gives beta at least fifteen. " +
            "The star-forming maximum is sixteen for every signing and bounds beta above. " +
            "Disconnected signings have beta fourteen.")),
            Node("connected_beta", "connected beta", "Exact declaration: theorem connected_beta (s : Signing) (hs : (graph s).Preconnected) : 15 ≤ beta (graph s) 2 ∧ beta (graph s) 2 ≤ 16.", DescribeRole.Theorem),
            Node("parameters", "parameters", "Exact declaration: theorem parameters (s : Signing) : SF (graph s) 2=16 ∧ (beta (graph s) 2=14 ↔ ¬ (graph s).Preconnected) ∧ ((graph s).Preconnected → (beta (graph s) 2=15 ∨ beta (graph s) 2=16) ∧ SF (graph s) 2-beta (graph s) 2≤1).", DescribeRole.Theorem)), []));
}
