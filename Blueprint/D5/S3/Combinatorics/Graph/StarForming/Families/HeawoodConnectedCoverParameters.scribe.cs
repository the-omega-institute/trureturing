using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming.Families;

internal sealed class HeawoodConnectedCoverParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete binary-lift parameter dichotomy", H("The complete binary-lift parameter dichotomy"),
        Blocks(Paragraph(Text("The six original fifteen-sets transport to every connected signing, giving beta fifteen or sixteen. Disconnected signings have beta fourteen. The exact beta values of the other four types and higher-cover optima remain open in this development.")),
            Node("sixIso", "sixIso", "Exact declaration: def sixIso (k : Fin 6) : graph (HeawoodActions.representative k) ≃g HeawoodCertificates.sixGraph k.", DescribeRole.Definition),
            Node("connected_beta", "connected beta", "Exact declaration: theorem connected_beta (s : Signing) (hs : (graph s).Preconnected) : 15 ≤ beta (graph s) 2 ∧ beta (graph s) 2 ≤ 16.", DescribeRole.Theorem),
            Node("parameters", "parameters", "Exact declaration: theorem parameters (s : Signing) : SF (graph s) 2=16 ∧ (beta (graph s) 2=14 ↔ ¬ (graph s).Preconnected) ∧ ((graph s).Preconnected → (beta (graph s) 2=15 ∨ beta (graph s) 2=16) ∧ SF (graph s) 2-beta (graph s) 2≤1).", DescribeRole.Theorem)), []));
}
