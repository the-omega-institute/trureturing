using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubQuorum;

internal sealed class HeawoodRepresentativesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Heawood representative instances", H("Heawood representative instances"),
        Blocks(Paragraph(Text("The cyclic-label Heawood graph has beta, psiSq and Omega seven and SF eight. The binary-label graph has an optimum with three singletons on each side and one matching edge. These finite positive certificates have no qualifying refutation basis under CLAUDE.md §3.3.")),
            Node("heawood_parameters", "heawood parameters", "Exact declaration: theorem heawood_parameters : beta HeawoodParameters.graph 2 = 7 ∧ psiSq HeawoodParameters.graph = 7 ∧ Omega HeawoodParameters.graph = 7 ∧ SF HeawoodParameters.graph 2 = 8.", DescribeRole.Theorem),
            Node("binaryHeawood", "binaryHeawood", "Exact declaration: def binaryHeawood : SimpleGraph (Fin 14).", DescribeRole.Definition),
            Node("mixedSingletons", "mixedSingletons", "Exact declaration: def mixedSingletons : Finset (Fin 14).", DescribeRole.Definition),
            Node("mixedMatching", "mixedMatching", "Exact declaration: def mixedMatching : Finset (Fin 14 × Fin 14).", DescribeRole.Definition),
            Node("mixed_support_optimum", "mixed support optimum", "Exact declaration: theorem mixed_support_optimum : Feasible binaryHeawood mixedSingletons mixedMatching ∧ mixedSingletons.card + mixedMatching.card = Omega binaryHeawood ∧ (mixedSingletons.filter (fun v => heawoodColor v = false)).card = 3 ∧ (mixedSingletons.filter (fun v => heawoodColor v = true)).card = 3.", DescribeRole.Theorem)), []));
}
