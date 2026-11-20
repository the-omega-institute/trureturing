using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubQuorum;

internal sealed class PappusRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SubQuorum/PappusRigidity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pappus representative and coloring rigidity", H("Pappus representative and coloring rigidity"),
        Blocks(Paragraph(Text("A feasible singleton and matching pair of total size ten has an empty matching. Every ten-color Pappus sub-quorum coloring has a ten-vertex dissociation support and is injective on that support.")),
            Node("pappus_optimal_matching_empty", "pappus optimal matching empty", "Exact declaration: theorem pappus_optimal_matching_empty (T : Finset (Fin 18)) (M : Finset (Fin 18 × Fin 18)) (hf : Feasible pappusGraph T M) (hc : T.card + M.card = 10) : M = ∅.", DescribeRole.Theorem),
            Node("pappus_coloring_rigidity", "pappus coloring rigidity", "Exact declaration: theorem pappus_coloring_rigidity (c : Fin 18 → Option ℕ) (hc : IsSubQuorum pappusGraph c) (hp : (palette c Finset.univ).card = 10) : IsKIndependent pappusGraph 2 (coloredSupport c Finset.univ) ∧ (coloredSupport c Finset.univ).card = 10 ∧ Set.InjOn c (coloredSupport c Finset.univ).", DescribeRole.Theorem)), []));
}
