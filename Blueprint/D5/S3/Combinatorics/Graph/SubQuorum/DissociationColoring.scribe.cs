using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubQuorum;

internal sealed class DissociationColoringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dissociation and injective partial colorings", H("Dissociation and injective partial colorings"),
        Blocks(Paragraph(Text("For any finite simple graph and any partial coloring injective on its actual support, the sub-quorum majority condition is equivalent to that support inducing maximum degree at most one. Each actual dissociation set therefore yields a coloring with exactly its cardinality many distinct represented natural colors; attainment gives beta two at most psi square. Empty graphs and empty supports are included. This does not provide the opposite representative-packing bound or identify SF with the coloring parameter.")),
            Node("injective_support_iff", "injective support iff", "Exact declaration: theorem injective_support_iff (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Option C) (hi : Set.InjOn c (coloredSupport c Finset.univ)) : IsSubQuorum G c ↔ IsKIndependent G 2 (coloredSupport c Finset.univ).", DescribeRole.Theorem),
            Node("distinct_support", "distinct support", "Exact declaration: theorem distinct_support (S : Finset V) : coloredSupport (distinctColoring S) Finset.univ = S.", DescribeRole.Theorem),
            Node("distinct_injective", "distinct injective", "Exact declaration: theorem distinct_injective (S : Finset V) : Set.InjOn (distinctColoring S) (coloredSupport (distinctColoring S) Finset.univ).", DescribeRole.Theorem),
            Node("distinct_palette", "distinct palette", "Exact declaration: theorem distinct_palette (S : Finset V) : (palette (distinctColoring S) Finset.univ).card = S.card.", DescribeRole.Theorem),
            Node("palette_le_psiSq", "palette le psiSq", "Exact declaration: theorem palette_le_psiSq (G : SimpleGraph V) (c : V → Option ℕ) (h : IsSubQuorum G c) : (palette c Finset.univ).card ≤ psiSq G.", DescribeRole.Theorem),
            Node("beta_le_psiSq", "beta le psiSq", "Exact declaration: theorem beta_le_psiSq (G : SimpleGraph V) [DecidableRel G.Adj] : beta G 2 ≤ psiSq G.", DescribeRole.Theorem)), []));
}
