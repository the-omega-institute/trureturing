using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class TripleRingsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/TripleRings.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-size triple-port ring parameters", H("All-size triple-port ring parameters"),
        Blocks(Paragraph(Text("For every finite index permutation, including empty and singleton cases, the actual forty-eight-vertex fibers joined at ports sixteen and seventeen form a cubic bipartite graph with beta two equal to twenty-six per fiber and SF two equal to twenty-eight per fiber. The original attaining selections and exact finite fiber counts supply both lower bounds; the regular compensation upper bound supplies SF. Connectivity is proved separately.")),
            Node("graph", "graph", "Exact declaration: def graph (e : Equiv.Perm I) : SimpleGraph (I × Fin 48).", DescribeRole.Definition),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors (e : Equiv.Perm I) (v : I × Fin 48) : List (I × Fin 48).", DescribeRole.Definition),
            Node("regular", "regular", "Exact declaration: theorem regular (e : Equiv.Perm I) : ∀ v, DegreeCapacity.degree (graph e) v=3.", DescribeRole.Theorem),
            Node("bipartite", "bipartite", "Exact declaration: theorem bipartite (e : Equiv.Perm I) : (graph e).Colorable 2.", DescribeRole.Theorem),
            Node("slice", "slice", "Exact declaration: def slice (S : Finset (I × Fin 48)) (i : I) : Finset (Fin 48).", DescribeRole.Definition),
            Node("beta_upper", "beta upper", "Exact declaration: theorem beta_upper (e : Equiv.Perm I) : beta (graph e) 2≤26*Fintype.card I.", DescribeRole.Theorem),
            Node("beta_lower", "beta lower", "Exact declaration: theorem beta_lower (e : Equiv.Perm I) : 26*Fintype.card I≤beta (graph e) 2.", DescribeRole.Theorem),
            Node("sf_lower", "sf lower", "Exact declaration: theorem sf_lower (e : Equiv.Perm I) : 28*Fintype.card I≤SF (graph e) 2.", DescribeRole.Theorem),
            Node("parameters", "parameters", "Exact declaration: theorem parameters (e : Equiv.Perm I) : Fintype.card (I × Fin 48)=48*Fintype.card I ∧ beta (graph e) 2=26*Fintype.card I ∧ SF (graph e) 2=28*Fintype.card I ∧ SF (graph e) 2-beta (graph e) 2=2*Fintype.card I.", DescribeRole.Theorem)), []));
}
