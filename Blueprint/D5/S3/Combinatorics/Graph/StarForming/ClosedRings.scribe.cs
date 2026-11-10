using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class ClosedRingsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/ClosedRings.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact parameters of arbitrary finite closed-high rings", H("Exact parameters of arbitrary finite closed-high rings"),
        Blocks(Paragraph(Text("A permutation on an arbitrary finite index type links the actual sixty-two-vertex modules. Slice accounting gives beta thirty-three per module; actual attaining selections and outside-only rewiring give SF thirty-six per module. The graph is cubic bipartite, including the empty family and singleton restoration. Connectivity and one-vertex-deletion connectivity require their own orbit argument and are not supplied by the parameter equalities.")),
            Node("graph", "graph", "Exact declaration: def graph (e : Equiv.Perm I) : SimpleGraph (I × Fin 62).", DescribeRole.Definition),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors (e : Equiv.Perm I) (v : I × Fin 62) : List (I × Fin 62).", DescribeRole.Definition),
            Node("regular", "regular", "Exact declaration: theorem regular (e : Equiv.Perm I) : ∀ v, DegreeCapacity.degree (graph e) v=3.", DescribeRole.Theorem),
            Node("bipartite", "bipartite", "Exact declaration: theorem bipartite (e : Equiv.Perm I) : (graph e).Colorable 2.", DescribeRole.Theorem),
            Node("slice", "slice", "Exact declaration: def slice (S : Finset (I × Fin 62)) (i : I) : Finset (Fin 62).", DescribeRole.Definition),
            Node("beta_upper", "beta upper", "Exact declaration: theorem beta_upper (e : Equiv.Perm I) : beta (graph e) 2≤33*Fintype.card I.", DescribeRole.Theorem),
            Node("beta_lower", "beta lower", "Exact declaration: theorem beta_lower (e : Equiv.Perm I) : 33*Fintype.card I≤beta (graph e) 2.", DescribeRole.Theorem),
            Node("sf_lower", "sf lower", "Exact declaration: theorem sf_lower (e : Equiv.Perm I) : 36*Fintype.card I≤SF (graph e) 2.", DescribeRole.Theorem),
            Node("parameters", "parameters", "Exact declaration: theorem parameters (e : Equiv.Perm I) : Fintype.card (I × Fin 62)=62*Fintype.card I ∧ beta (graph e) 2=33*Fintype.card I ∧ SF (graph e) 2=36*Fintype.card I ∧ SF (graph e) 2-beta (graph e) 2=3*Fintype.card I.", DescribeRole.Theorem)), []));
}
