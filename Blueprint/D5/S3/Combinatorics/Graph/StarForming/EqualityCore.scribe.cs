using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class EqualityCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/EqualityCore.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual periodic cubic equality cores", H("Actual periodic cubic equality cores"),
        Blocks(Paragraph(Text("The actual twenty-vertex cell graph is defined for every finite index type and every index permutation, including fixed points and the empty family. Symbolic neighbor rows prove cubic regularity and a common bipartition. The H/U minimal selection and the explicit matching dissociation selection both have twelve vertices per cell. Global degree capacity and actual attainment prove beta and SF each equal twelve times the cell count. Cyclic connectivity, padding attachments and four-port ring losses are separate obligations.")),
            Node("edges", "edges", "Exact declaration: def edges : Finset (Fin 20 × Fin 20).", DescribeRole.Definition),
            Node("internal", "internal", "Exact declaration: abbrev internal (v w : Fin 20) : Prop.", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph (next : Equiv.Perm I) : SimpleGraph (I × Fin 20).", DescribeRole.Definition),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors (next : Equiv.Perm I) (x : I × Fin 20) : Finset (I × Fin 20).", DescribeRole.Definition),
            Node("mem_neighbors", "mem neighbors", "Exact declaration: theorem mem_neighbors (next : Equiv.Perm I) (x y : I × Fin 20) : y ∈ neighbors next x ↔ (graph next).Adj x y.", DescribeRole.Theorem),
            Node("regular", "regular", "Exact declaration: theorem regular (next : Equiv.Perm I) (x : I × Fin 20) : DegreeCapacity.degree (graph next) x = 3.", DescribeRole.Theorem),
            Node("color", "color", "Exact declaration: def color (v : Fin 20) : Bool.", DescribeRole.Definition),
            Node("bipartite", "bipartite", "Exact declaration: theorem bipartite (next : Equiv.Perm I) : (graph next).Colorable 2.", DescribeRole.Theorem),
            Node("selected", "selected", "Exact declaration: abbrev selected (v : Fin 20) : Prop.", DescribeRole.Definition),
            Node("dissociation", "dissociation", "Exact declaration: abbrev dissociation (v : Fin 20) : Prop.", DescribeRole.Definition),
            Node("S", "S", "Exact declaration: def S : Finset (I × Fin 20).", DescribeRole.Definition),
            Node("D", "D", "Exact declaration: def D : Finset (I × Fin 20).", DescribeRole.Definition),
            Node("D_valid", "D valid", "Exact declaration: theorem D_valid (next : Equiv.Perm I) : IsKIndependent (graph next) 2 D.", DescribeRole.Theorem),
            Node("S_minimal", "S minimal", "Exact declaration: theorem S_minimal (next : Equiv.Perm I) : IsMinimalStarForming (graph next) 2 S.", DescribeRole.Theorem),
            Node("selected_card", "selected card", "Exact declaration: theorem selected_card : (S : Finset (I × Fin 20)).card = 12 * Fintype.card I.", DescribeRole.Theorem),
            Node("dissociation_card", "dissociation card", "Exact declaration: theorem dissociation_card : (D : Finset (I × Fin 20)).card = 12 * Fintype.card I.", DescribeRole.Theorem),
            Node("exact_parameters", "exact parameters", "Exact declaration: theorem exact_parameters (next : Equiv.Perm I) : beta (graph next) 2 = 12 * Fintype.card I ∧ SF (graph next) 2 = 12 * Fintype.card I.", DescribeRole.Theorem)), []));
}
