using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SubcubicIdentificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual shared-port subcubic assemblies", H("Actual shared-port subcubic assemblies"),
        Blocks(Paragraph(Text("The actual vertex type has ten core vertices and one identified port per cell. Source port zero maps to the current port and source port six to the next port. Degrees and the ambient-core upper bound concern this graph, with each port counted once. The explicit seven-per-cell minimal selection attains SF. Even-cycle dissociation, structural and other graph invariants require their own proofs.")),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors (next : Equiv.Perm I) (x : I × Fin 11) : List (I × Fin 11).", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph (next : Equiv.Perm I) : SimpleGraph (I × Fin 11).", DescribeRole.Definition),
            Node("degrees", "degrees", "Exact declaration: theorem degrees (next : Equiv.Perm I) (i : I) (v : Fin 11) : DegreeCapacity.degree (graph next) (i,v)= if v=3 ∨ v=4 ∨ v=6 ∨ v=7 ∨ v=10 then 2 else 3.", DescribeRole.Theorem),
            Node("core", "core", "Exact declaration: def core (i : I) (v : Fin 10) : I × Fin 11.", DescribeRole.Definition),
            Node("port", "port", "Exact declaration: def port (i : I) : I × Fin 11.", DescribeRole.Definition),
            Node("coreSlice", "coreSlice", "Exact declaration: def coreSlice (S : Finset (I × Fin 11)) (i : I) : Finset (Fin 10).", DescribeRole.Definition),
            Node("slice", "slice", "Exact declaration: def slice (S : Finset (I × Fin 11)) (i : I) : Finset (Fin 11).", DescribeRole.Definition),
            Node("core_edges", "core edges", "Exact declaration: theorem core_edges (next : Equiv.Perm I) (i : I) (v w : Fin 10) : (graph next).Adj (core i v) (core i w) ↔ Subcubic.CoreAdj v w.", DescribeRole.Theorem),
            Node("card_slice", "card slice", "Exact declaration: theorem card_slice (S : Finset (I × Fin 11)) (i : I) : (slice S i).card=(coreSlice S i).card+(if port i∈S then 1 else 0).", DescribeRole.Theorem),
            Node("sf_upper", "sf upper", "Exact declaration: theorem sf_upper (next : Equiv.Perm I) : SF (graph next) 2≤7*Fintype.card I.", DescribeRole.Theorem),
            Node("forming", "forming", "Exact declaration: def forming (x : I × Fin 11) : Prop.", DescribeRole.Definition),
            Node("failure", "failure", "Exact declaration: def failure (x : I × Fin 11) : I × Fin 11.", DescribeRole.Definition),
            Node("forming_minimal", "forming minimal", "Exact declaration: theorem forming_minimal (next : Equiv.Perm I) : IsMinimalStarForming (graph next) 2 (Finset.univ.filter forming).", DescribeRole.Theorem),
            Node("sf_exact", "sf exact", "Exact declaration: theorem sf_exact (next : Equiv.Perm I) : SF (graph next) 2=7*Fintype.card I.", DescribeRole.Theorem)), []));
}
