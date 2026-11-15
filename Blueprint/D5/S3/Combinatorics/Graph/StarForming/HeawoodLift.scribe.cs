using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All Heawood signings and connectivity", H("All Heawood signings and connectivity"),
        Blocks(Paragraph(Text("The twenty-one binary Fano flags define the actual fourteen-vertex graph and binary lift. The linear invariant vanishes exactly for vertex coboundaries on that graph. Equal invariants give sheet-switching graph isomorphisms, and connectedness is equivalent to a nonzero invariant.")),
            Node("Vertex", "Vertex", "Exact declaration: abbrev Vertex.", DescribeRole.Definition),
            Node("point", "point", "Exact declaration: def point (e : Fin 21) : Vertex.", DescribeRole.Definition),
            Node("line", "line", "Exact declaration: def line (e : Fin 21) : Vertex.", DescribeRole.Definition),
            Node("incident", "incident", "Exact declaration: def incident (e : Fin 21) (v w : Vertex) : Prop.", DescribeRole.Definition),
            Node("base", "base", "Exact declaration: def base : SimpleGraph Vertex.", DescribeRole.Definition),
            Node("edgeIndex", "edgeIndex", "Exact declaration: def edgeIndex (v w : Vertex) : Fin 21.", DescribeRole.Definition),
            Node("base_preconnected", "base preconnected", "Exact declaration: theorem base_preconnected : base.Preconnected.", DescribeRole.Theorem),
            Node("voltage", "voltage", "Exact declaration: def voltage (s : Signing) : BinaryLift.Voltage base.", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: abbrev graph (s : Signing).", DescribeRole.Definition),
            Node("coboundary_iff", "coboundary iff", "Exact declaration: theorem coboundary_iff (s : Signing) : (∃ t : Switches, ∀ v w, base.Adj v w → s (edgeIndex v w)=t v+t w) ↔ phi s=0.", DescribeRole.Theorem),
            Node("preconnected_iff", "preconnected iff", "Exact declaration: theorem preconnected_iff (s : Signing) : (graph s).Preconnected ↔ phi s≠0.", DescribeRole.Theorem),
            Node("isomorphic_of_phi_eq", "isomorphic of phi eq", "Exact declaration: theorem isomorphic_of_phi_eq (s t : Signing) (h : phi s=phi t) : Nonempty (graph s ≃g graph t).", DescribeRole.Theorem),
            Node("signingOfVoltage", "signingOfVoltage", "Exact declaration: def signingOfVoltage (s : BinaryLift.Voltage base) : Signing.", DescribeRole.Definition),
            Node("voltageIso", "voltageIso", "Exact declaration: def voltageIso (s : BinaryLift.Voltage base) : BinaryLift.graph base s ≃g graph (signingOfVoltage s).", DescribeRole.Definition)), []));
}
