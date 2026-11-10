using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class PortReturnDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/PortReturn.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direct split and relay returns", H("Direct split and relay returns"),
        Blocks(Paragraph(Text("A deletion failure is exactly one of the Direct, Split or Relay shapes defined here. Protected high ports have a return witness; that witness is unique and excludes another high vertex touching the same return. The proof keeps all adjacency, selected-neighbor and symmetry conditions. It does not assert that every signal forces a positive Heawood block loss.")),
            Node("OnlyNeighbor", "OnlyNeighbor", "Exact declaration: def OnlyNeighbor {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (vertex neighbor : Vertex) : Prop.", DescribeRole.Definition),
            Node("FailureShape", "FailureShape", "Exact declaration: def FailureShape {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted outside : Vertex) : Prop.", DescribeRole.Definition),
            Node("failure_iff_shapes", "failure iff shapes", "Exact declaration: theorem failure_iff_shapes {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hforms : Forms adjacency selection) (deleted outside : Vertex) (hselected : selection deleted) (houtside : ¬ selection outside) : Failure adjacency selection deleted outside ↔ FailureShape adjacency selection deleted outside.", DescribeRole.Theorem),
            Node("protected_port_returns", "protected port returns", "Exact declaration: theorem protected_port_returns {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection block core : Vertex → Prop) (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hminimal : Minimal adjacency selection) (port exit : Vertex) (hhigh : High adjacency selection port) (hexit : core exit) (hboundary : ∀ neighbor, adjacency port neighbor → ¬ block neighbor → neighbor = exit) (hprotectedOmitted : ∀ outside, block outside → ¬ selection outside → adjacency outside port → TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ port) outside) (hprotectedSelected : ∀ neighbor, block neighbor → selection neighbor → adjacency port neighbor → ∃ replacement, selection replacement ∧ replacement ≠ port ∧ adjacency neighbor replacement) (hexitNeighbors : ∀ vertex, adjacency exit vertex → vertex ≠ port → core vertex) : ∃ outside, core outside ∧ Failure adjacency selection port outside ∧ (outside = exit ∨ (¬ adjacency outside port ∧ OnlyNeighbor adjacency selection outside exit ∧ OnlyNeighbor adjacency selection exit port)).", DescribeRole.Theorem),
            Node("return_witness_unique", "return witness unique", "Exact declaration: theorem return_witness_unique {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hforms : Forms adjacency selection) (first second outside : Vertex) (hfirst : High adjacency selection first) (hsecond : High adjacency selection second) (hfailureFirst : Failure adjacency selection first outside) (hfailureSecond : Failure adjacency selection second outside) : first = second.", DescribeRole.Theorem),
            Node("other_high_cannot_touch_return", "other high cannot touch return", "Exact declaration: theorem other_high_cannot_touch_return {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (port other outside : Vertex) (hdifferent : other ≠ port) (hhigh : High adjacency selection other) (hfailure : Failure adjacency selection port outside) : ¬ adjacency outside other.", DescribeRole.Theorem)), []));
}
