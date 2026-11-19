using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class ClosedRingWitnessesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual module selections and deletion failures", H("Actual module selections and deletion failures"),
        Blocks(Paragraph(Text("The original thirty-six forming selection has explicit deletion failures. The displayed thirty-three dissociation selection, local bipartition and open-port states are kernel checked. These are local certificate inputs to the arbitrary finite symbolic assembly, not a finite enumeration of ring orders.")),
            Node("forming", "forming", "Exact declaration: def forming (v : Fin 62) : Prop.", DescribeRole.Definition),
            Node("failure", "failure", "Exact declaration: def failure (v : Fin 62) : Fin 62.", DescribeRole.Definition),
            Node("independent", "independent", "Exact declaration: def independent (v : Fin 62) : Prop.", DescribeRole.Definition),
            Node("forming_certificates", "forming certificates", "Exact declaration: theorem forming_certificates : Regular.Minimal graph.Adj forming ∧ (Finset.univ.filter forming).card=36.", DescribeRole.Theorem),
            Node("independent_certificates", "independent certificates", "Exact declaration: theorem independent_certificates : DissociationCover.Dissociates graph.Adj independent ∧ (Finset.univ.filter independent).card=33.", DescribeRole.Theorem),
            Node("color", "color", "Exact declaration: def color (v : Fin 62) : Fin 2.", DescribeRole.Definition),
            Node("local_class", "local class", "Exact declaration: theorem local_class : (∀ v w : Fin 62, graph.Adj v w → color v≠color w) ∧ (∀ v : Fin 62, (neighbors v).Nodup) ∧ (∀ v : Fin 62, (neighbors v).length=if v=12 ∨ v=17 then 2 else 3).", DescribeRole.Theorem),
            Node("interface_states", "interface states", "Exact declaration: theorem interface_states : ¬ forming 12 ∧ ¬ forming 17 ∧ independent 12 ∧ ¬ independent 17 ∧ color 12=0 ∧ color 17=1.", DescribeRole.Theorem)), []));
}
