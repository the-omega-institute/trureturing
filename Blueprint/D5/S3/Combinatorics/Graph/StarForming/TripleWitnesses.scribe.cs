using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class TripleWitnessesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original triple-port forming and dissociation witnesses", H("Original triple-port forming and dissociation witnesses"),
        Blocks(Paragraph(Text("The original selected twenty-eight-set, actual deletion failures, dissociation twenty-six-set and bipartition are checked on the forty-eight-vertex open module. Both seam vertices are unselected in the forming witness; only the even seam vertex belongs to the dissociation witness.")),
            Node("forming", "forming", "Exact declaration: def forming (v : Fin 48) : Prop.", DescribeRole.Definition),
            Node("failure", "failure", "Exact declaration: def failure (v : Fin 48) : Fin 48.", DescribeRole.Definition),
            Node("independent", "independent", "Exact declaration: def independent (v : Fin 48) : Prop.", DescribeRole.Definition),
            Node("forming_certificates", "forming certificates", "Exact declaration: theorem forming_certificates : Regular.Minimal graph.Adj forming ∧ (Finset.univ.filter forming).card=28.", DescribeRole.Theorem),
            Node("independent_certificates", "independent certificates", "Exact declaration: theorem independent_certificates : DissociationCover.Dissociates graph.Adj independent ∧ (Finset.univ.filter independent).card=26.", DescribeRole.Theorem),
            Node("color", "color", "Exact declaration: def color (v : Fin 48) : Fin 2.", DescribeRole.Definition),
            Node("local_class", "local class", "Exact declaration: theorem local_class : (∀ v w : Fin 48, graph.Adj v w → color v≠color w) ∧ (∀ v : Fin 48, (neighbors v).Nodup) ∧ (∀ v : Fin 48, (neighbors v).length=if v=16 ∨ v=17 then 2 else 3).", DescribeRole.Theorem),
            Node("interface_states", "interface states", "Exact declaration: theorem interface_states : ¬ forming 16 ∧ ¬ forming 17 ∧ independent 16 ∧ ¬ independent 17 ∧ color 16=0 ∧ color 17=1.", DescribeRole.Theorem)), []));
}
