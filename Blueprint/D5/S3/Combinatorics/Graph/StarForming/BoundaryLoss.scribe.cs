using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class BoundaryLossDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/BoundaryLoss.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exported private-clause ownership", H("Exported private-clause ownership"),
        Blocks(Paragraph(Text("An unsupported selected nonport in a port-only ambient block has a witness beyond a selected port. The ExportWitness records the actual omitted external vertex, the selected port, its sole selected internal neighbor and the ambient deletion failure. Distinct exported owners cannot reuse that witness under the displayed hypotheses. No arithmetic block-loss or global no-reuse theorem is inferred without its additional graph counts.")),
            Node("ExportWitness", "ExportWitness", "Exact declaration: def ExportWitness {Vertex : Type} (inside ambient : Vertex → Vertex → Prop) (core port selection : Vertex → Prop) (candidate boundary outside : Vertex) : Prop.", DescribeRole.Definition),
            Node("unsupported_has_export", "unsupported has export", "Exact declaration: theorem unsupported_has_export {Vertex : Type} (inside ambient : Vertex → Vertex → Prop) (core port selection : Vertex → Prop) (hinclusion : ∀ first second, inside first second → ambient first second) (hinside : ∀ first second, inside first second → core first ∧ core second) (hsymmInside : ∀ first second, inside first second → inside second first) (hsymmAmbient : ∀ first second, ambient first second → ambient second first) (hunchanged : ∀ vertex, core vertex → ¬ port vertex → ∀ neighbor, ambient vertex neighbor → inside vertex neighbor) (hminimal : Minimal ambient selection) (candidate : Vertex) (hcore : core candidate) (hnonport : ¬ port candidate) (hselected : selection candidate) (hunsupported : ¬ ∃ clause, Private inside (fun vertex => core vertex ∧ selection vertex) clause candidate) : ∃ boundary outside, ExportWitness inside ambient core port selection candidate boundary outside.", DescribeRole.Theorem),
            Node("exported_owner_unique", "exported owner unique", "Exact declaration: theorem exported_owner_unique {Vertex : Type} (inside ambient : Vertex → Vertex → Prop) (core port selection : Vertex → Prop) (first second firstBoundary secondBoundary outside : Vertex) (hfirst : ExportWitness inside ambient core port selection first firstBoundary outside) (hsecond : ExportWitness inside ambient core port selection second secondBoundary outside) (hcore : core second) (hselected : selection second) : first = second.", DescribeRole.Theorem)), []));
}
