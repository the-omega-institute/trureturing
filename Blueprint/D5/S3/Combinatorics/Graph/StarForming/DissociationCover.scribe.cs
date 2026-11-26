using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class DissociationCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/DissociationCover.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dissociation under local covers and square exclusions", H("Dissociation under local covers and square exclusions"),
        Blocks(Paragraph(Text("Local injectivity alone pulls back induced maximum degree at most one. Reflection additionally requires explicit global projection-surjectivity. A four-cycle cannot have any three consecutive vertices selected in a dissociation set. The square exclusion is a graph lemma, not a complete weighted-capacity certificate or a theorem equating SF with beta.")),
            Node("Dissociates", "Dissociates", "Exact declaration: def Dissociates {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) : Prop.", DescribeRole.Definition),
            Node("dissociates_pullback", "dissociates pullback", "Exact declaration: theorem dissociates_pullback {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) {selection : Base → Prop} (hdissociates : Dissociates baseAdjacency selection) : Dissociates liftAdjacency (fun vertex => selection (projection vertex)).", DescribeRole.Theorem),
            Node("dissociates_of_pullback", "dissociates of pullback", "Exact declaration: theorem dissociates_of_pullback {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) (hsurjective : ∀ vertex, ∃ lifted, projection lifted = vertex) {selection : Base → Prop} (hdissociates : Dissociates liftAdjacency (fun vertex => selection (projection vertex))) : Dissociates baseAdjacency selection.", DescribeRole.Theorem),
            Node("dissociates_pullback_iff", "dissociates pullback iff", "Exact declaration: theorem dissociates_pullback_iff {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) (hsurjective : ∀ vertex, ∃ lifted, projection lifted = vertex) {selection : Base → Prop} : Dissociates liftAdjacency (fun vertex => selection (projection vertex)) ↔ Dissociates baseAdjacency selection.", DescribeRole.Theorem),
            Node("four_cycle_excludes_triples", "four cycle excludes triples", "Exact declaration: theorem four_cycle_excludes_triples {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hdissociates : Dissociates adjacency selection) (first second third fourth : Vertex) (hfirstThird : first ≠ third) (hsecondFourth : second ≠ fourth) (hfirstSecond : adjacency first second) (hsecondThird : adjacency second third) (hthirdFourth : adjacency third fourth) (hfourthFirst : adjacency fourth first) : ¬ (selection first ∧ selection second ∧ selection third) ∧ ¬ (selection second ∧ selection third ∧ selection fourth) ∧ ¬ (selection third ∧ selection fourth ∧ selection first) ∧ ¬ (selection fourth ∧ selection first ∧ selection second).", DescribeRole.Theorem)), []));
}
