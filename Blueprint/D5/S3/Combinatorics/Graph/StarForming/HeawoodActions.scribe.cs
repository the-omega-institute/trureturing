using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodActionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual coordinate relabelings and the six-type transfer", H("Actual coordinate relabelings and the six-type transfer"),
        Blocks(Paragraph(Text("The 168 coordinate permutations, their inverses and flag transport are actual graph automorphisms, checked in Lean. A complete finite traceless-matrix conjugator table and the symbolic switching-kernel theorem transport every nonzero signing to one of the original six actual types. The table concerns the complete fixed three-dimensional binary matrix domain; it is not sampling arbitrary cover orders.")),
            Node("vertexMap", "vertexMap", "Exact declaration: def vertexMap (g : Fin 168) : Fin 14 → Fin 14.", DescribeRole.Definition),
            Node("inverseIndex", "inverseIndex", "Exact declaration: def inverseIndex : Fin 168 → Fin 168.", DescribeRole.Definition),
            Node("flagMap", "flagMap", "Exact declaration: def flagMap (g : Fin 168) : Fin 21 → Fin 21.", DescribeRole.Definition),
            Node("automorphism", "automorphism", "Exact declaration: def automorphism (g : Fin 168) : base ≃g base.", DescribeRole.Definition),
            Node("pull", "pull", "Exact declaration: def pull (g : Fin 168) (s : Signing) : Signing.", DescribeRole.Definition),
            Node("liftIso", "liftIso", "Exact declaration: def liftIso (g : Fin 168) (s : Signing) : graph (pull g s) ≃g graph s.", DescribeRole.Definition),
            Node("representative", "representative", "Exact declaration: def representative (k : Fin 6) : Signing.", DescribeRole.Definition),
            Node("matrix", "matrix", "Exact declaration: def matrix (a : Fin 8 → F2) : Mat.", DescribeRole.Definition),
            Node("bits", "bits", "Exact declaration: def bits (c : Fin 256) (i : Fin 8) : F2.", DescribeRole.Definition),
            Node("actionFor", "actionFor", "Exact declaration: def actionFor : Fin 256 → Fin 168.", DescribeRole.Definition),
            Node("typeFor", "typeFor", "Exact declaration: def typeFor : Fin 256 → Fin 6.", DescribeRole.Definition),
            Node("classification", "classification", "Exact declaration: theorem classification (M : Mat) (ht : Matrix.trace M=0) (hne : M≠0) : ∃ g : Fin 168, ∃ k : Fin 6, phi (pull g (representative k))=M.", DescribeRole.Theorem),
            Node("six_isomorphism", "six isomorphism", "Exact declaration: theorem six_isomorphism (s : Signing) (hs : phi s≠0) : ∃ k : Fin 6, Nonempty (graph s ≃g graph (representative k)).", DescribeRole.Theorem)), []));
}
