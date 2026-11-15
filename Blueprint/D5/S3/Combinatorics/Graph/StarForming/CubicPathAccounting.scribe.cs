using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CubicPathAccountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CubicPathAccounting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible witness-pair augmentation", H("Compatible witness-pair augmentation"),
        Blocks(Paragraph(Text("Compatible isolated witness/leaf pairs can be adjoined to an existing dissociation selection. The extra-leaf failure lemma identifies witness capacity outside the high image. These are graph-level augmentation statements with the complete compatibility hypotheses, not a proof that the original unaugmented exchanges are maximum or that their accounting normal form classifies graph-parameter equality.")),
            Node("augment_isolated_pairs", "augment isolated pairs", "Exact declaration: theorem augment_isolated_pairs {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection added : Vertex → Prop) (partner : Vertex → Vertex) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hdissociates : Dissociates adjacency selection) (hisolated : ∀ vertex, added vertex → ∀ neighbor, selection neighbor → ¬ adjacency (partner vertex) neighbor) (hneighbor : ∀ vertex, added vertex → ∀ neighbor, selection neighbor → adjacency vertex neighbor → neighbor = partner vertex) (hindependent : ∀ first second, added first → added second → ¬ adjacency first second) (hinjective : ∀ first second, added first → added second → partner first = partner second → first = second) : Dissociates adjacency (fun vertex => selection vertex ∨ added vertex).", DescribeRole.Theorem),
            Node("extra_leaf_failure_is_unused", "extra leaf failure is unused", "Exact declaration: theorem extra_leaf_failure_is_unused {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (htrianglefree : ∀ outside first second, adjacency outside first → adjacency outside second → adjacency first second → False) (witness reserved : Vertex → Vertex) (hfailure : ∀ owner, High adjacency selection owner → Failure adjacency selection owner (witness owner)) (hreserved : ∀ owner, High adjacency selection owner → ¬ adjacency (witness owner) owner → ∀ neighbor, selection neighbor → adjacency (witness owner) neighbor → neighbor = reserved owner) (leaf support outside : Vertex) (hleaf : selection leaf) (hsupport : selection support) (hleafedge : adjacency leaf support) (houtsideedge : adjacency outside leaf) (hunique : ∀ neighbor, selection neighbor → adjacency leaf neighbor → neighbor = support) (hextra : leaf ≠ reserved support) : ∀ owner, High adjacency selection owner → outside ≠ witness owner.", DescribeRole.Theorem)), []));
}
