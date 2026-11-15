using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodAllDoubleCoversDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodAllDoubleCovers.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full arbitrary Heawood double-cover parameter theorem", H("The full arbitrary Heawood double-cover parameter theorem"),
        Blocks(Paragraph(Text("An arbitrary finite neighborhood cover of the actual fourteen-vertex binary Fano graph with every actual fiber of size two is represented by a binary signing. Actual graph-isomorphism transport and the complete signing theorem give SF sixteen, beta fourteen exactly when not preconnected, and connected beta fifteen or sixteen with gap at most one. The four unresolved type-specific exact beta values and higher deck-group questions remain separate.")),
            Node("parameters", "parameters", "Exact declaration: theorem parameters {U : Type} [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 14) (cover : CoverPullback.NeighborhoodCover HeawoodLift.base.Adj H.Adj p) (fibers : ∀ v, Nat.card {u // p u=v}=2) : SF H 2=16 ∧ (beta H 2=14 ↔ ¬ H.Preconnected) ∧ (H.Preconnected → (beta H 2=15 ∨ beta H 2=16) ∧ SF H 2-beta H 2≤1).", DescribeRole.Theorem)), []));
}
