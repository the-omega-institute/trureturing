using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class FiniteCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/FiniteCover.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite fibers and canonical graph invariants", H("Finite fibers and canonical graph invariants"),
        Blocks(Paragraph(Text("The relational selection predicates are transported to canonical finite stars. Constant finite fibers are counted exactly, including fiber size zero. Safely certified minimal selections pull back under neighborhood covers and yield the multiplicative SF lower bound when every minimal base selection has safe certificates. Local injectivity yields the multiplicative beta lower bound. These directions do not preserve a positive SF-minus-beta gap, and global surjectivity is not silently added.")),
            Node("regular_forms_iff", "regular forms iff", "Exact declaration: theorem regular_forms_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Regular.Forms G.Adj (· ∈ S) ↔ IsStarForming G 2 S.", DescribeRole.Theorem),
            Node("regular_minimal_iff", "regular minimal iff", "Exact declaration: theorem regular_minimal_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Regular.Minimal G.Adj (· ∈ S) ↔ IsMinimalStarForming G 2 S.", DescribeRole.Theorem),
            Node("card_preimage_uniform", "card preimage uniform", "Exact declaration: theorem card_preimage_uniform (p : W → V) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) (S : Finset V) : (Finset.univ.filter (fun w => p w ∈ S)).card = k * S.card.", DescribeRole.Theorem),
            Node("minimal_preimage_of_safe", "minimal preimage of safe", "Exact declaration: theorem minimal_preimage_of_safe (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (S : Finset V) (hS : IsMinimalStarForming G 2 S) (hsafe : CoverPullback.HasSafeCertificates G.Adj (· ∈ S)) : IsMinimalStarForming H 2 (Finset.univ.filter (fun w => p w ∈ S)).", DescribeRole.Theorem),
            Node("sf_mul_le_of_safe", "sf mul le of safe", "Exact declaration: theorem sf_mul_le_of_safe (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) (hsafe : ∀ S : Finset V, IsMinimalStarForming G 2 S → CoverPullback.HasSafeCertificates G.Adj (· ∈ S)) : k * SF G 2 ≤ SF H 2.", DescribeRole.Theorem),
            Node("beta_mul_le", "beta mul le", "Exact declaration: theorem beta_mul_le (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : k * beta G 2 ≤ beta H 2.", DescribeRole.Theorem)), []));
}
