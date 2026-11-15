using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class SplitSubmoduleLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.";
    private static DocumentBlock Item(string id, string declaration, string title,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(
            LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete kernel/projection/placement geometry of the received orthogonality result.",
        H("Full actual submodules and source criteria"),
        Blocks(
            Item("finrank-split", "finrank_split", "Full kernel/projection dimension",
                "The actual first-kernel and complete second projection recover the dimension of every split submodule by a proved kernel equivalence and rank-nullity.", DescribeRole.Theorem),
            Item("first-kernel", "firstKernel", "Actual first-summand intersection",
                "The pullback along the first inclusion is the kernel part K of every actual submodule.", DescribeRole.Definition),
            Item("second-range", "secondRange", "Actual second projection",
                "The image under the second projection is the full projection P.", DescribeRole.Definition),
            Item("exists-unique-lift", "exists_unique_lift", "The uniquely determined quotient map",
                "Every submodule U determines exactly one linear f:P -> A/K; membership of (a,s) is equivalent to a mod K=f(s). A linear right inverse of the actual projection constructs f, including zero and full fibers.", DescribeRole.Theorem),
            Item("lift-space", "liftSpace", "All reconstructed submodules",
                "The carrier consists of all (a,s) with s in P and a mod K=f(s). It imposes no independent reconstruction premise.", DescribeRole.Definition),
            Item("first-kernel-lift-space", "firstKernel_liftSpace", "Exact recovered intersection",
                "Every arbitrary full placement map recovers precisely its specified K.", DescribeRole.Theorem),
            Item("second-range-lift-space", "secondRange_liftSpace", "Exact recovered projection",
                "Surjectivity of the quotient supplies every projection vector, without removing degenerate fibers.", DescribeRole.Theorem),
            Item("reconstruction", "reconstruction", "Full reconstruction",
                "The quotient map reconstructs every vector of the original entire submodule, and is unique.", DescribeRole.Theorem),
            Item("lift-space-injective", "liftSpace_injective", "Distinct placements remain distinct",
                "Full quotient-valued linear maps give distinct actual submodules.", DescribeRole.Theorem),
            Item("lift-equiv", "liftEquiv", "The entire fixed-profile fiber",
                "All linear maps P -> A/K are equivalent to all submodules with the exact prescribed first kernel and second image.", DescribeRole.Definition),
            Item("second-kernel-lift-space", "secondKernel_liftSpace", "Intersection with the complement",
                "The second-summand intersection is precisely the subtype image of ker(f).", DescribeRole.Theorem),
            Item("orthogonal-iff", "orthogonal_iff", "The complete bilinear X/Y/Z criterion",
                "For every field, two arbitrary complementary spaces and every bilinear form vanishing on the first summand, full orthogonality is equivalent to the two cross-kernel pairings and the complete placement pairing. All representatives are full linear lifts, and zero-dimensional cases remain included.", DescribeRole.Theorem),
            Item("fiber-card", "fiber_card", "Exact full finite-field count",
                "Over every finite field, count every submodule in the fixed K/P fiber by |F|^(dim(P)*(dim(A)-dim(K))). The actual lift equivalence and linear-map dimension formula prove the count.", DescribeRole.Theorem)),
        []));
}
