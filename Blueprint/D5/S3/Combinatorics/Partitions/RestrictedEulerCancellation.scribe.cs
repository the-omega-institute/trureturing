using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class RestrictedEulerCancellationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.";
    private static readonly LibraryNoteRef Question = LibraryNoteRef.Create("D5/L/Fourier/bringmann2024periodic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact restricted-partition Euler cancellation with finite and injectively indexed removed weights.", H("RestrictedEulerCancellation"), Blocks(
            Paragraph(Text("The base product supplier is Mathlib Nat.Partition.hasProd_powerSeriesMk_card_restricted, by Weiyi Wang under Apache 2.0. These proofs use actual restricted counting series, distinct allowed factors and exact stabilization at each arbitrary coefficient. The nine-block comparisons and positive decompositions implement the corresponding portion of the proposed ordinary source 'An all-index algebraic route to the denominator-ten eta signs', 3 November 2026, SHA256 f9c81115730bc353681e172d5b2ad17d199d66bd4602b56a5da7dfe8e185852b. The source is fallible mathematical input, not an acceptance certificate.")),
            Node("0", "restrictedSeries", "The actual counting series for partitions with a specified allowed-part predicate.", DescribeRole.Definition),
            Node("1", "coeff_restricted_nonnegative", "Every restricted counting coefficient is nonnegative.", DescribeRole.Theorem),
            Node("2", "restricted_constant_one", "The empty partition gives constant coefficient one for every predicate.", DescribeRole.Theorem),
            Node("3", "coeff_restricted_ge_one_of_parts", "An explicit positive allowed multiset of total degree n supplies a coefficient lower bound of one.", DescribeRole.Theorem),
            Node("4", "coeff_restricted_ge_one_of_two_three", "Allowed parts two and three give a coefficient at least one in every degree zero or at least two.", DescribeRole.Theorem),
            Node("5", "coeff_restricted_congr", "Allowed-part predicates agreeing on positive parts up to n have the same degree-n coefficient.", DescribeRole.Theorem),
            Node("6", "restricted_mul_one_sub", "Cancelling one allowed positive Euler factor gives exactly the restricted series with that part removed.", DescribeRole.Theorem),
            Node("7", "restricted_mul_euler_finset", "Cancelling a finite set of distinct positive allowed parts gives exactly its complementary restricted product.", DescribeRole.Theorem),
            Node("8", "coeff_cancelled_product_nonnegative", "Finite cancellation preserves nonnegativity because the result is an actual counting series.", DescribeRole.Theorem),
            Node("9", "restricted_mul_indexed_euler", "The exact finite cancellation identity is invariant under any injective indexing of the allowed weights.", DescribeRole.Theorem),
            Node("10", "coeff_cancelled_indexed_product_nonnegative", "An injective finite family of allowed weights cancels to a nonnegative counting product.", DescribeRole.Theorem),
            Paragraph(Text("These cancellation and comparison results have present mathematical consumers: EulerNineDissection identifies the actual quotient, EulerNineSquareDissection derives the cubic relation and squared coefficient bounds, and EtaSignK10 proves the complete source-defined denominator-ten endpoint. The separate ordinary manuscript is fallible input; independent formal review, original-problem acceptance, literature priority, unique status, CI and publication are not certified here."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("restrictedeulercancellation-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Question),
            Blocks(Paragraph(Text(text))), role);
}
