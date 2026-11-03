using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class EulerNineComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/EulerNineComparison.";
    private static readonly LibraryNoteRef Question = LibraryNoteRef.Create("D5/L/Fourier/bringmann2024periodic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-index restricted nine-residue partition comparisons and positive products for the algebraic k10 route.", H("EulerNineComparison"), Blocks(
            Paragraph(Text("The base product supplier is Mathlib Nat.Partition.hasProd_powerSeriesMk_card_restricted, by Weiyi Wang under Apache 2.0. These proofs use actual restricted counting series, distinct allowed factors and exact stabilization at each arbitrary coefficient. The nine-block comparisons and positive decompositions implement the corresponding portion of the proposed ordinary source 'An all-index algebraic route to the denominator-ten eta signs', 3 November 2026, SHA256 f9c81115730bc353681e172d5b2ad17d199d66bd4602b56a5da7dfe8e185852b. The source is fallible mathematical input, not an acceptance certificate.")),
            Node("0", "S", "The actual restricted partition series allowing all positive parts not divisible by nine.", DescribeRole.Definition),
            Node("1", "block", "A pair of Euler factors with weights 9i+r and 9i+9-r.", DescribeRole.Definition),
            Node("2", "pairWeight", "The two weights of a block, indexed by a Boolean colour.", DescribeRole.Definition),
            Node("3", "coeff_cancel_blocks", "Distinct nine-block weights and two absent small weights cancel distinct reciprocals; every coefficient of the remaining product is nonnegative.", DescribeRole.Theorem),
            Node("4", "mixed", "The finite product using one block type before a moving cut and another after it.", DescribeRole.Definition),
            Node("5", "coeff_finite_comparison", "A paid block difference and multiplicity-free cancellation prove the coefficientwise finite product comparison by telescoping.", DescribeRole.Theorem),
            Node("6", "coeff_finite_42", "Every coefficient of the finite type-four cancellation product bounds that of the type-two product.", DescribeRole.Theorem),
            Node("7", "coeff_finite_21", "Every coefficient of the finite type-two cancellation product bounds that of the type-one product.", DescribeRole.Theorem),
            Node("8", "Q", "The actual restricted counting series excluding residues zero, r and nine minus r modulo nine. Source A=Q4, B=Q2 and C=Q1.", DescribeRole.Definition),
            Node("9", "coeff_Q_finite", "For every n and N with n<9N, the degree-n coefficient of the infinite restricted series equals its finite cancelled product coefficient.", DescribeRole.Theorem),
            Node("10", "coefficient_order", "For every natural n, including zero, the actual restricted products satisfy C[n] <= B[n] <= A[n].", DescribeRole.Theorem),
            Node("11", "D", "The actual coloured partition product with one colour at residues three and six and two colours at residues four and five.", DescribeRole.Definition),
            Node("12", "multiplicity_relation", "Actual reciprocal multiplicities prove AD=BC, without dividing any coefficient inequality.", DescribeRole.Theorem),
            Node("13", "coeff_delta_nonnegative", "For every n, the coefficient of AC-CD is nonnegative, by C(A-B)+D(A-C) and AD=BC.", DescribeRole.Theorem),
            Node("14", "lowerProduct", "The actual lower product (1-X)AC appearing in the proposed W decomposition.", DescribeRole.Definition),
            Node("15", "coeff_lowerProduct_nonnegative", "Every coefficient of (1-X)AC is nonnegative after exact cancellation of its sole part-one factor.", DescribeRole.Theorem),
            Node("16", "coeff_lowerProduct_ge_one", "The coefficient of (1-X)AC is at least one at degree zero and every degree at least two.", DescribeRole.Theorem),
            Node("17", "lowerProduct_initial", "The exact lower product has constant coefficient one and degree-one coefficient zero.", DescribeRole.Theorem),
            Paragraph(Text("These cancellation and comparison results have present mathematical consumers: EulerNineDissection identifies the actual quotient, EulerNineSquareDissection derives the cubic relation and squared coefficient bounds, and EtaSignK10 proves the complete source-defined denominator-ten endpoint. The separate ordinary manuscript is fallible input; independent formal review, original-problem acceptance, literature priority, unique status, CI and publication are not certified here."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("eulerninecomparison-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Question),
            Blocks(Paragraph(Text(text))), role);
}
