using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class EtaSignK6Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/EtaSignK6.";
    private static readonly LibraryNoteRef Question = LibraryNoteRef.Create("D5/L/Fourier/bringmann2024periodic");
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two exact trisections and positive ordinary partition convolution give the full normalized k6 coefficient sign pattern.", H("EtaSignK6"), Blocks(
            Paragraph(Text("Two exact trisections and positive ordinary partition convolution give the full normalized k6 coefficient sign pattern.")),
            Node("0", "F6", "The normalized Euler quotient E(X)^9/E(X^3)^6, with its denominator realized by the actual unit inverse.", DescribeRole.Definition),
            Node("1", "C6", "The rational coefficient at the original natural index in the normalized Euler quotient; no eta-shift relabelling.", DescribeRole.Definition),
            Node("2", "G6", "The zero-progression quotient B(X)^2/E(X^3) used in the second trisection.", DescribeRole.Definition),
            Node("3", "expanded_inverse", "Expansion by three preserves the actual reciprocal of the Euler series.", DescribeRole.Theorem),
            Node("4", "F6_eq_expanded_inverse", "The expanded reciprocal equals the unit inverse used in the source-defined F6.", DescribeRole.Theorem),
            Node("5", "zero_component", "The first zero-progression expression is exactly B(X)^2/E(X^3).", DescribeRole.Theorem),
            Node("6", "first_dissection", "The first trisection has factors -9 and 27 and the correctly rescaled reciprocal Euler denominator.", DescribeRole.Theorem),
            Node("7", "second_dissection", "The second trisection has factors 1, -6 and 9 on the three remaining progressions.", DescribeRole.Theorem),
            Node("8", "five_coefficient_formulas", "Five exact coefficient formulas cover every natural degree, including zero.", DescribeRole.Theorem),
            Node("9", "positive_convolution", "Nonnegative lattice theta powers with constant term one convolved with ordinary partition powers have strictly positive coefficients.", DescribeRole.Theorem),
            Node("10", "progression_signs", "Strict signs on the two progressions modulo three and the three remaining progressions modulo nine hold for every natural parameter.", DescribeRole.Theorem),
            Node("11", "all_index_signs", "The complete BHHK v1 table entry: positivity exactly at 0,2,5,6,8 modulo nine, negativity exactly at 1,3,4,7, and no zero coefficient.", DescribeRole.Theorem),
            Paragraph(Text("Statements and proof dependencies come from the exact scoped Lean report. Classical theta mathematics is attributed to Borwein and Cooper as quoted in Huang et al. arXiv:2507.16644v1. The repository InversionSeq207 triple-product supplier is reused. No literature priority, worldwide absence, journal-typeset inspection, CI or original-problem acceptance is certified by this document."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("etasignk6-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Question, Source),
            Blocks(Paragraph(Text(text))), role);
}
