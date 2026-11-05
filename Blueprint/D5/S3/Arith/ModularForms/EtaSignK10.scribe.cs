using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class EtaSignK10Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/EtaSignK10.";
    private static readonly LibraryNoteRef Question = LibraryNoteRef.Create("D5/L/Fourier/bringmann2024periodic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete unshifted BHHK denominator-ten sign pattern at every natural index.", H("EtaSignK10"), Blocks(
            Paragraph(Text("The original quotient is F10=E(q)^9/E(q^3)^10, with the denominator defined by its actual unit inverse and C10(n) its unshifted natural coefficient. Its first cubic trisection has constants -9 and 27 and zero component G10=E(q)^2/E(q^3)^3. The exact squared dissection identifies G10 with the sections UP,-VP,-WP. Positive ordinary partition coefficients smooth the W hole in every degree. Thus C10(9m+6) is strictly negative for every m, including m=0. The endpoint proves both residue-nine biconditionals and nonvanishing with no eventual or finite-range qualifier; C10_zero proves the empty-index value one. The mathematical derivation implements the supplied ordinary algebraic source dated 3 November 2026, SHA256 f9c81115730bc353681e172d5b2ad17d199d66bd4602b56a5da7dfe8e185852b. Classical cubic theta identities and positive convolution are reused from the existing k6 chain. These source statements do not certify independent formal review, literature priority, unique status, CI, merge, or original-problem acceptance.")),
            Node("0", "F10", "The ninth power of the actual Euler series times the tenth power of the unit inverse of E(q^3).", DescribeRole.Definition),
            Node("1", "C10", "The actual rational coefficient at the original natural index, including zero.", DescribeRole.Definition),
            Node("2", "G10", "The exact zero-progression quotient E(q)^2/E(q^3)^3.", DescribeRole.Definition),
            Node("3", "F10_eq_expanded_inverse", "The denominator is exactly the expansion of the ordinary Euler reciprocal.", DescribeRole.Theorem),
            Node("4", "zero_component", "The cubic-lift zero component B^3 P^7 equals the actual G10.", DescribeRole.Theorem),
            Node("5", "first_dissection", "The first exact trisection preserves the factors -9 and 27.", DescribeRole.Theorem),
            Node("6", "second_dissection", "The zero component is the exact U,-V,-W partition smoothing.", DescribeRole.Theorem),
            Node("7", "smoothed_positive", "All coefficients of UP, VP, WP are strictly positive, with no hole.", DescribeRole.Theorem),
            Node("8", "five_coefficient_formulas", "Five exact formulas cover both nonzero progressions modulo three and all remaining progressions modulo nine.", DescribeRole.Theorem),
            Node("9", "progression_signs", "All five progression signs hold strictly for every natural parameter.", DescribeRole.Theorem),
            Node("10", "all_index_signs", "C10 is positive iff its residue is 0,2,5,8; negative iff 1,3,4,6,7; every coefficient is nonzero.", DescribeRole.Theorem),
            Node("11", "C10_zero", "The constant coefficient of the actual quotient equals one.", DescribeRole.Theorem)
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("etasignk10-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Question),
            Blocks(Paragraph(Text(text))), role);
}
