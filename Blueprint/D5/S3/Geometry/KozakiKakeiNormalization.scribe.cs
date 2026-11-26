using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiNormalization.";
    private static readonly LibraryNoteRef Primary = LibraryNoteRef.Create("D5/L/FiniteGeometry/kozakikakei2026coxeterfriezes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The written level equation is precisely the condition for an admissible matrix to have a unique representative in ordered normal form.",
        H("Existence and uniqueness of the ordered normal form"),
        Blocks(
            Definition("UnitAdjacent", "Unit consecutive minors",
                "Each successive pair in linear column order has minor one."),
            Theorem("normalized_level", "A normalized matrix is on the level",
                "This is the double-normalized case of Kozaki and Kakei's Lemma 5. All factors of both written matching products are one.",
                NormalizedLevel()),
            Theorem("normalized_exists", "Existence of the ordered representative",
                "This is the existence direction of Kozaki and Kakei's Theorem 7(ii). An invertible row operation fixes the first two columns. The initial diagonal factors fix the third, and a recurrence sets the remaining consecutive minors to one. The level equation then forces the closing minor to be one.",
                NormalizedExists()),
            Theorem("normalized_unique_of_equiv", "Uniqueness within a matrix class",
                "In the uniqueness part of Kozaki and Kakei's Theorem 7(ii), the first two fixed columns force the left transformation to be diagonal. The third forces its entries to agree, and the consecutive minors determine all remaining column factors.",
                NormalizedUniqueOfEquiv()),
            Theorem("normalized_representative_iff", "Characterization of normalizable matrices",
                "Kozaki and Kakei's Theorem 7(ii) characterizes even-order normalization. For every admissible matrix, the existence of exactly one normalized equivalent matrix is equivalent to the literal equality of the two determinant products in equations (24)–(26).",
                NormalizedRepresentativeIff()))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromLiterature(Primary),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    private static Formula NormalizedLevel() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("Z"),
        Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"), Comma, F.Id("m"), Close, Comma, Sp, D(2), Sp, Le, Sp,
        F.Id("m"), Sp, Implies, Sp, Word("Normalized"), Open, F.Id("m"), Comma, F.Id("Z"), Close, Sp, Implies,
        Sp, Word("evenProduct"), Open, F.Id("Z"), Close, Sp, Eq, Sp, Word("oddProduct"), Open, F.Id("Z"), Close);

    private static Formula NormalizedExists() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("Z"),
        Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"), Comma, F.Id("m"), Close, Comma, Sp, D(2), Sp, Le, Sp,
        F.Id("m"), Sp, Implies, Sp, Word("Admissible"), Open, F.Id("Z"), Close, Sp, Implies, Sp,
        Word("evenProduct"), Open, F.Id("Z"), Close, Sp, Eq, Sp, Word("oddProduct"), Open, F.Id("Z"), Close,
        Sp, Implies, Sp, Open, Exists, Sp, F.Id("W"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"), Comma,
        F.Id("m"), Close, Comma, Sp, Word("Normalized"), Open, F.Id("m"), Comma, F.Id("W"), Close, Sp, Land,
        Sp, Word("MatEquivalent"), Open, F.Id("W"), Comma, F.Id("Z"), Close, Close);

    private static Formula NormalizedUniqueOfEquiv() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("Z"),
        Comma, F.Id("W"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"), Comma, F.Id("m"), Close, Comma, Sp,
        D(2), Sp, Le, Sp, F.Id("m"), Sp, Implies, Sp, Word("Normalized"), Open, F.Id("m"), Comma, F.Id("Z"),
        Close, Sp, Implies, Sp, Word("Normalized"), Open, F.Id("m"), Comma, F.Id("W"), Close, Sp, Implies, Sp,
        Word("MatEquivalent"), Open, F.Id("W"), Comma, F.Id("Z"), Close, Sp, Implies, Sp, F.Id("W"), Sp, Eq,
        Sp, F.Id("Z"));

    private static Formula NormalizedRepresentativeIff() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("Z"),
        Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"), Comma, F.Id("m"), Close, Comma, Sp, D(2), Sp, Le, Sp,
        F.Id("m"), Sp, Implies, Sp, Word("Admissible"), Open, F.Id("Z"), Close, Sp, Implies, Sp, Open, Open,
        Exists, Bang, Sp, F.Id("W"), Sp, Colon, Sp, Word("Chart"), Open, F.Id("K"), Comma, F.Id("m"), Close,
        Comma, Sp, Word("Normalized"), Open, F.Id("m"), Comma, F.Id("W"), Close, Sp, Land, Sp,
        Word("MatEquivalent"), Open, F.Id("W"), Comma, F.Id("Z"), Close, Close, Sp, Iff, Sp,
        Word("evenProduct"), Open, F.Id("Z"), Close, Sp, Eq, Sp, Word("oddProduct"), Open, F.Id("Z"), Close,
        Close);

    private static Formula Word(string value) => Seq(Operatorname, Grp(F.Id(value)));

    private static string NodeId(string name) =>
        "frieze-normalization-" + name.ToLowerInvariant().Replace('_', '-');
}
