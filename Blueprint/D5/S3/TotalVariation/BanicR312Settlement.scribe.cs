using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class BanicR312SettlementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/BanicR312Settlement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/TotalVariation/banicelezovic2026cyclic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic multinomial dispersion reverses both monotonicities in Remark 3.12.",
        H("Two reversals of cyclic multinomial dispersion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cyclic-multinomial-dispersion-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Proposed monotonicities"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    Clause(Dispersion(Add(Id("n"), Num(1)), Id("N")), Dispersion(Id("n"), Id("N"))),
                    F.Sp, F.Land, F.Sp,
                    Clause(Dispersion(Id("n"), Id("N")), Dispersion(Id("n"), Add(Id("N"), Num(1))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The count vector has n bins and N draws with uniform bin probabilities. Its law is the sum of "
                    + "point masses of weight N! divided by the product of the count factorials, times n to the power −N. "
                    + "Vectors whose counts sum to a different total have weight zero. The cyclic variation D sums the "
                    + "absolute differences of consecutive counts, including the closing edge. The dispersion "
                    + "σ(n,N) is the square root of Var(D)/N. Each inequality ranges over natural n at least three "
                    + "and N at least one, as in the two questions in Remark 3.12."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cyclic-multinomial-dispersion-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Strict reversals in the two parameters"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For each of the three parameter pairs, sum the integer factorial weight times D to powers "
                        + "zero, one and two over the bounded count vectors. At (3,4) these sums are (81,312,1488), "
                        + "at (4,4) they are (256,1120,5888), and at (4,5) they are (1024,5040,29600). "
                        + "The zeroth sums give total probability one after division by n to the power N. "
                        + "The first and second sums give the corresponding moments under the same measure.")),
                    Paragraph(Text(
                        "Subtracting the squared first moment from the second moment and dividing by N gives "
                        + "normalized variances 644/729, 247/256 and 3835/4096, respectively. Both outside values "
                        + "are strictly smaller than 247/256. The square root preserves these strict comparisons, "
                        + "so adding the fourth bin raises the dispersion at N = 4 and adding the fifth draw "
                        + "lowers it at n = 4."))),
                DescribeRole.Theorem))));

    private static Formula Dispersion(Formula n, Formula samples) =>
        F.Seq(F.SigmaLower, F.Open, n, F.Comma, samples, F.Close);

    private static Formula Clause(Formula left, Formula right) =>
        F.Seq(F.OpenBracket, F.Forall, F.Sp, Id("n"), F.Comma, Id("N"), F.Sp,
            F.InMacro, F.Sp, F.Mathbb, F.Grp(Id("N")), F.Comma, F.Sp,
            Num(3), F.Le, Id("n"), F.Sp, F.Rightarrow, F.Sp,
            Num(1), F.Le, Id("N"), F.Sp, F.Rightarrow, F.Sp, left, F.Le, right, F.CloseBracket);
}
