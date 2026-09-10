using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class NymanMellinHelpersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/gochanour2026prime");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fractional Mellin Prerequisites.", H("Fractional Mellin Prerequisites"), Blocks(
            Describe.Lean(DescribeId.Create("vanishing-floor-series-tail"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.tail_vanishes"),
                H("Vanishing floor-series tail"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp, D(1), Lt, Re, Sp, F.Id("s"), Rightarrow, Lim, Underscore, Grp(F.Id("N"), To, Infty), F.Id("N"), Open, Frac, Grp(D(1)), Grp(F.Id("N"), Plus, D(1)), Close, Caret, Grp(F.Id("s")), Eq, D(0)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The power tail tends to zero when the real part of s exceeds one. This is the live FloorMellin source argument."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("partial-zeta-limit"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.partial_zeta_tendsto"),
                H("Partial zeta limit"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp, D(1), Lt, Re, Sp, F.Id("s"), Rightarrow, Lim, Underscore, Grp(F.Id("N"), To, Infty), Sum, Underscore, Grp(F.Id("n"), Eq, D(0)), Caret, Grp(F.Id("N"), Minus, D(1)), Frac, Grp(D(1)), Grp(Open, F.Id("n"), Plus, D(1), Close, Caret, Grp(F.Id("s"))), Eq, Zeta, Open, F.Id("s"), Close))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The reciprocal-power partial sums converge to the actual riemannZeta on the half-plane of absolute convergence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-base-power-quotient"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.ofReal_div_cpow"),
                H("Positive-base power quotient"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Comma, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp, D(1), Le, Sp, F.Id("k"), Land, D(1), Le, Sp, F.Id("n"), Rightarrow, Open, Frac, Grp(F.Id("k")), Grp(F.Id("n")), Close, Caret, Grp(F.Id("s")), Eq, F.Id("k"), Caret, Grp(F.Id("s")), F.Id("n"), Caret, Grp(Minus, F.Id("s"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source helper is bound to the installed nonnegative-real complex-power quotient and negation APIs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("restricted-mellin-definition"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.mellinRestricted"),
                H("Restricted Mellin integral"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source definition integrates x to the power s minus one times f over Ioc zero one with volume measure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fractional-basis-definition"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.fractBasisC"),
                H("Fractional basis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source definition is the complex coercion of the real fractional part of k divided by x."))), DescribeRole.Definition)), [

        ]));
}
