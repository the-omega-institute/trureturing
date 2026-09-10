using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class NymanFractionalMellinDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/gochanour2026prime");

    private static Formula Mellin(Formula theta) => Seq(
        Int, Underscore, Grp(D(0)), Caret, Grp(D(1)),
        Operatorname, Grp(F.Id("fract")), Open, Frac, Grp(theta), Grp(F.Id("x")), Close,
        F.Id("x"), Caret, Grp(F.Id("s"), Minus, D(1)), Thin, F.Id("dx"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real Fractional-Part Mellin Identity.", H("Real Fractional-Part Mellin Identity"), Blocks(
            Describe.Lean(DescribeId.Create("fractional-mellin-base"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.bd_mellin_base_case_proved"),
                H("Fractional Mellin base identity"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, D(0), Lt, Re, Sp, F.Id("s"), Land, Sp, F.Id("s"), Neq, D(1), Rightarrow, Mellin(D(1)), Eq, Frac, Grp(D(1)), Grp(F.Id("s"), Minus, D(1)), Minus, Frac, Grp(Zeta, Open, F.Id("s"), Close), Grp(F.Id("s"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For real part of s greater than zero and s different from one, the exact selected upstream proof continues the floor-series identity using analyticity and connectedness. Connectedness reuses ZetaBoundsUpper.isPathConnected_aux."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fractional-mellin-integrability"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.fractionalMellin_integrableOn"),
                H("Integrability for every real parameter"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Theta, InMacro, Mathbb, Grp(F.Id("R")), Comma, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, D(0), Lt, Re, Sp, F.Id("s"), Rightarrow, Operatorname, Grp(F.Id("IntegrableOn")), Open, Open, F.Id("x"), Mapsto, Operatorname, Grp(F.Id("fract")), Open, Theta, Slash, F.Id("x"), Close, F.Id("x"), Caret, Grp(F.Id("s"), Minus, D(1)), Close, Comma, Open, D(0), Comma, D(1), Close, Comma, Operatorname, Grp(F.Id("volume")), Close))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every real theta and real part of s greater than zero, the actual integrand is integrable on Ioo zero one. Bounded measurable fractional part is dominated by an integrable complex power; there is no restriction on theta."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-fractional-mellin-scaling"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.fractionalMellin_scaling"),
                H("Real-parameter scaling"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Theta, InMacro, Mathbb, Grp(F.Id("R")), Comma, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, D(0), Lt, Theta, Le, D(1), Land, D(0), Lt, Re, Sp, F.Id("s"), Land, Sp, F.Id("s"), Neq, D(1), Rightarrow, Mellin(Theta), Eq, Theta, Caret, Grp(F.Id("s")), Mellin(D(1)), Plus, Frac, Grp(Theta, Minus, Theta, Caret, Grp(F.Id("s"))), Grp(F.Id("s"), Minus, D(1))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For zero less than theta at most one, real part of s positive, and s different from one, substitute the real scale one over theta, split the integral at one, and integrate the tail using fract of one over u equals one over u for u greater than one. The case theta equals one and null endpoints are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-fractional-mellin-e9"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.fractionalMellin_eq_zeta"),
                H("Literal E9"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Theta, InMacro, Mathbb, Grp(F.Id("R")), Comma, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, D(0), Lt, Theta, Le, D(1), Land, D(0), Lt, Re, Sp, F.Id("s"), Lt, D(1), Rightarrow, Mellin(Theta), Eq, Frac, Grp(Theta), Grp(F.Id("s"), Minus, D(1)), Minus, Frac, Grp(Theta, Caret, Grp(F.Id("s")), Zeta, Open, F.Id("s"), Close), Grp(F.Id("s"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every real theta with zero less than theta at most one, and every complex s with real part strictly between zero and one, the actual fractional-part integral equals theta divided by s minus one minus theta to the complex power s times riemannZeta s divided by s. Positive real bases use mathlib's principal complex power, agreeing with the real logarithm. The separate unit-interval functional, Lp source vectors, and separating functional are not constructed here."))), DescribeRole.Theorem)), [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaPntBounds/NymanMellinFloorSeries"))
        ]));
}
