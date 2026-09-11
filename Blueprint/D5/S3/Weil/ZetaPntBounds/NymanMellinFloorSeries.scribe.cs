using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class NymanMellinFloorSeriesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/gochanour2026prime");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Floor-Series Mellin Identity.", H("Floor-Series Mellin Identity"), Blocks(
            Describe.Lean(DescribeId.Create("floor-series-mellin-identity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaPntBounds/NymanMellinFloorSeries.mellin_fractBasis"),
                H("Floor-series Mellin identity"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, D(1), Le, Sp, F.Id("k"), Land, D(1), Lt, Re, Sp, F.Id("s"), Rightarrow, Int, Underscore, Grp(D(0)), Caret, Grp(D(1)), F.Id("x"), Caret, Grp(F.Id("s"), Minus, D(1)), Operatorname, Grp(F.Id("fract")), Open, Frac, Grp(F.Id("k")), Grp(F.Id("x")), Close, Thin, F.Id("dx"), Eq, Frac, Grp(F.Id("k")), Grp(F.Id("s"), Open, F.Id("s"), Minus, D(1), Close), Plus, Frac, Grp(F.Id("k"), Caret, Grp(F.Id("s"))), Grp(F.Id("s")), Open, Sum, Underscore, Grp(F.Id("m"), Eq, D(0)), Caret, Grp(F.Id("k"), Minus, D(1)), Open, F.Id("m"), Plus, D(1), Close, Caret, Grp(Minus, F.Id("s")), Minus, Zeta, Open, F.Id("s"), Close, Close))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For positive natural k and real part of s greater than one, the source proof partitions the floor function into intervals, evaluates powers, and sums by parts to the actual zeta expression. The upstream argument and live prerequisites are retained."))), DescribeRole.Theorem)), [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers"))
        ]));
}
