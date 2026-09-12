using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ZfcCompatibleRecurrenceCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every Fibonacci recurrence observation has two integer coordinates, with an explicit reconstruction formula.",
        H("Two-coordinate reconstruction for Fibonacci recurrences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("recurrence-two-coordinate-reconstruction"),
                DeclarationHandle.Create("D5/S1/Digit/ZfcCompatibleRecurrenceCoordinates.recurrence_two_coordinate_reconstruction"),
                H("Two initial coordinates reconstruct every recurrence observation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("w"), Open, F.Id("n"), Close, Sp, Eq, Sp,
                    F.Id("G"), Open, F.Id("n"), Close, Sp, Times, Sp,
                    Open, F.Id("w"), Open, D(1), Close, Sp, Minus, Sp, F.Id("w"), Open, D(0), Close, Close,
                    Sp, Plus, Sp, F.Id("H"), Open, F.Id("n"), Close, Sp, Times, Sp,
                    Open, D(2), Sp, Times, Sp, F.Id("w"), Open, D(0), Close, Sp, Minus, Sp,
                    F.Id("w"), Open, D(1), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A sequence satisfying w at n plus two equals w at n plus one plus w at n is determined by its first two values. "
                            + "The reconstruction uses the two integer-valued recurrence coordinates G and H, so it works in every additive commutative group.")),
                    Paragraph(Text(
                        "The proof performs a genuine two-step induction and exposes the recurrence decomposition needed by the contextual arithmetic model. "
                            + "It does not formalize ZFC models, formula satisfaction, or the full Enc/Dec semantics."))),
                DescribeRole.Theorem)),
        []));
}
