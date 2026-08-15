using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class HistoryCarrierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite marker and event histories preserve the source append direction and low-level encoding.",
        H("History Carrier"),
        Blocks(
            Paragraph(
                Text("Marker histories form the free monoid on exactly two constructors. Because source expressions extend at the left edge, source append is represented by reversed free-monoid multiplication; its recursive equation and both unit laws follow definitionally from this orientation.")),
            Paragraph(
                Text("Events carry source history, opcode, input code, and output marker. Event histories embed into marker histories with the literal low-level code `0 -> 00`, `1 -> 01`, and separator `11`; the bridge preserves appending one generated event.")),
            Describe.Lean(
                DescribeId.Create("splice-is-associative-with-the-empty-history-as-two-sided-unit"),
                DeclarationHandle.Create("D5/S0/History/HistoryCarrier.marker_splice_laws"),
                H("Splice is associative with the empty history as two-sided unit"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp, F.Id("c"),
                    InMacro, Sp, Operatorname, Grp(F.Id("MarkerHistory")), Comma, Sp,
                    Operatorname, Grp(F.Id("splice")), Open,
                    Operatorname, Grp(F.Id("splice")), Open, F.Id("a"), Comma, Sp, F.Id("b"), Close,
                    Comma, Sp, F.Id("c"), Close, Eq,
                    Operatorname, Grp(F.Id("splice")), Open, F.Id("a"), Comma, Sp,
                    Operatorname, Grp(F.Id("splice")), Open, F.Id("b"), Comma, Sp, F.Id("c"), Close,
                    Close, Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("h"), InMacro, Sp,
                    Operatorname, Grp(F.Id("MarkerHistory")), Comma, Sp,
                    Operatorname, Grp(F.Id("splice")), Open, D(1), Comma, Sp, F.Id("h"), Close,
                    Eq, F.Id("h"), Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("h"), InMacro, Sp,
                    Operatorname, Grp(F.Id("MarkerHistory")), Comma, Sp,
                    Operatorname, Grp(F.Id("splice")), Open, F.Id("h"), Comma, Sp, D(1), Close,
                    Eq, F.Id("h"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The three conjuncts are the atomic acceptance theorem for the marker carrier: splice is associative, and the empty history is a unit on the left and on the right. All three follow definitionally from representing source append as reversed free-monoid multiplication, so the proof is the single rewrite that unfolds splice and applies monoid associativity. The prime-power Godel numbering and its decoder round-trip are explicitly outside this producer cluster and tracked separately."))),
                DescribeRole.Theorem))));
}
