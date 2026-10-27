using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class OriginalLowerSelectorArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consumed arithmetic for supported LOWER masks and source-funded prepayment.",
        H("Supported-mask selection arithmetic"),
        Blocks(
            Paragraph(Text("These private helpers are consumed by OriginalLowerFirstSelector.canonical_lower_first_selector. Their SelectorArithmetic record contains numerical consequences of the original source and terminal bounds; source_arithmetic in the selector module proves every field. It assumes no selection conclusion. The helper has no independent first-freeze or new mathematical credit.")),
            Paragraph(Text("fixed_support_crossing scans an actual finite inventory of positive integer weights bounded by M, returning a literal subset whose sum lies between the positive target and target+M-1. low_selection uses it on retained w or n bits, or selects the retained top w bit. It proves both the reflected correction and the available positive b compensation.")),
            Paragraph(Text("high_prepayment chooses the least natural payment reaching E-B+1 when E is at least B=(q-tau-1)*b. The terminal bound Q<=f0*a0 together with the arithmetic bound payment*a0<Q proves payment<f0. numerical_selection combines the low and high quotient cases to return actual submasks, a b coefficient in [0,q-1], a payment below f0 and a residual in [0,(y-1)/2].")),
            Paragraph(Text("The physical source, signed costs, chronological word, separate LARGE steps, exact unused complement and bounds on every natural take remain in OriginalLowerFirstSelector. This arithmetic does not assert arbitrary depleted-tail viability, terminal arrival, all-m completion, BOTH-F completion or original normalization."))), []));
}
