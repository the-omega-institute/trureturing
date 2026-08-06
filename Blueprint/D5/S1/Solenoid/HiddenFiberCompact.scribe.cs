using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class HiddenFiberCompactDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Solenoid/HiddenFiberCompact",
                "The hidden fiber is closed, compact, and sequentially compact coordinatewise."),
            H("Hidden Fiber Compactness"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("hidden-fiber-closed-compact-sequentially-compact"),
                    H("The hidden fiber is compact in every equivalent sense"),
                    LeanTheorem(
                        "D5/S1/Solenoid/HiddenFiberCompact."
                        + "hiddenFiber_closed_compact_seqCompact"),
                    StatementProjectionFixtureLoader.FromLean(LeanTheorem("D5/S1/Solenoid/HiddenFiberCompact.hiddenFiber_closed_compact_seqCompact")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Continuity of the visible projection makes its zero fiber closed. "
                        + "The ambient solenoid is compact, so the fiber is compact. Its "
                        + "countable product topology is first countable, hence compactness "
                        + "gives a convergent subsequence; the formal coordinatewise "
                        + "convergence equivalence identifies this with the diagonal, "
                        + "layer-by-layer limit."))))),
[
                                DocumentEdge.TruthAnchor.Create(
                                    LeanDeclarationRef.Create("D5/S1/Solenoid/HiddenFiberCompact.hiddenFiber_closed_compact_seqCompact")),
                            ]));
}
