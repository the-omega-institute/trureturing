using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class ResidualLedgerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/History/ResidualLedger",
            "A residual ledger entry consists exactly of its source, detector, four-state status, and next action."),
        H("The Residual Ledger"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("residual-ledger-entries-have-exactly-four-components"),
                H("Residual ledger entries are losslessly determined by four components"),
                LeanTheorem(
                    "D5/S0/History/ResidualLedger.residual_ledger_components_bijective"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("ResidualLedgerEntry")),
                    Sp, Sim, Sp,
                    F.Id("Source"), Sp, Times, Sp,
                    F.Id("Detector"), Sp, Times, Sp,
                    Operatorname, Grp(F.Id("ResidualStatus")), Sp, Times, Sp,
                    F.Id("NextAction"))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "A residual ledger entry is a typed workflow object with four fields. "
                        + "The source records where the discrepancy arose, the detector records "
                        + "the readout that exposes it, the status is one of open, closed, tail, "
                        + "or semantic, and the next-action field stores its future treatment or "
                        + "budget. The Lean carrier makes those alternatives explicit and prevents "
                        + "an entry from silently occupying an unnamed fifth state.")),
                    Paragraph(Text(
                        "The theorem packages the definition as a lossless equivalence between "
                        + "the named record and the product of its four components. The library "
                        + "was searched before proving: pinned Mathlib supplies standard product "
                        + "equivalences and `Equiv.bijective`, but no residual-ledger workflow type. "
                        + "The implementation therefore adds only the source-specific record and "
                        + "uses Mathlib's bijectivity theorem for the final claim. The source atom "
                        + "contains no numerical certificate.")))
            ))));
}
