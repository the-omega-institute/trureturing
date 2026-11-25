using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.ResidualLedger;

internal sealed class NativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A residual ledger entry is equivalent to the tuple of its four fields.",
        H("The native residual ledger representation"),
        Blocks(Describe.Lean(
            DescribeId.Create("native-residual-ledger-product-equivalence"),
            DeclarationHandle.Create("D5/S0/History/ResidualLedger/Native.residualLedgerEquivComponents"),
            H("Recovering an entry from its components"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("ResidualLedgerEntry"), Sp, Sim, Sp, F.Id("Source"), Sp, Times, Sp,
                F.Id("Detector"), Sp, Times, Sp, F.Id("ResidualStatus"), Sp, Times, Sp,
                F.Id("NextAction")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The forward map reads the source, detector, status and next action in field order. "
                + "The inverse builds a record from the same four components. Pattern matching on "
                + "the record and tuple proves both round trips."))),
            DescribeRole.Definition))));
}
