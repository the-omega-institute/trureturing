using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class PerfectRecordExchangeReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A perfect copied-address record eliminates the exchange readout after the record is discarded.",
        H("Perfect Record Exchange Readout"),
        Blocks(Describe.Lean(
            DescribeId.Create("perfect-record-exchange-readout-vanishes"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Measurement/PerfectRecordExchangeReadout."
                    + "perfect_record_exchange_readout_vanishes"),
            H("Perfect recording eliminates the unread exchange readout"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The input rho is an arbitrary complex matrix on two addresses; no positivity, "
                        + "normalization, or diagonal hypothesis is required. The joint state is "
                        + "constructed with the repository's canonical copied-address record, and "
                        + "the unread marginal is constructed by tracing that record out.")),
                Paragraph(Text(
                    "The copied-record marginal has zero off-diagonal entries. Since qubitX has "
                        + "only off-diagonal entries, their trace pairing is zero. Thus a nonzero "
                        + "readout function cannot be the same function as this exchange pairing "
                        + "on the unread interface.")),
                Paragraph(Text(
                    "For every distinct address pair, nonzero input coherence remains nonzero in "
                        + "the matched system-record entry of the controlled joint state while the "
                        + "corresponding unread marginal entry is zero. This exposes the joint-record "
                        + "alternative using the same construction as the vanishing readout."))),
            DescribeRole.Theorem))));

    private static Formula Entry(Formula matrix, Formula i, Formula j) =>
        Seq(matrix, Underscore, Grp(i, j));

    private static Formula JointEntry(Formula matrix, Formula i, Formula j) =>
        Seq(matrix, Underscore,
            Grp(Open, i, Comma, i, Close, Comma, Open, j, Comma, j, Close));

    private static Formula ExchangePairing(Formula state) =>
        Call("Tr", Seq(state, Sp, Cdot, Sp, F.Id("qubitX")));

    private static Formula TheoremFormula()
    {
        Formula rho = Rho;
        Formula sigma = SigmaLower;
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula readout = F.Id("readout");
        Formula matrixType = F.Id("QubitMatrix");
        Formula complexType = Seq(Mathbb, Grp(F.Id("C")));
        Formula indexType = Call("Fin", D(2));
        Formula jointState = F.Id("jointState");
        Formula unreadMarginal = F.Id("unreadMarginal");
        Formula jointDefinition = Call(
            "controlledRecordJointState", F.Id("copiedAddressRecord"), rho);
        Formula unreadDefinition = Call("traceEnvironment", jointState);
        Formula exchange = ExchangePairing(unreadMarginal);
        Formula canonicalReadout = Seq(
            Open, sigma, Colon, Sp, matrixType, Sp, Mapsto, Sp,
            ExchangePairing(sigma), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, rho, Colon, Sp, matrixType, Comma, RowBreak, Grp(),
            jointState, Sp, Colon, Eq, Sp, jointDefinition, Semi, RowBreak, Grp(),
            unreadMarginal, Sp, Colon, Eq, Sp, unreadDefinition, Semi, RowBreak, Grp(),
            exchange, Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Neg, Open, exchange, Sp, Neq, Sp, D(0), Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, i, Comma, Sp, j, Colon, Sp, indexType, Comma, Sp,
            i, Sp, Neq, Sp, j, Sp, Land, Sp,
            Entry(rho, i, j), Sp, Neq, Sp, D(0), Sp, Rightarrow, RowBreak, Grp(),
            JointEntry(jointState, i, j), Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Entry(unreadMarginal, i, j), Sp, Eq, Sp, D(0), Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, readout, Colon, Sp,
            matrixType, Sp, To, Sp, complexType, Comma, Sp,
            readout, Open, unreadMarginal, Close, Sp, Neq, Sp, D(0),
            Sp, Rightarrow, RowBreak, Grp(),
            readout, Sp, Neq, Sp, canonicalReadout, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
