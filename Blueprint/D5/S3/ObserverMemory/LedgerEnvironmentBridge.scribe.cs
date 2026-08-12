using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class LedgerEnvironmentBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-entry record channel is an environment marginal, while homogeneous finite record-channel composition is iterated phase damping under the same Gram rule.",
        H("Record-Environment Partial Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-one-entry-record-channel-is-the-environment-marginal"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/LedgerEnvironmentBridge.one_record_channel_is_environment_marginal"),
                H("A one-entry record channel is the environment marginal"),
                StatementSource.FromAuthor(LedgerEnvironmentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any frozen environment record whose Gram overlaps have phase-damping "
                    + "coefficient c, tracing the frozen controlled joint state is equal to the "
                    + "frozen finite-record channel indexed by the one-element type. Both sides "
                    + "exist independently of this bridge. The frozen EventHistory API exposes no "
                    + "map from the ledger opcode to an environment record, so no such semantics is "
                    + "postulated here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-record-channel-composition-is-iterated-decoherence"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/LedgerEnvironmentBridge.finite_record_channel_is_iterated_decoherence"),
                H("Finite record-channel composition is iterated decoherence"),
                StatementSource.FromAuthor(BookkeepingDecoherenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For N copies of the same normalized frozen record, the existing finite-family "
                    + "record channel equals N iterations of the existing phase-damping map. The "
                    + "common Gram-overlap premise determines the retained off-diagonal factor, so "
                    + "the statement identifies two independently frozen constructions rather than "
                    + "unfolding a newly defined history channel. This is the strongest frozen bridge; "
                    + "it does not identify EventHistory bookkeeping with quantum evolution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-copied-address-records-erase-both-coherences"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/LedgerEnvironmentBridge.record_decoherence_anti_vacuity"),
                H("Two copied-address records erase both coherences"),
                StatementSource.FromAuthor(AntiVacuityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the same equal-superposition density matrix, the one-record environment "
                    + "marginal agrees with the one-entry finite record channel. For two copied-address "
                    + "records, finite record-channel composition agrees with two zero-retention damping steps, "
                    + "preserving both one-half populations and sending both coherences to zero."))),
                DescribeRole.Theorem))));

    private static Formula Overlap(Formula record, Formula i, Formula j) => Seq(
        F.Id("g"), Underscore, Grp(record), Open, i, Comma, Sp, j, Close);

    private static Formula MultiChannel(Formula index, Formula record, Formula state) => Seq(
        Operatorname, Grp(F.Id("multiRecordChannel")), Underscore, Grp(index),
        Open, record, Comma, Sp, state, Close);

    private static Formula GramPremise() => Seq(
        Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Esc, Sp,
        Overlap(F.Id("R"), F.Id("i"), F.Id("j")), Eq, Sp,
        F.Id("if"), Sp, F.Id("i"), Eq, F.Id("j"), Sp, F.Id("then"), Sp, D(1),
        Sp, F.Id("else"), Sp, F.Id("c"));

    private static Formula LedgerEnvironmentFormula() => Disp(Seq(
        Forall, Sp, F.Id("R"), Comma, Sp, F.Id("c"), Comma, Sp, Rho, Comma, Esc, Sp,
        GramPremise(), Sp, Rightarrow, Sp, RowBreak,
        Operatorname, Grp(F.Id("tr")), Underscore, Grp(F.Id("E")), Open,
        F.Id("J"), Underscore, Grp(F.Id("R")), Open, Rho, Close, Close,
        Eq, Sp, MultiChannel(F.Id("Unit"), F.Id("R"), Rho), Dot));

    private static Formula BookkeepingDecoherenceFormula() => Disp(Seq(
        Forall, Sp, F.Id("R"), Comma, Sp, F.Id("c"), Comma, Sp, F.Id("N"), Comma,
        Sp, Rho, Comma, Esc, Sp, GramPremise(), Sp, Rightarrow, Sp, RowBreak,
        MultiChannel(Seq(F.Id("Fin"), Sp, F.Id("N")), F.Id("R"), Rho),
        Eq, Sp, Operatorname, Grp(F.Id("phaseDampingIterate")), Open,
        F.Id("c"), Comma, Sp, F.Id("N"), Comma, Sp, Rho, Close, Dot));

    private static Formula Entry(Formula state, Formula i, Formula j) => Seq(
        state, Underscore, Grp(i, j));

    private static Formula AntiVacuityFormula() => Disp(Seq(
        F.Id("rho"), Colon, Eq, Sp, Seq(Rho, Underscore, Grp(Plus)), Comma, Sp,
        F.Id("rhoB"), Colon, Eq, Sp,
        MultiChannel(Seq(F.Id("Fin"), Sp, D(2)), F.Id("copy"), F.Id("rho")), Comma, Sp,
        F.Id("rhoD"), Colon, Eq, Sp,
        Operatorname, Grp(F.Id("phaseDampingIterate")), Open,
        D(0), Comma, Sp, D(2), Comma, Sp, F.Id("rho"), Close, Comma, RowBreak,
        Operatorname, Grp(F.Id("tr")), Underscore, Grp(F.Id("E")), Open,
        F.Id("J"), Underscore, Grp(F.Id("copy")), Open, F.Id("rho"), Close, Close,
        Eq, Sp, MultiChannel(F.Id("Unit"), F.Id("copy"), F.Id("rho")), Sp, Land, Sp,
        F.Id("rhoB"), Eq, F.Id("rhoD"), Sp, Land, Sp, RowBreak,
        Entry(F.Id("rhoB"), D(0), D(0)), Eq, Frac, Grp(D(1)), Grp(D(2)), Sp, Land, Sp,
        Entry(F.Id("rhoB"), D(1), D(1)), Eq, Frac, Grp(D(1)), Grp(D(2)), Sp, Land, Sp,
        Entry(F.Id("rhoB"), D(0), D(1)), Eq, D(0), Sp, Land, Sp,
        Entry(F.Id("rhoB"), D(1), D(0)), Eq, D(0), Dot));
}
