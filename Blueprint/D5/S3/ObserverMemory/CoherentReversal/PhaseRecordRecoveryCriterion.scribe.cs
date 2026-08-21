using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.CoherentReversal;

internal sealed class PhaseRecordRecoveryCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite phase records recover exactly at unit overlap, while strict overlap contraction leaves a squared residual factor.",
        H("Phase-Record Recovery Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-phase-record-recovery-has-three-complementary-clauses"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/CoherentReversal/PhaseRecordRecoveryCriterion."
                        + "phase_record_recovery_criterion"),
                H("Finite phase-record recovery and its two obstructions"),
                StatementSource.FromAuthor(RecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a finite family of canonical environment records act on one selected "
                            + "matrix entry. If every record overlap has norm one, the imported "
                            + "all-copy reversal theorem restores that entry after every record is "
                            + "amplitude-conjugated.")),
                    Paragraph(Text(
                        "If some overlap has norm strictly below one, the same record followed by "
                            + "its conjugate record channel multiplies the entry by the squared "
                            + "overlap norm, which is still strictly below one. Consequently a "
                            + "nonzero selected entry is not restored.")),
                    Paragraph(Text(
                        "Finally, if one overlap unequal to one is left unreversed while every "
                            + "other overlap has norm one, the imported surviving-copy theorem "
                            + "shows that a nonzero selected entry is not restored. The statement "
                            + "uses the frozen record, overlap, channel, and reversal operations "
                            + "throughout; it introduces no replacement model."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula name, Formula type) => Seq(name, Colon, Sp, type);

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Overlap(Formula records, Formula copy, Formula i, Formula j) =>
        Call("recordOverlap", At(records, copy), i, j);

    private static Formula Norm(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula Entry(Formula matrix, Formula i, Formula j) =>
        Seq(matrix, Open, i, Close, Open, j, Close);

    private static Formula MultiChannel(Formula records, Formula matrix) =>
        Call("multiRecordChannel", records, matrix);

    private static Formula FullyReversed(Formula records, Formula matrix) =>
        MultiChannel(Call("reverseOn", F.Id("univ"), records), MultiChannel(records, matrix));

    private static Formula SingleConjugate(Formula records, Formula copy, Formula matrix) =>
        Call("recordChannel", Call("reverseRecord", At(records, copy)),
            Call("recordChannel", At(records, copy), matrix));

    private static Formula PartiallyReversed(Formula records, Formula copy, Formula matrix) =>
        Call("reverseChannelOn", Call("erase", F.Id("univ"), copy), records,
            MultiChannel(records, matrix));

    private static Formula RecoveryFormula()
    {
        Formula copyType = F.Id("Copy");
        Formula records = F.Id("R");
        Formula matrix = Rho;
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula k = F.Id("k");
        Formula l = F.Id("l");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula recordType = Seq(Operatorname, Grp(F.Id("EnvironmentRecord")));
        Formula matrixType = Seq(Operatorname, Grp(F.Id("QubitMatrix")));
        Formula indexType = Call("Fin", D(2));
        Formula overlapK = Overlap(records, k, i, j);
        Formula overlapL = Overlap(records, l, i, j);
        Formula normK = Norm(overlapK);
        Formula inputEntry = Entry(matrix, i, j);
        Formula singleEntry = Entry(SingleConjugate(records, k, matrix), i, j);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(copyType, type), Comma, Sp,
            OpenBracket, Call("Fintype", copyType), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", copyType), CloseBracket, Comma, RowBreak, Grp(),
            Typed(records, new Formula.TypeArrow(copyType, recordType)), Comma, Sp,
            Typed(matrix, matrixType), Comma, Sp,
            Typed(i, indexType), Comma, Sp, Typed(j, indexType), Comma, RowBreak, Grp(),
            Open,
                Open, Forall, Sp, k, Comma, Sp, normK, Sp, Eq, Sp, D(1), Close,
                Sp, Rightarrow, Sp,
                Entry(FullyReversed(records, matrix), i, j), Sp, Eq, Sp, inputEntry,
            Close, Sp, Land, RowBreak, Grp(),
            Open,
                Open, Exists, Sp, k, Comma, Sp, normK, Sp, Lt, Sp, D(1), Close,
                Sp, Rightarrow, Sp, Exists, Sp, k, Comma, RowBreak, Grp(),
                normK, Sp, Lt, Sp, D(1), Sp, Land, Sp,
                normK, Caret, Grp(D(2)), Sp, Lt, Sp, D(1), Sp, Land, RowBreak, Grp(),
                singleEntry, Sp, Eq, Sp,
                    normK, Caret, Grp(D(2)), Sp, inputEntry, Sp, Land, RowBreak, Grp(),
                Open, inputEntry, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                    singleEntry, Sp, Neq, Sp, inputEntry, Close,
            Close, Sp, Land, RowBreak, Grp(),
            Open,
                Forall, Sp, k, Comma, Sp,
                Open, Forall, Sp, l, Comma, Sp, l, Sp, Neq, Sp, k,
                    Sp, Rightarrow, Sp, Norm(overlapL), Sp, Eq, Sp, D(1), Close,
                Sp, Rightarrow, Sp, overlapK, Sp, Neq, Sp, D(1),
                Sp, Rightarrow, Sp, inputEntry, Sp, Neq, Sp, D(0),
                Sp, Rightarrow, RowBreak, Grp(),
                Entry(PartiallyReversed(records, k, matrix), i, j),
                    Sp, Neq, Sp, inputEntry,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
