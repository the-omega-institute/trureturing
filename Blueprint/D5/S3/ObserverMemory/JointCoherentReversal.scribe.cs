using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class JointCoherentReversalDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/ObserverMemory/JointCoherentReversal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Amplitude conjugation reverses unimodular record-overlap phases under composed finite-record channels.",
        H("Joint Reversal of Unimodular Record Phases"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reversing-all-record-copies-restores-the-original-entry"),
                DeclarationHandle.Create(LeanPrefix + "joint_coherent_reversal"),
                H("Reversing all unimodular record phases restores the selected entry"),
                StatementSource.FromAuthor(AllCopiesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a finite family of record factors act through the imported product "
                        + "channel. The record operation reverseRecord conjugates every complex "
                        + "amplitude of the selected existing record; reverse_record_overlap proves "
                        + "that this conjugates its Gram overlap. If conjugate(g_k) times g_k is "
                        + "one for every copy at the selected addresses, the reversed-family "
                        + "channel is applied to the output of the original-family channel and the "
                        + "two overlap products cancel.")),
                    Paragraph(Text(
                        "This proves entrywise recovery only for the displayed unimodular-overlap "
                        + "family inside the deposited record-vector model. That frozen model does "
                        + "not expose record-generating unitaries, so the theorem does not construct "
                        + "an inverse unitary interaction or provide a recovery guarantee outside "
                        + "the stated overlap hypothesis. It makes no claim about inverting an "
                        + "arbitrary traced physical channel.")),
                    Paragraph(Text(
                        "The proof reuses the frozen finite-copy channel equation. Local library "
                        + "searches checked map_sum, map_mul, Finset.prod_mul_distrib, "
                        + "Finset.prod_ite, and Complex.I_mul_I. The imported structure exposes no "
                        + "record-generating unitary inverse."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-surviving-phase-copy-blocks-restoration"),
                DeclarationHandle.Create(LeanPrefix + "surviving_copy_blocks_reversal"),
                H("One surviving phase copy blocks restoration"),
                StatementSource.FromAuthor(SurvivingCopyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reverse every copy except k and assume the other overlaps obey the same "
                    + "unimodularity law. The composed channel then multiplies the original entry "
                    + "by the surviving overlap g_k. If that overlap is not one and the input "
                    + "entry is nonzero, "
                    + "the result differs from the input. This is an entrywise obstruction for one "
                    + "surviving record factor, not a general no-recoherence theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-copies-separate-partial-from-joint-reversal"),
                DeclarationHandle.Create(LeanPrefix + "two_copy_joint_reversal_certificate"),
                H("Two copies separate partial from joint reversal"),
                StatementSource.FromAuthor(TwoCopyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take two identical phase records whose zero-one overlap is minus i and the "
                    + "normalized equal-superposition density matrix. The original two-record "
                    + "channel changes its one-half entry to minus one-half. Applying only the "
                    + "copy-zero conjugate channel gives minus i over two, while applying "
                    + "the fully conjugated family channel to that same channel output restores "
                    + "one-half. This witnesses reversible phase cancellation, not recovery of "
                    + "zero-overlap decoherence."))),
                DescribeRole.Theorem))));

    private static Formula Reverse(Formula copies, Formula records) => Seq(
        Operatorname, Grp(F.Id("reverse")), Open,
        copies, Comma, Sp, records, Close);

    private static Formula Channel(Formula records, Formula matrix) => Seq(
        Operatorname, Grp(F.Id("channel")), Open,
        records, Comma, Sp, matrix, Close);

    private static Formula Entry(Formula matrix, Formula i, Formula j) => Seq(
        matrix, Underscore, Grp(i, j));

    private static Formula Overlap(Formula copy, Formula i, Formula j) => Seq(
        F.Id("g"), Underscore, Grp(copy), Open, i, Comma, Sp, j, Close);

    private static Formula Conjugate(Formula value) => Seq(Overline, Grp(value));

    private static Formula UnitOverlap(Formula copy, Formula i, Formula j) => Seq(
        Conjugate(Overlap(copy, i, j)), Sp, Overlap(copy, i, j), Eq, D(1));

    private static Formula AllCopiesFormula()
    {
        Formula records = F.Id("R");
        Formula matrix = Rho;
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        return Disp(Seq(
            Forall, Sp, records, Comma, Sp, matrix, Comma, Sp, i, Comma, Sp, j, Comma, Esc,
            Open, Forall, Sp, F.Id("k"), Comma, Esc,
            UnitOverlap(F.Id("k"), i, j), Close, Sp, Rightarrow, RowBreak,
            Entry(Channel(Reverse(F.Id("all"), records), Channel(records, matrix)), i, j),
            Eq, Entry(matrix, i, j), Dot));
    }

    private static Formula SurvivingCopyFormula()
    {
        Formula records = F.Id("R");
        Formula matrix = Rho;
        Formula copy = F.Id("k");
        Formula other = F.Id("l");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula allExceptCopy = Seq(F.Id("all"), Setminus, OpenBrace, copy, CloseBrace);
        return Disp(Seq(
            Open, Forall, Sp, other, Comma, Esc, other, Neq, Sp, copy, Sp, Rightarrow, Sp,
            UnitOverlap(other, i, j), Close, Sp, Land, Sp,
            Overlap(copy, i, j), Neq, D(1), Sp, Land, Sp,
            Entry(matrix, i, j), Neq, D(0), Sp, Rightarrow, RowBreak,
            Entry(Channel(Reverse(allExceptCopy, records), Channel(records, matrix)), i, j),
            Neq, Entry(matrix, i, j), Dot));
    }

    private static Formula TwoCopyFormula()
    {
        Formula records = Seq(F.Id("R"), Underscore, Grp(F.Id("two")));
        Formula entry = Entry(Rho, D(0), D(1));
        return Disp(Seq(
            entry, Eq, Frac, Grp(D(1)), Grp(D(2)), Sp, Land, RowBreak,
            Entry(Channel(records, Rho), D(0), D(1)), Eq,
            Minus, Frac, Grp(D(1)), Grp(D(2)), Sp, Land, RowBreak,
            Entry(Channel(Reverse(Seq(OpenBrace, D(0), CloseBrace), records),
                Channel(records, Rho)), D(0), D(1)), Eq,
            Minus, F.Id("i"), Frac, Grp(D(1)), Grp(D(2)), Sp, Land, RowBreak,
            Entry(Channel(Reverse(F.Id("all"), records), Channel(records, Rho)), D(0), D(1)),
            Eq, Frac, Grp(D(1)), Grp(D(2)), Dot));
    }
}
