using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class MultiCopyErasureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("A finite independent record family keeps a nonzero coherence entry nonzero exactly when every record overlap is nonzero.",
        H("Finite Multi-Copy Record Erasure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-zero-overlap-copy-erases-a-nonzero-entry"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/MultiCopyErasure.multi_copy_erasure_quantifier"),
                H("A zero-overlap copy erases a nonzero entry"),
                StatementSource.FromAuthor(ZeroQuantifierFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a finite family of independent environment records act on one nonzero "
                    + "system matrix entry. Composing the frozen single-record channel once per "
                    + "copy multiplies that entry by the product of all record overlaps. The output "
                    + "is zero exactly when at least one copy has zero overlap at the selected pair "
                    + "of addresses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherence-survives-exactly-when-every-copy-has-nonzero-overlap"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/MultiCopyErasure.multi_copy_erasure_nonzero_iff"),
                H("Coherence survives exactly when every copy has nonzero overlap"),
                StatementSource.FromAuthor(NonzeroQuantifierFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonzero input entry, the output remains nonzero if and only if every "
                    + "record factor has nonzero overlap. Thus a family containing a zero-overlap "
                    + "copy erases the selected entry. This statement evaluates the composed "
                    + "record channel on its stated input; it does not apply another channel to "
                    + "the resulting output."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-copies-give-a-nontrivial-erasure-certificate"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/MultiCopyErasure.two_copy_erasure_certificate"),
                H("Two copies give a nontrivial erasure certificate"),
                StatementSource.FromAuthor(WitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the original equal-superposition density matrix, the family containing "
                    + "one copied-address factor has zero off-diagonal overlap in that factor, and "
                    + "its channel erases the selected entry. The counterfactual family with two "
                    + "address-independent factors is evaluated separately on the same original "
                    + "matrix and leaves its one-half entry unchanged."))),
                DescribeRole.Theorem))));

    private static Formula Overlap(Formula copy) => Seq(
        F.Id("g"), Underscore, Grp(copy), Open, F.Id("i"), Comma, F.Id("j"), Close);

    private static Formula ChannelEntry() => Seq(
        Operatorname, Grp(F.Id("channel")), Open,
        F.Id("R"), Comma, Rho, Close,
        Underscore, Grp(F.Id("ij")));

    private static Formula ZeroQuantifierFormula() => Disp(Seq(
        Rho, Underscore, Grp(F.Id("ij")), Neq, D(0), Sp, Rightarrow, RowBreak,
        ChannelEntry(), Eq, D(0), Sp, Iff, Sp,
        Exists, Sp, F.Id("k"), Comma, Sp, Overlap(F.Id("k")), Eq, D(0), Dot));

    private static Formula NonzeroQuantifierFormula() => Disp(Seq(
        Rho, Underscore, Grp(F.Id("ij")), Neq, D(0), Sp, Rightarrow, RowBreak,
        ChannelEntry(), Neq, D(0), Sp, Iff, Sp,
        Forall, Sp, F.Id("k"), Comma, Sp, Overlap(F.Id("k")), Neq, D(0), Dot));

    private static Formula WitnessFormula() => Disp(Seq(
        Rho, Underscore, Grp(D(0), D(1)), Eq, Frac, Grp(D(1)), Grp(D(2)), Sp,
        Land, Sp, Overlap(D(0)), Eq, D(0), Sp,
        Land, Sp, Overlap(D(1)), Eq, D(1), Sp, Land, RowBreak,
        Operatorname, Grp(F.Id("channel")), Open,
        F.Id("distinguishing"), Comma, Rho, Close,
        Underscore, Grp(D(0), D(1)), Eq, D(0), Sp, Land, Sp,
        Operatorname, Grp(F.Id("channel")), Open,
        F.Id("independent"), Comma, Rho, Close,
        Underscore, Grp(D(0), D(1)), Eq, Frac, Grp(D(1)), Grp(D(2)), Dot));
}
