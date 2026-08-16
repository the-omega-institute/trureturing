using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class RecordFixedCenterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The center of a record-block algebra is exactly its block-scalar range.",
        H("The Center of a Record-Block Algebra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("record-block-center-is-the-block-scalar-range"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/RecordFixedCenter."
                    + "record_fixed_center_eq_block_scalars"),
                H("The record-block center is the block-scalar range"),
                StatementSource.FromAuthor(RecordFixedCenterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Lambda index the record-indistinguishability classes and let I "
                            + "alpha be the finite set of addresses in class alpha. Under the "
                            + "preceding fixed-algebra decomposition, the fixed algebra is the "
                            + "product of the full matrix algebras on these blocks. The source "
                            + "address set, hence its label set, is finite, so this product is "
                            + "the source statement's finite direct sum.")),
                    Paragraph(Text(
                        "Mathlib identifies the center of a product pointwise and identifies "
                            + "the center of every full complex matrix algebra with its scalar "
                            + "matrices. Choosing the scalar in each block gives exactly the "
                            + "range of recordCenterScalar, and every such block-scalar family "
                            + "is central.")),
                    Paragraph(Text(
                        "The coordinate alpha is therefore the independently variable classical "
                            + "record label. The matrix block on I alpha remains unrestricted in "
                            + "the fixed algebra, while its center retains only a scalar multiple "
                            + "of the identity; this is the unresolved internal quantum freedom "
                            + "described by the source corollary."))),
                DescribeRole.Theorem))));

    private static Formula RecordFixedCenterFormula()
    {
        Formula block = Seq(F.Id("I"), Underscore, Grp(Alpha));
        Formula matrixBlock = Seq(
            F.Id("M"), Underscore, Grp(block), Open,
            Mathbb, Grp(F.Id("C")), Close);
        Formula blockProduct = Seq(
            Prod, Underscore, Grp(Alpha, InMacro, Sp, Lambda), Sp, matrixBlock);

        return Disp(Seq(
            Forall, Sp, Lambda, Comma, Sp, F.Id("I"), Comma, Esc,
            OpenBracket, Forall, Sp, Alpha, Comma, Sp,
            Operatorname, Grp(F.Id("Fintype")), Open, block, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Forall, Sp, Alpha, Comma, Sp,
            Operatorname, Grp(F.Id("DecidableEq")), Open, block, Close,
            CloseBracket, Comma, Esc,
            F.Id("Z"), Open, blockProduct, Close, Sp, Eq, Sp,
            Operatorname, Grp(F.Id("range")), Open,
            Operatorname, Grp(F.Id("recordCenterScalar")), Underscore,
            Grp(F.Id("I")), Close, Dot));
    }
}
