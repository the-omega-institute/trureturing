using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class ProjectionCommutatorIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complementary split expresses a commutator through its two directed cross blocks, and projection commutation is exactly their joint vanishing.",
        H("Projection Commutator Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("commutator-is-the-difference-of-directed-cross-blocks"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity."
                        + "commutator_eq_cross_blocks"),
                H("The commutator is the difference of the directed cross blocks"),
                StatementSource.FromAuthor(CommutatorCrossBlocksFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In any possibly noncommutative ring, let Q be the complement 1 minus P. "
                            + "Then P times T minus T times P equals the P-to-Q cross term "
                            + "minus the Q-to-P cross term.")),
                    Paragraph(Text(
                        "Inserting P plus Q as the identity on both sides separates the two "
                            + "diagonal PTP terms, which cancel. No idempotence or nondegeneracy "
                            + "condition on P is required, so the identity also includes the "
                            + "degenerate complements P = 0 and P = 1 and the zero ring."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("visible-projection-commutes-iff-cross-blocks-vanish"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity."
                        + "visible_projection_commutes_iff_cross_blocks_eq_zero"),
                H("Visible projection commutes exactly when both cross blocks vanish"),
                StatementSource.FromAuthor(ProjectionCommutationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For complementary subspaces V and R of a finite complex coordinate "
                            + "space, the matrix of the projection onto V along R commutes with T "
                            + "exactly when both directed cross-component maps are zero.")),
                    Paragraph(Text(
                        "The visible-after-T-after-hidden block measures flow from R into V, while "
                            + "the hidden-after-T-after-visible block measures flow from V into R. "
                            + "Their simultaneous vanishing is the reducing condition, so it is "
                            + "equivalent to projection commutation."))),
                DescribeRole.Lemma))));

    private static Formula IsCompl(Formula visible, Formula hidden) =>
        Call("IsCompl", visible, hidden);

    private static Formula VisibleProjection(
        Formula visible,
        Formula hidden,
        Formula witness) =>
        Call("visibleProjection", visible, hidden, witness);

    private static Formula HiddenProjection(
        Formula visible,
        Formula hidden,
        Formula witness) =>
        Call("hiddenProjection", visible, hidden, witness);

    private static Formula VisibleProjectionMatrix(
        Formula visible,
        Formula hidden,
        Formula witness) =>
        Call("visibleProjectionMatrix", visible, hidden, witness);

    private static Formula MatrixToLinear(Formula matrix) =>
        Call("matrixToLinear", matrix);

    private static Formula Compose(Formula first, Formula middle, Formula last) =>
        Seq(first, Sp, Circ, Sp, middle, Sp, Circ, Sp, last);

    private static Formula CommutatorCrossBlocksFormula()
    {
        Formula algebra = F.Id("A");
        Formula projection = F.Id("P");
        Formula complement = F.Id("Q");
        Formula map = F.Id("T");
        Formula complementEquation = Equal(complement, Subtract(D(1), projection));
        Formula commutator = Subtract(
            Multiply(projection, map),
            Multiply(map, projection));
        Formula crossBlocks = Subtract(
            Multiply(Multiply(projection, map), complement),
            Multiply(Multiply(complement, map), projection));

        return Disp(Seq(
            Forall, Sp, algebra, Comma, Sp,
            OpenBracket, Call("Ring", algebra), CloseBracket, Comma, Sp,
            Forall, Sp, projection, Comma, Sp, complement, Comma, Sp, map,
            Sp, InMacro, Sp, algebra, Comma, Sp,
            complementEquation, Sp, Rightarrow, Sp,
            Equal(commutator, crossBlocks), Dot));
    }

    private static Formula ProjectionCommutationFormula()
    {
        Formula visible = F.Id("V");
        Formula hidden = F.Id("R");
        Formula witness = F.Id("h");
        Formula matrix = F.Id("T");
        Formula projection = VisibleProjectionMatrix(visible, hidden, witness);
        Formula matrixMap = MatrixToLinear(matrix);
        Formula visibleHidden = Compose(
            VisibleProjection(visible, hidden, witness),
            matrixMap,
            HiddenProjection(visible, hidden, witness));
        Formula hiddenVisible = Compose(
            HiddenProjection(visible, hidden, witness),
            matrixMap,
            VisibleProjection(visible, hidden, witness));

        return Disp(Seq(
            Forall, Sp, visible, Comma, Sp, hidden, Comma, Sp,
            witness, Colon, Sp, IsCompl(visible, hidden), Comma, Sp,
            matrix, Comma, Sp,
            Equal(Multiply(projection, matrix), Multiply(matrix, projection)),
            Sp, Iff, Sp,
            Open, Equal(visibleHidden, D(0)), Sp, Land, Sp,
            Equal(hiddenVisible, D(0)), Close, Dot));
    }
}
