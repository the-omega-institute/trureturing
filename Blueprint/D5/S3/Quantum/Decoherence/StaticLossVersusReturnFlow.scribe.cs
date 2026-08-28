using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class StaticLossVersusReturnFlowDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix =
        "D5/S3/Quantum/Decoherence/StaticLossVersusReturnFlow.";

    private static Formula Discarded(Formula projection, Formula matrix) =>
        F.Seq(F.Open, F.Id("I"), F.Minus, projection, F.Close, matrix);

    private static Formula HsSquared(Formula matrix) =>
        F.Seq(F.Vert, F.Sp, matrix, F.Vert, F.Caret, F.D(2));

    private static Formula StaticLoss(Formula projection, Formula matrix) =>
        HsSquared(Discarded(projection, matrix));

    private static Formula ReturnFlow(
        Formula projection,
        Formula dynamics,
        Formula matrix) =>
        F.Seq(F.Vert, F.Sp, projection, F.Open, dynamics, F.Open,
            Discarded(projection, matrix), F.Close, F.Close,
            F.Vert, F.Caret, F.D(2));

    public DocumentDefinition Create()
    {
        Formula matrix = F.Id("X");
        Formula projection = F.Id("D");
        Formula dynamics = F.Id("T");
        Formula matrixType = F.Id("QubitMatrix");
        Formula dynamicsType = F.Id("Dynamics");
        Formula diagonal = F.Seq(F.Operatorname, F.Grp(F.Id("diag")));
        Formula staticLoss = StaticLoss(projection, matrix);
        Formula returnFlow = ReturnFlow(projection, dynamics, matrix);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Concrete two-by-two witnesses separate squared static coherence loss from "
                + "squared return flow into a visible diagonal record.",
            H("Static Loss Versus Return Flow"),
            Blocks(
                Paragraph(Text(
                    "For real two-by-two matrices, the entrywise square sum is the square of "
                        + "the Frobenius, or Hilbert-Schmidt, norm. Squaring preserves zero and "
                        + "nonzero values, while turning the chosen large and small thresholds "
                        + "into one and one quarter.")),
                Paragraph(Text(
                    "The retained record is the diagonal projection. Future dynamics are real "
                        + "linear maps, which excludes a nonzero constant map from manufacturing "
                        + "a return signal without discarded input.")),
                Describe.Lean(
                    DescribeId.Create("large-static-loss-can-have-zero-return"),
                    DeclarationHandle.Create(
                        LeanPrefix + "large_static_loss_with_zero_return"),
                    H("Large static loss can have zero return"),
                    StatementSource.FromAuthor(F.Disp(F.Seq(
                        F.Exists, F.Sp, matrix, F.Comma, F.Sp, projection, F.Comma,
                        F.Sp, dynamics, F.Comma, F.Sp,
                        projection, F.Sp, F.Eq, F.Sp, diagonal, F.Sp, F.Land, F.Sp,
                        F.D(1), F.Sp, F.Leq, F.Sp, staticLoss, F.Sp, F.Land, F.Sp,
                        returnFlow, F.Sp, F.Eq, F.Sp, F.D(0)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Take one off-diagonal entry equal to two and use zero future dynamics. "
                            + "Its squared static loss is four, hence at least one, while the "
                            + "returned visible strength is exactly zero."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("small-nonzero-static-loss-can-have-nonzero-return"),
                    DeclarationHandle.Create(
                        LeanPrefix + "small_static_loss_with_nonzero_return"),
                    H("Small nonzero static loss can have nonzero return"),
                    StatementSource.FromAuthor(F.Disp(F.Seq(
                        F.Exists, F.Sp, matrix, F.Comma, F.Sp, projection, F.Comma,
                        F.Sp, dynamics, F.Comma, F.Sp,
                        projection, F.Sp, F.Eq, F.Sp, diagonal, F.Sp, F.Land, F.Sp,
                        F.D(0), F.Sp, F.Lt, F.Sp, staticLoss, F.Sp, F.Leq, F.Sp,
                        F.D(1), F.Slash, F.D(4), F.Sp, F.Land, F.Sp,
                        returnFlow, F.Sp, F.Neq, F.Sp, F.D(0)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Take one off-diagonal entry equal to one half. Its squared static loss "
                            + "is one quarter, while a linear dynamics sends that entry into the "
                            + "visible zero-zero diagonal record with nonzero strength."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("static-loss-and-return-flow-are-logically-independent"),
                    DeclarationHandle.Create(
                        LeanPrefix
                            + "static_loss_and_return_flow_are_logically_independent"),
                    H("Static loss and return flow are logically independent"),
                    StatementSource.FromAuthor(F.Disp(F.Seq(
                        F.Open, F.Neg, F.Forall, F.Sp,
                        matrix, F.Colon, F.Sp, matrixType, F.Comma, F.Sp,
                        projection, F.Comma, F.Sp, dynamics,
                        F.Colon, F.Sp, dynamicsType, F.Comma, F.Sp,
                        projection, F.Sp, F.Eq, F.Sp, diagonal, F.Sp,
                        F.Rightarrow, F.Sp, F.D(1), F.Sp, F.Leq, F.Sp, staticLoss,
                        F.Sp, F.Rightarrow, F.Sp, returnFlow, F.Sp, F.Neq, F.Sp,
                        F.D(0), F.Close, F.Sp, F.Land, F.Sp,
                        F.Open, F.Neg, F.Forall, F.Sp,
                        matrix, F.Colon, F.Sp, matrixType, F.Comma, F.Sp,
                        projection, F.Comma, F.Sp, dynamics,
                        F.Colon, F.Sp, dynamicsType, F.Comma, F.Sp,
                        projection, F.Sp, F.Eq, F.Sp, diagonal, F.Sp,
                        F.Rightarrow, F.Sp, returnFlow, F.Sp, F.Neq, F.Sp,
                        F.D(0), F.Sp, F.Rightarrow, F.Sp, F.D(1), F.Sp,
                        F.Leq, F.Sp, staticLoss, F.Close))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The two witnesses refute both universal one-way implications at the "
                            + "large threshold one. Static decoherence size and later return into "
                            + "the prediction interface are therefore different scalars."))),
                    DescribeRole.Theorem))));
    }
}
