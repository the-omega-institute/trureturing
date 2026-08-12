using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class ConditioningDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite projective record measurements preserve trace and define idempotent unread conditioning.",
        H("Finite Record Conditioning"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("record-weights-sum-to-the-original-trace"),
                DeclarationHandle.Create("D5/S3/Observer/Conditioning.recordWeight_sum"),
                H("Record weights sum to the original trace"),
                StatementSource.FromAuthor(RecordWeightSumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Let n and kappa be finite index types, let rho be an arbitrary complex "
                                    + "n-by-n matrix, and let P be a complete pairwise orthogonal family of "
                                    + "self-adjoint idempotents. The record weight w_k(rho) is the Born weight "
                                    + "trace(rho P_k). Linearity of trace and the completeness identity "
                                    + "sum_k P_k = 1 give the displayed normalization. No positivity, "
                                    + "Hermiticity, or trace-one premise is imposed on rho."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("discarding-the-record-preserves-trace"),
                DeclarationHandle.Create("D5/S3/Observer/Conditioning.unreadState_trace"),
                H("Discarding the record preserves trace"),
                StatementSource.FromAuthor(UnreadTraceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "The unread matrix U_P(rho) is the finite sum of the diagonal record "
                                    + "compressions P_k rho P_k. Cyclicity of trace and P_k squared equal to "
                                    + "P_k reduce each compressed trace to w_k(rho); the record-weight sum "
                                    + "then recovers trace(rho). This is an algebraic trace-preservation "
                                    + "statement for arbitrary rho, not a claim that the file develops a "
                                    + "general completely positive channel theory."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("forgetting-the-record-is-idempotent"),
                DeclarationHandle.Create("D5/S3/Observer/Conditioning.unreadState_idempotent"),
                H("Forgetting the record is idempotent"),
                StatementSource.FromAuthor(UnreadIdempotentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Pairwise orthogonality removes every cross-record block when U_P is "
                                    + "applied a second time, while projection idempotence leaves each "
                                    + "diagonal block unchanged. Consequently repeated unread measurement "
                                    + "equals one unread measurement. The result again requires no state "
                                    + "positivity or normalization assumption."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("unread-fixed-points-have-no-off-diagonal-record-blocks"),
                DeclarationHandle.Create("D5/S3/Observer/Conditioning.unreadState_fixed_iff"),
                H("Unread fixed points have no off-diagonal record blocks"),
                StatementSource.FromAuthor(UnreadFixedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "A matrix is fixed by U_P exactly when every block P_k rho P_l with "
                                    + "distinct record labels vanishes. In the forward direction, compressing "
                                    + "the fixed-point identity isolates an off-diagonal block and "
                                    + "orthogonality kills it. Conversely, completeness expands rho into "
                                    + "record columns; removing the off-diagonal columns leaves precisely the "
                                    + "sum defining U_P(rho). The equivalence concerns arbitrary complex "
                                    + "matrices, not only density matrices."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("nonzero-conditional-branches-are-states"),
                DeclarationHandle.Create("D5/S3/Observer/Conditioning.conditionalState_isState"),
                H("Nonzero conditional branches are states"),
                StatementSource.FromAuthor(ConditionalStateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Assume rho is positive semidefinite with trace one and the selected "
                                    + "record weight is nonzero. Self-adjointness of P_k makes the compression "
                                    + "P_k rho P_k positive semidefinite, while the Born-weight theorem makes "
                                    + "w_k(rho) nonnegative. Scaling by its inverse therefore preserves "
                                    + "positivity, and the compressed trace cancels the nonzero weight to give "
                                    + "trace one. The definition uses a totalized inverse, but this theorem "
                                    + "explicitly excludes a zero-weight outcome."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-unread-matrix-is-the-weighted-conditional-ensemble"),
                DeclarationHandle.Create("D5/S3/Observer/Conditioning.unread_eq_weighted_ensemble"),
                H("The unread matrix is the weighted conditional ensemble"),
                StatementSource.FromAuthor(WeightedEnsembleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "For a positive semidefinite rho, a zero record weight forces the corresponding "
                                    + "positive compressed block P_k rho P_k to have zero trace and hence vanish. "
                                    + "For every nonzero weight, multiplication by w_k(rho) cancels the inverse in "
                                    + "rho_k. Thus every term agrees with its unread compression and summing gives "
                                    + "U_P(rho), without excluding zero-weight outcomes or requiring trace-one "
                                    + "normalization."))),
                DescribeRole.Theorem
            ))));

    private static Formula RecordWeightSumFormula() => Disp(Seq(
        Ambient(),
        RecordPremise(), Sp, Rightarrow, Sp,
        Sum, Underscore, Grp(F.Id("k"), InMacro, Kappa),
        Weight(), Eq, Operatorname, Grp(F.Id("tr")), Open, Rho, Close,
        Comma, Quad, Sp,
        Weight(), Colon, Eq,
        Operatorname, Grp(F.Id("tr")), Open, Rho, Sp, Projection(), Close, Dot));

    private static Formula UnreadTraceFormula() => Disp(Seq(
        Ambient(),
        RecordPremise(), Sp, Rightarrow, Sp,
        Operatorname, Grp(F.Id("tr")), Open, Unread(Rho), Close,
        Eq, Operatorname, Grp(F.Id("tr")), Open, Rho, Close,
        Comma, RowBreak,
        Unread(Rho), Colon, Eq,
        Sum, Underscore, Grp(F.Id("k"), InMacro, Kappa),
        Projection(), Sp, Rho, Sp, Projection(), Dot));

    private static Formula UnreadIdempotentFormula() => Disp(Seq(
        Ambient(),
        RecordPremise(), Sp, Rightarrow, Sp,
        Unread(Unread(Rho)), Eq, Unread(Rho), Dot));

    private static Formula UnreadFixedFormula() => Disp(Seq(
        Ambient(),
        RecordPremise(), Sp, Rightarrow, Sp,
        Unread(Rho), Eq, Rho, Sp, Leftrightarrow, Sp,
        Forall, Sp, F.Id("k"), Comma, F.Id("l"), InMacro, Kappa, Comma, Esc,
        F.Id("k"), Neq, Sp, F.Id("l"), Sp, Rightarrow, Sp,
        Projection(), Sp, Rho, Sp, ProjectionAt(F.Id("l")), Eq, D(0), Dot));

    private static Formula ConditionalStateFormula() => Disp(Seq(
        Ambient(),
        Forall, Sp, F.Id("k"), InMacro, Kappa, Comma, Esc,
        RecordPremise(), Sp, Land, Sp,
        Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close,
        Sp, Land, Sp,
        Operatorname, Grp(F.Id("tr")), Open, Rho, Close, Eq, D(1),
        Sp, Land, Sp, Weight(), Neq, Sp, D(0), Sp, Rightarrow, RowBreak,
        Operatorname, Grp(F.Id("PosSemidef")), Open, Branch(), Close,
        Sp, Land, Sp,
        Operatorname, Grp(F.Id("tr")), Open, Branch(), Close, Eq, D(1),
        Comma, RowBreak,
        Branch(), Colon, Eq, Weight(), Caret, Grp(Minus, D(1)), Cdot, Sp,
        Projection(), Sp, Rho, Sp, Projection(), Dot));

    private static Formula WeightedEnsembleFormula() => Disp(Seq(
        Ambient(),
        RecordPremise(), Sp, Land, Sp,
        Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close,
        Sp, Rightarrow, RowBreak,
        Unread(Rho), Eq,
        Sum, Underscore, Grp(F.Id("k"), InMacro, Kappa),
        Weight(), Cdot, Sp, Branch(),
        Comma, RowBreak,
        Branch(), Colon, Eq, Weight(), Caret, Grp(Minus, D(1)), Cdot, Sp,
        Projection(), Sp, Rho, Sp, Projection(), Dot));

    private static Formula Ambient() => Seq(
        Forall, Sp, F.Id("n"), Comma, Kappa, Esc,
        OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("n"), Close,
        CloseBracket, Esc,
        OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
        CloseBracket, Comma, RowBreak,
        Forall, Sp, F.Id("P"), Colon, Sp, Kappa, To, Sp, MatrixType(), Comma, Esc,
        Rho, InMacro, Sp, MatrixType(), Comma, RowBreak);

    private static Formula MatrixType() => Seq(
        F.Id("M"), Underscore, Grp(F.Id("n")),
        Open, Mathbb, Grp(F.Id("C")), Close);

    private static Formula RecordPremise() => Seq(
        Operatorname, Grp(F.Id("Record")), Open, F.Id("P"), Close);

    private static Formula Weight() => Seq(
        F.Id("w"), Underscore, Grp(F.Id("k")), Open, Rho, Close);

    private static Formula Projection() => ProjectionAt(F.Id("k"));

    private static Formula ProjectionAt(Formula index) => Seq(
        F.Id("P"), Underscore, Grp(index));

    private static Formula Branch() => Seq(
        Rho, Underscore, Grp(F.Id("k")));

    private static Formula Unread(Formula argument) => Seq(
        F.Id("U"), Underscore, Grp(F.Id("P")), Open, argument, Close);
}
