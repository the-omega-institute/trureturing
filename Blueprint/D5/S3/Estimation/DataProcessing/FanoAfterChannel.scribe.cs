using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class FanoAfterChannelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Fano inversion and Markov data processing give estimator-error floors after " +
            "arbitrary finite garbling and after explicit row-stochastic channels.",
        H("Fano Error Bounds after Finite Channels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("markov-garbling-preserves-the-pre-channel-fano-floor"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/FanoAfterChannel.fano_error_probability_lower_bound_of_markov"),
                H("Markov garbling preserves the pre-channel Fano floor"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("X"), Comma, Sp, F.Id("Y"), Comma, Sp, F.Id("Z"), Comma,
                    RowBreak,
                    F.Id("p"), Colon, Sp, F.Id("X"), Times, Sp,
                    Open, F.Id("Y"), Times, Sp, F.Id("Z"), Close, To, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("g"), Colon, Sp, F.Id("Z"), To, Sp, F.Id("X"), Comma, RowBreak,
                    Open,
                    Open,
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp, F.Id("z"), Comma,
                    Sp, D(0), Leq, Sp,
                    F.Id("p"), Open, F.Id("x"), Comma, Sp,
                    Open, F.Id("y"), Comma, Sp, F.Id("z"), Close, Close,
                    Close, Sp, Land, Sp,
                    Sum, Sp, Underscore,
                    Grp(F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp, F.Id("z")), Sp,
                    F.Id("p"), Open, F.Id("x"), Comma, Sp,
                    Open, F.Id("y"), Comma, Sp, F.Id("z"), Close, Close,
                    Eq, Sp, D(1), Close, Sp, Land, Sp, RowBreak,
                    Open,
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp, F.Id("z"), Comma,
                    Sp,
                    F.Id("p"), Open, F.Id("x"), Comma, Sp,
                    Open, F.Id("y"), Comma, Sp, F.Id("z"), Close, Close, Times, Sp,
                    Operatorname, Grp(F.Id("marginal")), Open,
                    Operatorname, Grp(F.Id("yFirstLaw")), Open, F.Id("p"), Close, Close,
                    Open, F.Id("y"), Close, Eq, Sp,
                    Operatorname, Grp(F.Id("xyProjection")), Open, F.Id("p"), Close,
                    Open, F.Id("x"), Comma, Sp, F.Id("y"), Close, Times, Sp,
                    Operatorname, Grp(F.Id("xzProjection")), Open,
                    Operatorname, Grp(F.Id("yFirstLaw")), Open, F.Id("p"), Close, Close,
                    Open, F.Id("y"), Comma, Sp, F.Id("z"), Close,
                    Close, Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("p"), Close,
                    Open, F.Id("x"), Close, Eq, Sp,
                    Frac, Grp(D(1)),
                    Grp(Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close), Close,
                    Sp, Land, Sp, D(2), Leq, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close,
                    Close, Sp, Rightarrow, Sp, RowBreak,
                    D(1), Minus, Sp,
                    Frac,
                    Grp(
                        Operatorname, Grp(F.Id("mutualInformation")), Open,
                        Operatorname, Grp(F.Id("xyProjection")), Open, F.Id("p"), Close, Close,
                        Plus, Sp, Log, Sp, D(2)),
                    Grp(Log, Sp,
                        Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close),
                    Leq, Sp,
                    Sum, Sp, Underscore,
                    Grp(
                        F.Id("x"), Comma, Sp, F.Id("z"), Colon, Sp,
                        F.Id("g"), Open, F.Id("z"), Close, Neq, Sp, F.Id("x")), Sp,
                    Operatorname, Grp(F.Id("xzProjection")), Open, F.Id("p"), Close,
                    Open, F.Id("x"), Comma, Sp, F.Id("z"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be a normalized nonnegative law on the right-nested product " +
                            "X times (Y times Z). The theorem keeps the Markov assumption in the " +
                            "repository's raw cross-multiplied form: p(x,y,z) times the Y marginal " +
                            "equals the XY marginal times the YZ marginal. No conditional division " +
                            "or named Markov predicate is introduced.")),
                    Paragraph(Text(
                        "The estimator sees only Z. To apply the frozen Fano endpoint, the proof " +
                            "swaps the XZ projection into the observation-first order Z times X. " +
                            "It verifies normalization after that swap, transports the uniform X " +
                            "marginal, and uses mutual-information symmetry to identify the swapped " +
                            "information term with I(X;Z).")),
                    Paragraph(Text(
                        "Fano then lower-bounds the estimator's XZ error using I(X;Z). The Markov " +
                            "data-processing inequality gives I(X;Z) <= I(X;Y), and positivity of " +
                            "log(card X), supplied exactly by 2 <= card X, makes substitution of the " +
                            "larger pre-garbling information budget order-correct."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("row-stochastic-channels-inherit-the-pre-channel-fano-floor"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/FanoAfterChannel.fano_error_probability_lower_bound_after_channel"),
                H("Row-stochastic channels inherit the pre-channel Fano floor"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("pXY"), Comma, Sp, F.Id("W"), Comma, Sp, F.Id("g"), Comma,
                    RowBreak,
                    Open,
                    Open,
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    D(0), Leq, Sp,
                    F.Id("pXY"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Close, Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("x"), Comma, Sp, F.Id("y")), Sp,
                    F.Id("pXY"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, Sp, D(1), Close, Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("y"), Comma, Sp, F.Id("z"), Comma, Sp,
                    D(0), Leq, Sp, F.Id("W"), Open, F.Id("y"), Comma, Sp, F.Id("z"), Close,
                    Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("y"), Comma, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("z")), Sp,
                    F.Id("W"), Open, F.Id("y"), Comma, Sp, F.Id("z"), Close,
                    Eq, Sp, D(1), Close, Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("pXY"), Close,
                    Open, F.Id("x"), Close, Eq, Sp,
                    Frac, Grp(D(1)),
                    Grp(Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close), Close,
                    Sp, Land, Sp, D(2), Leq, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close,
                    Close, Sp, Rightarrow, Sp, RowBreak,
                    D(1), Minus, Sp,
                    Frac,
                    Grp(
                        Operatorname, Grp(F.Id("mutualInformation")), Open, F.Id("pXY"), Close,
                        Plus, Sp, Log, Sp, D(2)),
                    Grp(Log, Sp,
                        Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close),
                    Leq, Sp,
                    Sum, Sp, Underscore,
                    Grp(
                        F.Id("x"), Comma, Sp, F.Id("z"), Colon, Sp,
                        F.Id("g"), Open, F.Id("z"), Close, Neq, Sp, F.Id("x")), Sp,
                    Sum, Sp, Underscore, Grp(F.Id("y")), Sp,
                    F.Id("pXY"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close, Times, Sp,
                    F.Id("W"), Open, F.Id("y"), Comma, Sp, F.Id("z"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The explicit channel law is p(x,y,z) = pXY(x,y) W(y,z). The input joint " +
                            "pXY is a normalized nonnegative law with a uniform X marginal, while W " +
                            "is pointwise nonnegative and every row sums to one. The estimator g is " +
                            "otherwise arbitrary.")),
                    Paragraph(Text(
                        "Row normalization does all of the transport work. Summing the generated " +
                            "joint over Z recovers pXY, so the generated law has total mass one, its " +
                            "X marginal remains uniform, and its XY projection has exactly the " +
                            "pre-channel mutual information appearing in the displayed floor.")),
                    Paragraph(Text(
                        "The existing channel lemma supplies the raw Markov identity for the " +
                            "generated joint. Applying the preceding theorem therefore bounds the " +
                            "error mass of every estimator based on the garbled output Z by the " +
                            "information available before the channel. No invertibility, positivity " +
                            "of individual channel entries, or estimator construction is assumed."))),
                DescribeRole.Theorem))));
}
