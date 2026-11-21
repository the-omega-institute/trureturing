using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedNonlinearLossDocument : IScribeDocumentDefinition
{
    private static Formula X => F.Id("x");
    private static Formula I => F.Id("i");
    private static Formula B => F.Id("B");
    private static Formula Jump => Seq(Open, I, Plus, D(1), Close);
    private static Formula ProfileSq(Formula x) =>
        Seq(Call("discrepancyProfile", x), Caret, Grp(D(2)));
    private static Formula Summand => Call("lossSummand", X, I);
    private static Formula Conv => Call("lossConvolution", X);
    private static Formula SumTerms => Seq(Sum, Underscore, Grp(I, Eq, D(0)), Caret, Grp(Infty), Sp, Summand);
    private static Formula LossWeight => Call("lossWeight", I);
    private static Formula Summable(Formula index, Formula term) => Call("Summable", Seq(index, Mapsto, Sp, term));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual paired loss kernel has a uniform bound on the squared logarithmic profile.",
        H("Nonlinear loss convolution for the occupation profile"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-loss-summand"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedNonlinearLoss.lossSummand"),
                H("Paired term at positive jump size"),
                StatementSource.FromAuthor(Disp(Seq(Summand, Eq, LossWeight, Cdot, Sp,
                    ProfileSq(Seq(X, Plus, Jump)), Plus, LossWeight, Cdot, Sp, ProfileSq(Seq(X, Minus, Jump))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer origin is x. The natural index i corresponds to the positive jump i+1 in both directions. The coefficient is the actual loss weight, including its singleton correction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-loss-convolution"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedNonlinearLoss.lossConvolution"),
                H("Actual paired loss convolution"),
                StatementSource.FromAuthor(Disp(Seq(Conv, Eq, SumTerms))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The following theorem verifies that this real series is summable at every integer origin."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-loss-convolution-bound"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedNonlinearLoss.actual_loss_convolution_bound"),
                H("Uniform bound, including the origin"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Summable(X, ProfileSq(X)), Sp, Land, Sp,
                    Open, Forall, Sp, X, Comma, Sp, Summable(I, Summand), Close, Sp, Land,
                    RowBreak, Grp(),
                    Exists, Sp, B, Ge, D(0), Comma, Sp, Forall, Sp, X, Comma, Sp,
                    Conv, Le, Sp, B, Cdot, Sp, ProfileSq(X),
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The profile is taken from AbsoluteDiscrepancySeries. All occurrences of x range over the integers, and the one nonnegative constant B controls every x, including zero.")),
                    Paragraph(Text("The square is summable by the decreasing integral test for the shifted inverse log-square function. When the shifted location has absolute value at least half the incoming absolute value, their squared profiles are directly comparable. Otherwise the jump size is at least half the incoming distance, so the strict coefficient remainder supplies a power bound and summability controls the shifted profile mass. At the origin the far case cannot occur."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
