using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class ArchimedeanObserverProductPositiveDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaGamma/ArchimedeanObserverProductPositive."
            + "archimedean_observer_product_positive";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonzero regulator mode has a strictly positive Archimedean observer product.",
        H("Archimedean Observer-Product Positivity"),
        Blocks(Describe.Lean(
            DescribeId.Create("archimedean-observer-product-positive"),
            DeclarationHandle.Create(Declaration),
            H("Nonzero modes have positive Archimedean cost"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a positive offset sigma and a nonzero regulator mode tau, every "
                        + "summand is nonnegative and the zeroth summand is strictly positive.")),
                Paragraph(Text(
                    "The logarithm is bounded above by its nonnegative increment, while the "
                        + "increments are controlled by the convergent p-series of exponent "
                        + "two. Summability and the positive zeroth term therefore make the "
                        + "entire infinite sum strictly positive."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula tau = F.Id("tau");
        Formula index = F.Id("m");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula tauSquared = Seq(tau, Caret, Grp(D(2)));
        Formula scale = Seq(sigma, Sp, Plus, Sp, D(2), index);
        Formula scaleSquared = Seq(Open, scale, Close, Caret, Grp(D(2)));
        Formula summand = Call("log", Seq(
            D(1), Sp, Plus, Sp,
            new Formula.Fraction(tauSquared, scaleSquared)));
        Formula tower = Seq(
            Sum, Underscore, Grp(index, Eq, D(0)), Caret, Grp(Infty), Sp, summand);
        Formula tauNonzero = new Formula.Not(
            new Formula.Relation(tau, FormulaRelationOperator.Equal, D(0)));

        return Disp(Seq(
            Forall, Sp, sigma, Comma, Sp, tau, InMacro, Sp, reals, Comma, Sp,
            D(0), Sp, Lt, Sp, sigma, Comma, Sp, tauNonzero, Sp, Rightarrow, Sp,
            D(0), Sp, Lt, Sp, tower, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
