using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class ExplicitHyperbolicDegreeThresholdDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A closed natural cutoff makes a faster positive hyperbolic orbit dominate a "
            + "bounded tail.",
        H("Explicit Hyperbolic Degree Threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("explicit-hyperbolic-degree-threshold"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/ExplicitHyperbolicDegreeThreshold."
                        + "explicit_hyperbolic_degree_threshold"),
                H("The faster hyperbolic orbit dominates beyond a closed cutoff"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The cutoff is the natural floor of the larger of two explicit "
                            + "real bounds, plus one. The reciprocal-rate term forces the "
                            + "target argument above one, while the coefficient term makes "
                            + "the exponential rate gap absorb the nonnegative tail constant.")),
                    Paragraph(Text(
                        "The proof first derives the two-sided estimate "
                            + "(exp(x)-1)/2 <= sinh(x) <= exp(x)/2 for positive x. It then "
                            + "uses exp(x)/4 <= sinh(x) for x at least one and the elementary "
                            + "strict bound x < exp(x) to compare the squared terms.")),
                    Paragraph(Text(
                        "For kappa-zero = 1, kappa-one = 1/2, delta = 1, and C = 100, "
                            + "the formal cutoff evaluates to 401. The module verifies the "
                            + "strict comparison at degrees 401 and 402, and proves that the "
                            + "same comparison is false at degree one."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula kappaZero = new Formula.Subscript(Kappa, D(0));
        Formula kappaOne = new Formula.Subscript(Kappa, D(1));
        Formula delta = Delta;
        Formula coefficient = F.Id("C");
        Formula degree = F.Id("N");
        Formula threshold = new Formula.Subscript(F.Id("N"), D(0));
        Formula rateGap = Seq(Open, kappaZero, Sp, Minus, Sp, kappaOne, Close);
        Formula deltaSquare = Square(delta);
        Formula cutoff = Seq(
            new Formula.Floor(Call(
                "max",
                new Formula.Fraction(D(1), kappaZero),
                new Formula.Fraction(
                    Product(D(2), coefficient),
                    Product(deltaSquare, rateGap)))),
            Sp, Plus, Sp, D(1));
        Formula tail = Call("sinh", Product(degree, kappaOne));
        Formula target = Call("sinh", Product(degree, kappaZero));

        return Disp(new Formula.Aligned([
            Seq(threshold, Sp, Eq, Sp, cutoff, Comma),
            Seq(Forall, Sp, kappaZero, Comma, Sp, kappaOne, Comma, Sp,
                delta, Comma, Sp, coefficient, Sp, InMacro, Sp,
                RealNumbers(), Comma, Sp, degree, Sp, InMacro, Sp,
                NaturalNumbers(), Comma),
            Seq(D(0), Sp, Lt, Sp, kappaOne, Sp, Lt, Sp, kappaZero,
                Sp, Land, Sp, D(0), Sp, Lt, Sp, delta,
                Sp, Land, Sp, D(0), Sp, Le, Sp, coefficient,
                Sp, Land, Sp, threshold, Sp, Le, Sp, degree,
                Sp, Rightarrow),
            Seq(Product(coefficient, Square(tail)), Sp, Lt, Sp,
                Product(deltaSquare, Square(target)), Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula NaturalNumbers() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula RealNumbers() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Square(Formula value) =>
        new Formula.Power(value, D(2));

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);
}
