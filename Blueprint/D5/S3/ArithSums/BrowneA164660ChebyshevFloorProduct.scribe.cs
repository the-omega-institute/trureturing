using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class BrowneA164660ChebyshevFloorProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/browne2016a164660");
    private const string SourceFormula =
        "a(n+1) = Product_{k=1..n} ( 1-2*(floor(k^n/n)-floor((k^n -1)/n)) ) = (-1)^(A003557(n)) for n>0 (conjecture). - _Anthony Browne_, May 29 2016";
    private const string SourceRow =
        "a(n) = numerator(Sum_{m=1..n+1} IT(n,m)), n>=0, with IT(n,m):= A164658(n,m)/A164659(n,m) (coefficient triangle from the indefinite integral Integral_{x} T(n,x), n>=0, in lowest terms).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive Chebyshev row numerator equals Browne's literal floor product and its radical sign.",
        H("Browne's Chebyshev numerator and floor product"),
        Blocks(
            Paragraph(Text("The source is OEIS A164660, revision 19, FORMULA; it has no page numbers. "
                + "Natural indices include zero, while the asserted equalities require a positive index. "
                + "The Chebyshev polynomials and the natural radical are the Mathlib objects. "
                + "Nat.div denotes natural integer division. The floors have values in the integers.")),
            Node("rowSum", "The rational row sum", RowSum(),
                SourceRow + " A164658, revision 21, FORMULA: a(n,m) = numerator(b(n,m)), with int(T(n,x))= sum(b(n,m)*x^m,m=1..n+1), n>=0, where T(n,x) are Chebyshevs polynomials of the first kind. "
                + "A164659 gives the denominators of the same coefficients. The primitive has zero constant coefficient. "
                + "The row is summed over Finset.Icc 1 (m+1), with both endpoints included; its summand is "
                + "the coefficient of degree j-1 in T(m,x), divided by j. Natural subtraction is used in j-1; "
                + "the displayed division is rational.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The reduced numerator", Numerator(),
                SourceRow + " The operation Rat.num is the reduced signed numerator with positive denominator.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("floorProduct", "The literal floor product", FloorProduct(),
                SourceFormula + " The product is in the integers; exponentiation, subtraction and division "
                + "inside each floor are rational operations. Finset.Icc includes one and n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Browne's complete assertion", Disp(Equal(F.Id("claim"), ClaimBody())),
                SourceFormula + " The natural n satisfies 0<n. A003557(n) is n divided by its radical, "
                + "with radical(1)=1. Both equalities are asserted, including n=1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The all-index identity", Disp(ClaimBody()),
                "The floor difference is the indicator that n divides k to the power n. This is equivalent "
                + "to the radical of n dividing k, so the product is minus one raised to the number n/radical(n) "
                + "of positive multiples. That number is even exactly when four divides n. "
                + "The polynomial T(n+2)/(2(n+2))-T(n)/(2n) has derivative T(n+1); its values at zero "
                + "and one evaluate the rational row sum. Its reduced numerator is one when four divides n "
                + "and minus one otherwise, giving the same sign for every positive n.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("b164660-chebfloor"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("b164660-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula RowSum()
    {
        var m = F.Id("m");
        var j = F.Id("j");
        var range = Apply(Qualified("Finset", "Icc"), D(1), Add(m, D(1)));
        var polynomial = Apply(Qualified("Polynomial", "Chebyshev", "T"),
            Rationals(), Cast(m, Integers()));
        var coefficient = Apply(Qualified("Polynomial", "coeff"), polynomial, Sub(j, D(1)));
        var sum = Seq(Sum, Underscore, Grp(j, Sp, InMacro, Sp, range), Sp,
            new Formula.Fraction(coefficient, Cast(j, Rationals())));
        return Disp(All("m", Equal(Call("rowSum", m), sum)));
    }

    private static Formula Numerator()
    {
        var m = F.Id("m");
        return Disp(All("m", Equal(Call("a", m),
            Apply(Qualified("Rat", "num"), Call("rowSum", m)))));
    }

    private static Formula FloorProduct()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var power = new Formula.Power(Cast(k, Rationals()), n);
        var first = new Formula.Floor(new Formula.Fraction(power, Cast(n, Rationals())));
        var second = new Formula.Floor(new Formula.Fraction(Sub(power, D(1)), Cast(n, Rationals())));
        var factor = Sub(D(1), Mul(D(2), Parenthesized(Sub(first, second))));
        var range = Apply(Qualified("Finset", "Icc"), D(1), n);
        var product = Seq(Prod, Underscore, Grp(k, Sp, InMacro, Sp, range), Sp, Parenthesized(factor));
        return Disp(All("n", Equal(Call("floorProduct", n), product)));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var product = Call("floorProduct", n);
        var quotient = Apply(Qualified("Nat", "div"), n,
            Apply(Qualified("UniqueFactorizationMonoid", "radical"), n));
        var sign = new Formula.Power(Parenthesized(Cast(Seq(Minus, D(1)), Integers())), quotient);
        return All("n", new Formula.Logic(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n),
            FormulaLogicOperator.Implies,
            new Formula.Logic(
                Parenthesized(Equal(Call("a", Add(n, D(1))), product)),
                FormulaLogicOperator.And, Parenthesized(Equal(product, sign)))));
    }

    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Naturals(), body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(params string[] names)
    {
        Formula result = F.Id(names[0]);
        foreach (var name in names[1..])
            result = Seq(result, Dot, F.Id(name));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
