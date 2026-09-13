using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class JointPolynomialPairBinomialCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/schulte2017a208342");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's binomial sum gives every coefficient in the jointly generated polynomial pair.",
        H("The Joint Polynomial Pair of OEIS A208342"),
        Blocks(
            Paragraph(Text(
                "All indices and values are natural numbers. The operators natSub and natDiv "
                + "mean truncated subtraction and integer division. The function ite chooses "
                + "its second or third argument according to its first argument, and binomial "
                + "is the natural binomial coefficient.")),
            Node("coefficientPair", "The joint coefficient recursion", CoefficientPairFormula(),
                "At stage zero both coefficient functions equal one at degree zero and zero "
                + "elsewhere. The two step equations are the coefficient forms of "
                + "u(n,x)=u(n-1,x)+x*v(n-1,x) and "
                + "v(n,x)=x*u(n-1,x)+x*v(n-1,x).",
                DescribeRole.Definition),
            Node("u", "Coefficients of the first polynomial", UFormula(),
                "The stage shift makes u(1,x) the initial constant polynomial one.",
                DescribeRole.Definition),
            Node("v", "Coefficients of the companion polynomial", VFormula(),
                "The same stage shift makes v(1,x) the initial constant polynomial one.",
                DescribeRole.Definition),
            Node("T", "The A208342 triangle entry", TFormula(),
                "The entry T(n,k) is the coefficient of x^(k-1) in u(n,x).",
                DescribeRole.Definition),
            Node("schulte_a208342", "Schulte's binomial coefficient formula", TheoremFormula(),
                "Simultaneous induction gives closed forms for both coefficient functions. "
                + "The two recursion components use different Pascal summation transformations. "
                + "Vanishing binomial coefficients remove every term above "
                + "natDiv(k-1,2), leaving the displayed finite sum.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a208342-joint-polynomial-pair-binomial-coefficients"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a208342-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula CoefficientPairFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i");
        Formula initial = All(i, And(
            Equal(First(D(0), i), If(Equal(i, D(0)), D(1), D(0))),
            Equal(Second(D(0), i), If(Equal(i, D(0)), D(1), D(0)))));
        Formula previous = NatSub(i, D(1));
        Formula step = All(Seq(n, Comma, Sp, i), And(
            Equal(First(Add(n, D(1)), i),
                Add(First(n, i), If(Equal(i, D(0)), D(0), Second(n, previous)))),
            Equal(Second(Add(n, D(1)), i),
                If(Equal(i, D(0)), D(0), Add(First(n, previous), Second(n, previous))))));
        return Disp(new Formula.Aligned([Parenthesized(initial), Parenthesized(step)]));
    }

    private static Formula UFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i");
        return Disp(All(Seq(n, Comma, Sp, i),
            Equal(Call("u", n, i), First(NatSub(n, D(1)), i))));
    }

    private static Formula VFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i");
        return Disp(All(Seq(n, Comma, Sp, i),
            Equal(Call("v", n, i), Second(NatSub(n, D(1)), i))));
    }

    private static Formula TFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        return Disp(All(Seq(n, Comma, Sp, k),
            Equal(Call("T", n, k), Call("u", n, NatSub(k, D(1))))));
    }

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), j = F.Id("j");
        Formula upper = NatDiv(NatSub(k, D(1)), D(2));
        Formula summand = Mul(
            Call("binomial", NatSub(NatSub(k, D(1)), j), j),
            Call("binomial", Add(NatSub(n, k), j), j));
        Formula sum = Seq(
            new Formula.Power(
                Seq(new Formula.Subscript(Sum, Equal(j, D(0)))), upper),
            Sp, summand);
        Formula conclusion = Equal(Call("T", n, k), sum);
        Formula hypotheses = Implies(Less(D(0), k), Implies(LessEqual(k, n), conclusion));
        return Disp(All(Seq(n, Comma, Sp, k), hypotheses));
    }

    private static Formula First(Formula stage, Formula index) =>
        Call("first", Call("coefficientPair", stage), index);
    private static Formula Second(Formula stage, Formula index) =>
        Call("second", Call("coefficientPair", stage), index);
    private static Formula If(Formula condition, Formula whenTrue, Formula whenFalse) =>
        Call("ite", condition, whenTrue, whenFalse);
    private static Formula NatSub(Formula left, Formula right) => Call("natSub", left, right);
    private static Formula NatDiv(Formula left, Formula right) => Call("natDiv", left, right);
    private static Formula All(Formula variables, Formula body) => Seq(
        Forall, Sp, variables, Sp, InMacro, Sp, Naturals(), Comma, Sp, body);
    private static Formula Naturals() => F.Id("Nat");
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
