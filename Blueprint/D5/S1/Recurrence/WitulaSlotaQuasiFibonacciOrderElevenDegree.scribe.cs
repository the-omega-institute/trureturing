using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class WitulaSlotaQuasiFibonacciOrderElevenDegreeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/witulaslota2007order11");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every order-eleven quasi-Fibonacci polynomial in the five families has full degree from index five onward.",
        H("Degrees of the Order-Eleven Quasi-Fibonacci Polynomials"),
        Blocks(
            Paragraph(Text(
                "The coefficient ring is Z and X represents the paper's variable delta. "
                    + "The five-fold product is right-associated. Thus fst selects its first "
                    + "component and snd moves to the remaining product. Polynomial degree "
                    + "takes values in the naturals with a bottom element; the zero polynomial "
                    + "has degree bottom. A natural number on the right of a degree equality "
                    + "is embedded in that ordered type.")),
            Node(
                "quasi",
                "The order-eleven recurrence system",
                QuasiFormula(),
                "System (3.12) on printed page 5 gives these five recurrence lines and "
                    + "the initial values A(0)=1 and B(0)=C(0)=D(0)=E(0)=0. The tuple "
                    + "quasi(n) contains the five polynomials in that order.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("A", "The polynomial A(n)", ProjectionFormula("A", 0, true),
                "A(n) is the first component of quasi(n).", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("B", "The polynomial B(n)", ProjectionFormula("B", 1, true),
                "B(n) is the first component after one move into the remaining product.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("C", "The polynomial C(n)", ProjectionFormula("C", 2, true),
                "C(n) is the first component after two moves into the remaining product.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("D", "The polynomial D(n)", ProjectionFormula("D", 3, true),
                "D(n) is the first component after three moves into the remaining product.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("E", "The polynomial E(n)", ProjectionFormula("E", 4, false),
                "E(n) is the final component of the right-associated product.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node(
                "claim",
                "The page-19 degree problem",
                ClaimFormula(),
                "The Problem on printed page 19 asks verbatim: \"Problem. Is it true that "
                    + "deg A_n(Δ) = deg B_n(Δ) = deg C_n(Δ) = deg D_n(Δ) = "
                    + "deg E_n(Δ) = n for every n = 5, 6, . . .?\" Here deg is "
                    + "Polynomial.degree, so each equality also asserts that the corresponding "
                    + "polynomial is nonzero.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "result",
                "All five degrees are full",
                ResultFormula(),
                "The answer is affirmative. Each recurrence step raises degree by at most one. "
                    + "For the coefficient of X^n, apply alternating signs to the five "
                    + "coordinates. At n=5 the resulting vector is (1,9,1,4,1). Its coordinates "
                    + "remain positive and its last coordinate remains smaller than the sum of "
                    + "the first and third: the next vector is (2b+e,a+c-e,b+d+e,c,d+e), and "
                    + "the new difference between that sum and the last coordinate is 3b+e. "
                    + "Consequently every degree-n coefficient is nonzero for n at least five, "
                    + "and the upper degree bounds are equalities.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "witula-slota-2007-quasi-fibonacci-order-eleven-degree"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string declaration,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("witula-slota-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula PolynomialRing() =>
        Seq(Integers(), OpenBracket, F.Id("X"), CloseBracket);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula ImpliesF(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula IffF(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Tuple(params Formula[] entries)
    {
        var items = new List<Formula>();
        for (var index = 0; index < entries.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(entries[index]);
        }
        return Parenthesized(Seq([.. items]));
    }

    private static Formula SequenceValue(string name, Formula n) => Call(name, n);

    private static Formula Next(Formula n) => Add(n, D(1));

    private static Formula QuasiFormula()
    {
        var n = F.Id("n");
        var x = F.Id("X");
        var a = SequenceValue("A", n);
        var b = SequenceValue("B", n);
        var c = SequenceValue("C", n);
        var d = SequenceValue("D", n);
        var e = SequenceValue("E", n);
        var next = Next(n);
        var ring = PolynomialRing();
        var type = Seq(F.Id("quasi"), Sp, Colon, Sp, Naturals(), Sp, To, Sp,
            Seq(ring, Sp, Times, Sp, Parenthesized(Seq(
                ring, Sp, Times, Sp, Parenthesized(Seq(
                    ring, Sp, Times, Sp, Parenthesized(Seq(
                        ring, Sp, Times, Sp, ring))))))));
        var initial = Equal(Call("quasi", D(0)), Tuple(D(1), D(0), D(0), D(0), D(0)));
        var aStep = Equal(SequenceValue("A", next),
            Subtract(Add(a, Multiply(Multiply(D(2), x), b)), Multiply(x, e)));
        var bStep = Equal(SequenceValue("B", next),
            Subtract(Add(Add(Multiply(x, a), b), Multiply(x, c)), Multiply(x, e)));
        var cStep = Equal(SequenceValue("C", next),
            Subtract(Add(Add(Multiply(x, b), c), Multiply(x, d)), Multiply(x, e)));
        var dStep = Equal(SequenceValue("D", next), Add(Multiply(x, c), d));
        var eStep = Equal(SequenceValue("E", next),
            Add(Multiply(x, d), Multiply(Parenthesized(Subtract(D(1), x)), e)));
        return Disp(new Formula.Aligned([
            type,
            initial,
            ForAllN(n, aStep),
            ForAllN(n, bStep),
            ForAllN(n, cStep),
            ForAllN(n, dStep),
            ForAllN(n, eStep),
        ]));
    }

    private static Formula ProjectionFormula(string name, int sndCount, bool finishWithFst)
    {
        var n = F.Id("n");
        Formula projection = Call("quasi", n);
        for (var index = 0; index < sndCount; index++)
        {
            projection = Call("snd", projection);
        }
        if (finishWithFst)
        {
            projection = Call("fst", projection);
        }
        return Disp(ForAllN(n, Equal(Call(name, n), projection)));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        Formula Degree(string name) => Call("deg", Call(name, n));
        var degrees = And(Equal(Degree("A"), n),
            And(Equal(Degree("B"), n),
                And(Equal(Degree("C"), n),
                    And(Equal(Degree("D"), n), Equal(Degree("E"), n)))));
        return ForAllN(n, ImpliesF(AtMost(D(5), n), degrees));
    }

    private static Formula ClaimFormula() =>
        Disp(IffF(F.Id("claim"), ClaimBody()));

    private static Formula ResultFormula() => Disp(ClaimBody());

    private static Formula ForAllN(Formula n, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals())],
            body);
}
