using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenBusemannCoordinateDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenBusemannCoordinate."
            + "golden_busemann_coordinate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden null coefficients carry a nontrivial Busemann rapidity coordinate.",
        H("Golden Busemann Coordinate"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-busemann-coordinate"),
            DeclarationHandle.Create(Declaration),
            H("The golden null basis exposes Busemann rapidity"),
            StatementSource.FromAuthor(CoordinateFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The real Lorentz form uses the existing sign convention "
                        + "Q_phi(x,y)=x^2-xy-y^2. The golden ratio and its negative "
                        + "conjugate give two null vectors, and direct polarization "
                        + "reduces the form of a v_plus+b v_minus to -5ab.")),
                Paragraph(Text(
                    "On the branch a>0 and b<0, the ratio a/(-b) is positive. At "
                        + "unit Lorentz level the coefficient product is "
                        + "a(-b)=1/5, so the half-log definition agrees exactly with "
                        + "log(a sqrt(5)). Differences of this coordinate satisfy the "
                        + "Busemann cocycle law by telescoping.")),
                Paragraph(Text(
                    "Reciprocal golden-square scaling preserves the branch and adds "
                        + "2 log(phi) to rapidity. The points with coefficients "
                        + "(1/sqrt(5),-1/sqrt(5)) and "
                        + "(2/sqrt(5),-1/(2sqrt(5))) both have Lorentz value one, "
                        + "but their rapidities are zero and log(2)."))),
            DescribeRole.Theorem))));

    private static Formula CoordinateFormula()
    {
        Formula real = Call("Real");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula d = F.Id("d");
        Formula e = F.Id("e");
        Formula f = F.Id("f");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula phi = new Formula.LatexMacro(FormulaLatexMacro.Phi);
        Formula phiPrime = F.Id("phiPrime");
        Formula sqrtFive = Call("sqrt", D(5));
        Formula q = new Formula.Subscript(
            F.Id("Q"), new Formula.LatexMacro(FormulaLatexMacro.Phi));
        Formula eta = F.Id("eta");
        Formula beta = new Formula.Subscript(F.Id("beta"), D(1));

        Formula stateAB = State(a, b);
        Formula stateCD = State(c, d);
        Formula stateEF = State(e, f);
        Formula branchAB = And(Less(D(0), a), Less(b, D(0)));
        Formula qDefinition = Subtract(
            Subtract(Pow(x, D(2)), Multiply(x, y)),
            Pow(y, D(2)));
        Formula etaDefinition = Multiply(
            new Formula.Fraction(D(1), D(2)),
            Call("log", new Formula.Fraction(a, Neg(b))));

        Formula nullity = And(
            Equal(Apply(q, phi, D(1)), D(0)),
            Equal(Apply(q, phiPrime, D(1)), D(0)));
        Formula expansion = ForAll(
            ["a", "b"],
            real,
            Equal(Apply(q, stateAB), Neg(Multiply(D(5), Multiply(a, b)))));
        Formula positiveArgument = ForAll(
            ["a", "b"],
            real,
            Implies(branchAB, Less(D(0), new Formula.Fraction(a, Neg(b)))));
        Formula unitClosedForm = ForAll(
            ["a", "b"],
            real,
            Implies(
                And(branchAB, Equal(Apply(q, stateAB), D(1))),
                Equal(
                    Apply(eta, a, b),
                    Call("log", Multiply(a, sqrtFive)))));
        Formula cocycle = ForAll(
            ["a", "b", "c", "d", "e", "f"],
            real,
            Equal(
                Add(
                    Apply(beta, a, b, c, d),
                    Apply(beta, c, d, e, f)),
                Apply(beta, a, b, e, f)));
        Formula update = ForAll(
            ["a", "b"],
            real,
            Implies(
                branchAB,
                Equal(
                    Apply(
                        eta,
                        Multiply(Pow(phi, D(2)), a),
                        Multiply(Pow(phi, Neg(D(2))), b)),
                    Add(
                        Apply(eta, a, b),
                        Multiply(D(2), Call("log", phi))))));

        Formula baseA = new Formula.Fraction(D(1), sqrtFive);
        Formula baseB = Neg(baseA);
        Formula movedA = new Formula.Fraction(D(2), sqrtFive);
        Formula movedB = Neg(new Formula.Fraction(D(1), Multiply(D(2), sqrtFive)));
        Formula witnesses = All(
            Equal(Apply(q, State(baseA, baseB)), D(1)),
            Equal(Apply(eta, baseA, baseB), D(0)),
            Equal(Apply(q, State(movedA, movedB)), D(1)),
            Equal(Apply(eta, movedA, movedB), Call("log", D(2))),
            NotEqual(Apply(eta, baseA, baseB), Apply(eta, movedA, movedB)));
        Formula clauses = All(
            nullity,
            expansion,
            positiveArgument,
            unitClosedForm,
            cocycle,
            update,
            witnesses);

        return Disp(Seq(
            F.Id("let"), Sp, q, Open, x, Comma, Sp, y, Close,
            Sp, Eq, Sp, qDefinition, Semi, Sp,
            F.Id("let"), Sp, F.Id("v"), Open, a, Comma, Sp, b, Close,
            Sp, Eq, Sp, stateAB, Semi, Sp,
            F.Id("let"), Sp, eta, Open, a, Comma, Sp, b, Close,
            Sp, Eq, Sp, etaDefinition, Semi, Sp,
            F.Id("let"), Sp, beta, Open, a, Comma, Sp, b, Comma, Sp,
            c, Comma, Sp, d, Close, Sp, Eq, Sp,
            Subtract(Apply(eta, c, d), Apply(eta, a, b)), Semi, Sp,
            clauses));

        Formula State(Formula left, Formula right) =>
            Call(
                "pair",
                Add(Multiply(left, phi), Multiply(right, phiPrime)),
                Add(left, right));
    }

    private static Formula ForAll(
        string[] names,
        Formula domain,
        Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. names.Select(name => Bound(name, domain))],
            body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Neg(Formula value) => Seq(Minus, value);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Not(Equal(left, right));

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate(And);
}
