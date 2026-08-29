using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class ExactTruncatedHaarFloorDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/TestFunctions/ExactTruncatedHaarFloor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A represented Hermitian truncated circle moment vector has exact "
            + "normalized-Haar floor equal to its least Toeplitz eigenvalue.",
        H("Exact Truncated Haar Floor"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-truncated-haar-floor"),
            DeclarationHandle.Create(Handle + "exact_truncated_haar_floor"),
            H("Exact truncated Haar floor"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The Toeplitz matrix and feasible floor set are constructed "
                        + "directly from the supplied truncated moment data and "
                        + "normalized circle Haar measure.")),
                Paragraph(Text(
                    "The forward bound subtracts any dominated Haar component and "
                        + "uses positivity of the residual Toeplitz matrix. For the "
                        + "reverse bound, a local finite trigonometric-moment proof "
                        + "constructs a positive atomic circle measure from the "
                        + "positive semidefinite shifted Toeplitz matrix.")),
                Paragraph(Text(
                    "The positive zeroth moment bounds the feasible floors, so their "
                        + "supremum is well-defined and equals the least ordered "
                        + "Hermitian eigenvalue."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula nonnegativeReal = Call("NonnegativeReal");
        Formula circle = Call("Circle");
        Formula finiteMeasure = Call("FiniteMeasure", circle);
        Formula depth = F.Id("N");
        Formula moment = F.Id("m");
        Formula mass = F.Id("R");
        Formula exponent = F.Id("ell");
        Formula row = F.Id("j");
        Formula column = F.Id("k");
        Formula circlePoint = F.Id("z");
        Formula measure = F.Id("mu");
        Formula alpha = F.Id("alpha");
        Formula toeplitz = F.Id("T");
        Formula hermitianWitness = F.Id("hT");
        Formula feasible = F.Id("A");
        Formula floor = F.Id("alphaN");
        Formula finDepth = Call("Fin", Add(depth, D(1)));
        Formula matrixType = Call("Matrix", finDepth, finDepth, complex);

        Formula Lambda(Formula variable, Formula body) =>
            Seq(Open, variable, Sp, Mapsto, Sp, body, Close);
        Formula Let(Formula name, Formula value) =>
            Seq(Operatorname, Grp(F.Id("let")), Sp, name, Sp, Eq, Sp, value);
        Formula MomentAt(Formula index) => Apply(moment, index);
        Formula MonomialAt(Formula index) =>
            Call("zpow", circlePoint, Call("neg", index));
        Formula MomentIntegral(Formula source, Formula index) =>
            Call("integral", circlePoint, circle, MonomialAt(index), source);
        Formula MomentAgreement(Formula source) => ForAll(
            [Bound("ell", integer)],
            Implies(
                LessEqual(Call("natAbs", exponent), depth),
                Equal(MomentIntegral(source, exponent), MomentAt(exponent))));

        Formula hermitian = ForAll(
            [Bound("ell", integer)],
            Equal(
                MomentAt(Call("neg", exponent)),
                Call("star", MomentAt(exponent))));
        Formula zeroMoment = Equal(MomentAt(D(0)), Call("toComplex", mass));
        Formula positiveMass = Less(D(0), mass);
        Formula represented = Exists(
            [Bound("mu", finiteMeasure)],
            MomentAgreement(measure));

        Formula matrixDomain = Seq(row, Comma, column, InMacro, finDepth);
        Formula toeplitzDefinition = Let(
            toeplitz,
            Call(
                "Matrix",
                Lambda(
                    matrixDomain,
                    MomentAt(Sub(Call("toInt", row), Call("toInt", column))))));
        Formula hermitianDefinition = Seq(
            Let(
                hermitianWitness,
                Call("hermitianToeplitz", moment, hermitian)),
            Colon,
            Sp,
            Call("IsHermitian", toeplitz));

        Formula feasiblePredicate = Exists(
            [Bound("mu", finiteMeasure)],
            All(
                MomentAgreement(measure),
                LessEqual(
                    Call(
                        "toMeasure",
                        Call(
                            "smul",
                            alpha,
                            Call("normalizedCircleHaar"))),
                    Call("toMeasure", measure))));
        Formula feasibleDefinition = Let(
            feasible,
            new Formula.SetBuilder(feasiblePredicate, alpha, nonnegativeReal));
        Formula floorDefinition = Let(floor, Call("sSup", feasible));
        Formula conclusion = Equal(
            Call("toReal", floor),
            Call("lambdaMin", toeplitz, hermitianWitness));

        Formula premise = All(
            hermitian,
            zeroMoment,
            positiveMass,
            represented,
            toeplitzDefinition,
            hermitianDefinition,
            feasibleDefinition,
            floorDefinition);

        return Disp(ForAll(
            [
                Bound("N", natural),
                Bound("m", Arrow(integer, complex)),
                Bound("R", real),
            ],
            Implies(premise, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
