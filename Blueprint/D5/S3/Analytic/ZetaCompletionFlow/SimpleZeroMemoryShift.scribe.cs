using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaCompletionFlow;

internal sealed class SimpleZeroMemoryShiftDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroMemoryShift.simple_zero_memory_shift";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A simple zero has a locally unique analytic branch under a quadratic closed-loop perturbation.",
        H("Simple-Zero Memory Shift"),
        Blocks(Describe.Lean(
            DescribeId.Create("simple-zero-memory-shift"),
            DeclarationHandle.Create(Declaration),
            H("A quadratic memory term displaces a simple zero"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source formula does not state the equation that defines the displaced "
                        + "zero. The positive first-order sign fixes that equation as "
                        + "F(z) minus kappa times A(z) squared equals zero; the formal statement "
                        + "makes this correction explicit.")),
                Paragraph(Text(
                    "For analytic F and A and a simple zero rho of F, the complex implicit "
                        + "function theorem constructs a branch through rho. Near the base pair, "
                        + "the displayed equation holds exactly when z is the branch value, so "
                        + "the continuation is locally unique.")),
                Paragraph(Text(
                    "Differentiating the equation gives the coefficient A(rho) squared divided "
                        + "by the derivative of F at rho. Analytic Taylor factorization supplies "
                        + "a genuine quadratic big-O remainder. The complex parameter statement "
                        + "is stronger than the real small-parameter formulation and does not "
                        + "identify the branch with zeros of the Riemann zeta function."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula functionType = Seq(complex, Sp, To, Sp, complex);
        Formula function = F.Id("F");
        Formula memory = F.Id("A");
        Formula rho = F.Id("rho");
        Formula branch = F.Id("branch");
        Formula kappa = F.Id("kappa");
        Formula pair = F.Id("p");
        Formula pairKappa = Call("fst", pair);
        Formula pairZero = Call("snd", pair);
        Formula basePair = Call("pair", D(0), rho);

        Formula equation(Formula parameter, Formula zero) => EqualTo(
            Seq(
                Apply(function, zero), Sp, Minus, Sp,
                parameter, Sp, Times, Sp, Power(Apply(memory, zero), D(2))),
            D(0));

        Formula premises = And(
            Call("AnalyticAt", complex, function, rho),
            And(
                Call("AnalyticAt", complex, memory, rho),
                And(
                    EqualTo(Apply(function, rho), D(0)),
                    NotEqualTo(Call("deriv", function, rho), D(0)))));
        Formula branchBase = EqualTo(Apply(branch, D(0)), rho);
        Formula branchEquation = Call(
            "EventuallyAt",
            kappa,
            Call("nhds", D(0)),
            equation(kappa, Apply(branch, kappa)));
        Formula branchUnique = Call(
            "EventuallyAt",
            pair,
            Call("nhds", basePair),
            Iff(
                equation(pairKappa, pairZero),
                EqualTo(Apply(branch, pairKappa), pairZero)));
        Formula linearCoefficient = Seq(
            Power(Apply(memory, rho), D(2)), Sp, Slash, Sp,
            Call("deriv", function, rho));
        Formula remainder = Seq(
            Apply(branch, kappa), Sp, Minus, Sp, rho, Sp, Minus, Sp,
            kappa, Sp, Times, Sp, linearCoefficient);
        Formula quadraticRemainder = Call(
            "IsBigOAtZero",
            Lambda(kappa, remainder),
            Lambda(kappa, Power(kappa, D(2))));
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("branch", functionType)],
            And(branchBase, And(branchEquation, And(branchUnique, quadraticRemainder))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("F", functionType),
                Bound("A", functionType),
                Bound("rho", complex),
            ],
            Implies(premises, conclusion)));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Not(EqualTo(left, right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));
}
