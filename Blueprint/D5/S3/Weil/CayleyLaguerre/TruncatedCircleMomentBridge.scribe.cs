using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class TruncatedCircleMomentBridgeDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/CayleyLaguerre/TruncatedCircleMomentBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive semidefinite Hermitian truncated Toeplitz moment vector "
            + "has a finite atomic representing measure on the complex unit circle.",
        H("Truncated Circle Moment Bridge"),
        Blocks(Describe.Lean(
            DescribeId.Create("truncated-circle-moment-bridge"),
            DeclarationHandle.Create(Handle + "truncated_circle_moment_of_posSemidef"),
            H("Truncated positive Toeplitz moments have a circle representation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A Gram factorization realizes the truncated Toeplitz matrix as "
                        + "inner products of a finite vector orbit. The one-step shift "
                        + "descends through the Gram kernel and completes to a unitary "
                        + "operator.")),
                Paragraph(Text(
                    "The commuting self-adjoint real and imaginary parts admit a "
                        + "joint orthogonal eigenspace decomposition. Their joint "
                        + "spectral points lie on the complex unit circle and the "
                        + "squared orbit coefficients form the required finite atomic "
                        + "measure."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula depth = F.Id("N");
        Formula moment = F.Id("r");
        Formula exponent = F.Id("ell");
        Formula row = F.Id("j");
        Formula column = F.Id("k");
        Formula circlePoint = F.Id("z");
        Formula measure = F.Id("sigma");
        Formula circle = Call("Circle");
        Formula finiteMeasure = Call("FiniteMeasure", circle);
        Formula finDepth = Call("Fin", Add(depth, D(1)));

        Formula MomentAt(Formula index) => Apply(moment, index);
        Formula hermitian = ForAll(
            [Bound("ell", integer)],
            Equal(
                MomentAt(Call("neg", exponent)),
                Call("star", MomentAt(exponent))));
        Formula toeplitz = Call(
            "Matrix",
            Seq(
                Open,
                row,
                Comma,
                column,
                InMacro,
                finDepth,
                Sp,
                Mapsto,
                Sp,
                MomentAt(Sub(Call("toInt", row), Call("toInt", column))),
                Close));
        Formula positive = Call("PosSemidef", toeplitz);
        Formula represented = Exists(
            [Bound("sigma", finiteMeasure)],
            ForAll(
                [Bound("ell", integer)],
                Implies(
                    LessEqual(Call("natAbs", exponent), depth),
                    Equal(
                        Call(
                            "integral",
                            circlePoint,
                            circle,
                            Call("zpow", circlePoint, Call("neg", exponent)),
                            measure),
                        MomentAt(exponent)))));

        return Disp(ForAll(
            [
                Bound("N", natural),
                Bound("r", Arrow(integer, complex)),
            ],
            Implies(All(hermitian, positive), represented)));
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
