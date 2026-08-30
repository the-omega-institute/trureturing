using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenLorentzUpdateDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenLorentzUpdate.golden_lorentz_update";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Fibonacci update negates the golden Lorentz form, while two updates preserve it.",
        H("Golden Lorentz Update"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-lorentz-update"),
            DeclarationHandle.Create(Declaration),
            H("One update exchanges sectors and two preserve the form"),
            StatementSource.FromAuthor(UpdateFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The quadratic form is constructed on the real two-dimensional carrier "
                        + "as Q_phi(x,y)=x^2-xy-y^2. The update is the repository's canonical "
                        + "real Fibonacci matrix with rows (1,1) and (1,0).")),
                Paragraph(Text(
                    "Direct expansion gives the one-step negation identity. Applying that "
                        + "identity twice cancels the two signs and proves exact preservation "
                        + "under the squared update.")),
                Paragraph(Text(
                    "The last two public clauses spell out the sector consequence: positive "
                        + "values become negative and negative values become positive after "
                        + "one update."))),
            DescribeRole.Theorem))));

    private static Formula UpdateFormula()
    {
        Formula real = Call("Real");
        Formula vector = Call("Vector", real, D(2));
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula v = F.Id("v");
        Formula qPhi = new Formula.Subscript(
            F.Id("Q"),
            new Formula.LatexMacro(FormulaLatexMacro.Phi));
        Formula fibonacci = F.Id("F");
        Formula qDefinition = Subtract(
            Subtract(new Formula.Power(x, D(2)), Multiply(x, y)),
            new Formula.Power(y, D(2)));
        Formula fibonacciDefinition = Call("matrix2", D(1), D(1), D(1), D(0));
        Formula qAtV = Apply(qPhi, v);
        Formula oneStep = Call("mulVec", fibonacci, v);
        Formula twoStep = Call(
            "mulVec", new Formula.Power(fibonacci, D(2)), v);
        Formula qAtOneStep = Apply(qPhi, oneStep);
        Formula qAtTwoStep = Apply(qPhi, twoStep);

        Formula antiIsometry = ForAll(
            "v", vector, Equal(qAtOneStep, Neg(qAtV)));
        Formula twoStepIsometry = ForAll(
            "v", vector, Equal(qAtTwoStep, qAtV));
        Formula positiveToNegative = ForAll(
            "v",
            vector,
            Implies(Less(D(0), qAtV), Less(qAtOneStep, D(0))));
        Formula negativeToPositive = ForAll(
            "v",
            vector,
            Implies(Less(qAtV, D(0)), Less(D(0), qAtOneStep)));
        Formula clauses = All(
            antiIsometry,
            twoStepIsometry,
            positiveToNegative,
            negativeToPositive);
        Formula definitions = Seq(
            F.Id("let"), Sp, qPhi, Open, x, Comma, Sp, y, Close,
            Sp, Eq, Sp, qDefinition, Semi, Sp,
            F.Id("let"), Sp, fibonacci, Sp, Eq, Sp, fibonacciDefinition,
            Semi, Sp, clauses);

        return Disp(definitions);
    }

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound(name, domain)],
            body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Neg(Formula value) => Seq(Minus, value);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate(And);
}
