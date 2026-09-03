using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class FourierLaplaceClosedStripDecayDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/TestFunctions/FourierLaplaceClosedStripDecay."
            + "fourierLaplace_decay_closedStrip";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier-Laplace transforms of Weil test functions decay uniformly on closed strips.",
        H("Fourier-Laplace Closed-Strip Decay"),
        Blocks(Describe.Lean(
            DescribeId.Create("fourier-laplace-decay-closed-strip"),
            DeclarationHandle.Create(Declaration),
            H("Uniform quadratic decay on every closed strip"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary nonnegative strip width eta, compact support bounds "
                        + "the complex exponential by exp(eta times the absolute value of x). "
                        + "Two integrations by parts transfer two derivatives to the test "
                        + "function and give a quadratic denominator in the real direction.")),
                Paragraph(Text(
                    "The constant is the sum of the zeroth- and second-derivative strip "
                        + "majorants. The statement is uniform over the closed strip and "
                        + "does not assert a zero-sum or separator-limit conclusion."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula testFunction = F.Id("WeilTestFunction");
        Formula b = F.Id("b");
        Formula eta = F.Id("eta");
        Formula w = F.Id("w");
        Formula c = F.Id("C");

        Formula re = Seq(w, Dot, F.Id("re"));
        Formula im = Seq(w, Dot, F.Id("im"));
        Formula transform = Call("fourierLaplace", b, w);
        Formula denominator = Seq(
            D(1), Plus, new Formula.Power(re, D(2)));
        Formula bound = new Formula.Relation(
            new Formula.Norm(transform),
            FormulaRelationOperator.LessThanOrEqual,
            new Formula.Fraction(c, denominator));
        Formula stripHypothesis = new Formula.Relation(
            new Formula.Absolute(im),
            FormulaRelationOperator.LessThanOrEqual,
            eta);
        Formula pointwise = ForAll(
            [Bound("w", complex)],
            Implies(stripHypothesis, bound));
        Formula constantProperties = And(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, c),
            pointwise);
        Formula conclusion = Exists(
            [Bound("C", real)],
            constantProperties);
        Formula etaHypothesis = new Formula.Relation(
            D(0), FormulaRelationOperator.LessThanOrEqual, eta);

        return Disp(ForAll(
            [Bound("b", testFunction), Bound("eta", real)],
            Implies(etaHypothesis, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
