using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GramianBehaviorQuotientMetricDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The observability Gramian metrizes the complete future-behavior quotient.",
        H("Gramian Behavior-Quotient Metric"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gramian-behavior-quotient-metric"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Linear/GramianBehaviorQuotientMetric."
                        + "gramian_behavior_quotient_metric"),
                H("Gramian zero distance is complete behavioral equivalence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The evolution, readout, and discounted observability Gramian are the "
                            + "canonical imported linear-observer primitives.")),
                    Paragraph(Text(
                        "For any two states, equality of every future readout is equivalent to "
                            + "zero real Gramian quadratic form on their difference. Thus the "
                            + "Gramian supplies a quadratic metric on the behavioral quotient."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Arrow(Formula scalar, Formula domain, Formula codomain) =>
        Call("LinearMap", scalar, domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula beta = F.Id("beta");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula n = F.Id("n");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula gramian = Call("discountedObservabilityGramian", evolution, readout, beta);
        Formula difference = Seq(x, Sp, Minus, Sp, y);
        Formula Iterate(Formula value) =>
            new Formula.Apply(
                readout,
                [new Formula.Apply(
                    Seq(evolution, Caret, Grp(n)),
                    [value])]);
        Formula futureAgreement = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            F.Id("Nat"),
            new Formula.Relation(
                Iterate(x), FormulaRelationOperator.Equal, Iterate(y)));
        Formula quadratic = Seq(
            Call("re", Call("inner", scalar, difference,
                new Formula.Apply(gramian, [difference]))),
            Sp, Eq, Sp, D(0));
        Formula assumptions = Seq(
            Call("RCLike", scalar), Sp, Land, Sp,
            Call("NormedAddCommGroup", state), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, state), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, state), Sp, Land, Sp,
            Call("NormedAddCommGroup", output), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, output), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, output), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, beta, Sp, Lt, Sp, D(1), Sp, Land, Sp,
            Sqrt, Grp(beta), Sp, new Formula.Norm(evolution), Sp, Lt, Sp, D(1));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("K"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("V"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("Y"), F.Id("Type")),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("T"), Arrow(scalar, state, state)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("C"), Arrow(scalar, state, output)),
                new Formula.BoundVariable(FormulaIdentifier.Create("beta"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), state),
                new Formula.BoundVariable(FormulaIdentifier.Create("y"), state),
            ],
            new Formula.Logic(
                assumptions,
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    futureAgreement, FormulaLogicOperator.Iff, quadratic))));
    }
}
