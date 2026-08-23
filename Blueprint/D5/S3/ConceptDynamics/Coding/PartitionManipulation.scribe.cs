using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class PartitionManipulationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homogeneous message fibers admit a correct default rule and exclude partition "
            + "manipulation.",
        H("Partition Manipulation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("homogeneous-message-fibers-exclude-partition-manipulation"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Coding/PartitionManipulation."
                        + "manipulation_needs_heterogeneous_fiber"),
                H("Homogeneous message fibers exclude partition manipulation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose two states with the same message always have the same target "
                            + "value. Nonemptiness supplies an anchor target value, allowing the "
                            + "target on realized messages to extend to a total default rule on "
                            + "the whole message space.")),
                    Paragraph(Text(
                        "The resulting default agrees with the target at every actual state. "
                            + "Partition manipulation requires the default at the true message "
                            + "to be wrong, so this pointwise agreement rules it out everywhere."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula messageCarrier = F.Id("M");
        Formula targetCarrier = F.Id("Tval");
        Formula message = F.Id("message");
        Formula target = F.Id("target");
        Formula left = F.Id("a");
        Formula right = F.Id("b");
        Formula actual = F.Id("actual");
        Formula delta = F.Id("delta");

        Formula homogeneous = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("a", state), Bound("b", state)],
            new Formula.Logic(
                Equal(Apply(message, left), Apply(message, right)),
                FormulaLogicOperator.Implies,
                Equal(Apply(target, left), Apply(target, right))));
        Formula correct = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("actual"),
            state,
            Equal(
                Apply(delta, Apply(message, actual)),
                Apply(target, actual)));
        Formula noManipulation = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("actual"),
            state,
            new Formula.Not(Call(
                "PartitionManipulation",
                message,
                target,
                delta,
                actual)));
        Formula conclusion = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("delta"),
            Arrow(messageCarrier, targetCarrier),
            new Formula.Logic(correct, FormulaLogicOperator.And, noManipulation));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("M", F.Id("Type")),
                Bound("Tval", F.Id("Type")),
            ],
            new Formula.Logic(
                Call("Nonempty", state),
                FormulaLogicOperator.Implies,
                new Formula.BindMany(
                    FormulaQuantifier.ForAll,
                    [
                        Bound("message", Arrow(state, messageCarrier)),
                        Bound("target", Arrow(state, targetCarrier)),
                    ],
                    new Formula.Logic(
                        homogeneous,
                        FormulaLogicOperator.Implies,
                        conclusion)))));
    }
}
