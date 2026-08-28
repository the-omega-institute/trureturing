using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TargetRisk;

internal sealed class JointResourceSafetyCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/TargetRisk/JointResourceSafetyCriterion."
            + "jointly_attainable_caps_characterize_resource_safety";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jointly attainable local extraction caps guarantee resource safety exactly when "
            + "their total fits the stock-plus-recovery budget.",
        H("Joint Resource Safety Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("joint-resource-safety-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Jointly attainable caps characterize resource safety"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A feasible extraction is constructed from a finite family of agents, "
                        + "a current stock, its recovery rule, and local extraction caps. "
                        + "The cap vector itself is explicitly required to be feasible.")),
                Paragraph(Text(
                    "If every feasible extraction is nonnegative and bounded pointwise by "
                        + "the caps, then all feasible next-period stocks meet the minimum "
                        + "exactly when the sum of the caps fits the recoverable budget.")),
                Paragraph(Text(
                    "The same two-agent cap and extraction vectors witness the contrast: "
                        + "each three-quarter extraction alone leaves nonnegative stock, "
                        + "while their joint extraction drives the next stock below zero."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula proposition = F.Id("Prop");
        Formula real = F.Id("Real");
        Formula agent = F.Id("Agent");
        Formula stock = F.Id("s");
        Formula minimumStock = F.Id("smin");
        Formula recovery = F.Id("g");
        Formula cap = F.Id("c");
        Formula extraction = F.Id("a");
        Formula index = F.Id("i");
        Formula agentVector = Arrow(agent, real);
        Formula feasible = F.Id("Feasible");
        Formula feasibleType = Arrow(
            F.Seq(F.Open, agentVector, F.Close), proposition);

        Formula localBounds = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("a"),
            agentVector,
            Implies(
                Apply(feasible, extraction),
                new Formula.Bind(
                    FormulaQuantifier.ForAll,
                    FormulaIdentifier.Create("i"),
                    agent,
                    And(
                        Leq(new Formula.Number(0), Apply(extraction, index)),
                        Leq(Apply(extraction, index), Apply(cap, index))))));

        Formula safetyGuarantee = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("a"),
            agentVector,
            Implies(
                Apply(feasible, extraction),
                Leq(minimumStock, NextStock(stock, recovery, Sum(extraction)))));

        Formula capCriterion = Leq(
            Sum(cap),
            Subtract(Add(stock, Apply(recovery, stock)), minimumStock));

        Formula criterion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Agent", type),
                Bound("s", real),
                Bound("smin", real),
                Bound("g", Arrow(real, real)),
                Bound("c", agentVector),
                Bound("Feasible", feasibleType),
            ],
            Implies(
                And(
                    Call("Fintype", agent),
                    Apply(feasible, cap),
                    localBounds),
                Iff(safetyGuarantee, capCriterion)));

        Formula finTwo = Call("Fin", new Formula.Number(2));
        Formula twoVector = Arrow(finTwo, real);
        Formula witnessIndex = F.Id("j");
        Formula threeQuarters = new Formula.Fraction(
            new Formula.Number(3), new Formula.Number(4));
        Formula witnessBounds = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("j"),
            finTwo,
            And(
                Leq(new Formula.Number(0), Apply(extraction, witnessIndex)),
                Leq(Apply(extraction, witnessIndex), Apply(cap, witnessIndex))));
        Formula individualSafety = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("j"),
            finTwo,
            Leq(
                minimumStock,
                NextStock(stock, recovery, Apply(extraction, witnessIndex))));

        Formula countermodel = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("s", real),
                Bound("smin", real),
                Bound("g", Arrow(real, real)),
                Bound("c", twoVector),
                Bound("a", twoVector),
            ],
            And(
                Equal(stock, new Formula.Number(1)),
                Equal(minimumStock, new Formula.Number(0)),
                Equal(recovery, Call("const", new Formula.Number(0))),
                Equal(cap, Call("const", threeQuarters)),
                Equal(extraction, cap),
                witnessBounds,
                individualSafety,
                Lt(
                    NextStock(stock, recovery, Sum(extraction)),
                    minimumStock)));

        return F.Disp(And(criterion, countermodel));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Sum(Formula vector) => Call("sum", vector);

    private static Formula NextStock(
        Formula stock, Formula recovery, Formula totalExtraction) =>
        Subtract(Add(stock, Apply(recovery, stock)), totalExtraction);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var index = 1; index < clauses.Length; index++)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, clauses[index]);
        }

        return result;
    }
}
