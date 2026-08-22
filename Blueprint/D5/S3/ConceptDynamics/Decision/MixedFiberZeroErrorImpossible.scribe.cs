using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class MixedFiberZeroErrorImpossibleDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Decision/MixedFiberZeroErrorImpossible.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite labels in one evidence fiber force a sharp one-error lower bound for "
            + "every deterministic evidence-based decision rule.",
        H("Mixed-Fiber Zero Error Is Impossible"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixed-fiber-zero-error-is-impossible"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "mixed_fiber_zero_error_impossible"),
                H("A mixed evidence fiber rules out zero error"),
                StatementSource.FromAuthor(ZeroErrorImpossibleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The evidence map sends x and y to the same observation, while their "
                            + "Boolean labels are true and false. A deterministic rule therefore "
                            + "returns the same value at both states and cannot agree with both "
                            + "opposite labels; at least one state must be misclassified.")),
                    Paragraph(Text(
                        "Because the conclusion ranges over every total evidence-based rule, "
                            + "the obstruction belongs to the evidence interface itself rather "
                            + "than to a particular choice of decision procedure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixed-fiber-one-error-bound-is-tight"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "mixed_fiber_error_bound_is_tight"),
                H("The one-error lower bound is sharp"),
                StatementSource.FromAuthor(TightErrorBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Counting errors on the ordered pair (x, y), the mixed-fiber theorem gives "
                        + "a lower bound of one for every deterministic rule. The constant-true "
                        + "rule is correct on the positively labelled state and wrong on the "
                        + "negatively labelled state, so it attains exactly one error. Thus the "
                        + "universal lower bound cannot be improved."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula SharedFiberHypotheses(
        Formula evidence,
        Formula label,
        Formula x,
        Formula y) =>
        And(
            Equal(Apply(evidence, x), Apply(evidence, y)),
            And(
                Equal(Apply(label, x), F.Id("true")),
                Equal(Apply(label, y), F.Id("false"))));

    private static Formula PairErrorCount(
        Formula evidence,
        Formula label,
        Formula decide,
        Formula x,
        Formula y) =>
        Call("pairErrorCount", evidence, label, decide, x, y);

    private static Formula ZeroErrorImpossibleFormula()
    {
        Formula stateType = F.Id("X");
        Formula evidenceType = F.Id("B");
        Formula boolean = F.Id("Bool");
        Formula evidence = F.Id("e");
        Formula label = F.Id("l");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula decide = F.Id("d");
        Formula someError = Or(
            NotEqual(Apply(decide, Apply(evidence, x)), Apply(label, x)),
            NotEqual(Apply(decide, Apply(evidence, y)), Apply(label, y)));
        Formula everyRuleHasError = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            Arrow(evidenceType, boolean),
            someError);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. ContextVariables(stateType, evidenceType, boolean)],
            ImpliesFormula(
                SharedFiberHypotheses(evidence, label, x, y),
                everyRuleHasError)));
    }

    private static Formula TightErrorBoundFormula()
    {
        Formula stateType = F.Id("X");
        Formula evidenceType = F.Id("B");
        Formula boolean = F.Id("Bool");
        Formula evidence = F.Id("e");
        Formula label = F.Id("l");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula decide = F.Id("d");
        Formula ruleType = Arrow(evidenceType, boolean);
        Formula atLeastOne = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            ruleType,
            LessThanOrEqual(
                Num(1),
                PairErrorCount(evidence, label, decide, x, y)));
        Formula exactlyOne = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("d"),
            ruleType,
            Equal(
                PairErrorCount(evidence, label, decide, x, y),
                Num(1)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. ContextVariables(stateType, evidenceType, boolean)],
            ImpliesFormula(
                SharedFiberHypotheses(evidence, label, x, y),
                And(atLeastOne, exactlyOne))));
    }

    private static Formula.BoundVariable[] ContextVariables(
        Formula stateType,
        Formula evidenceType,
        Formula boolean) =>
        [
            Bound("X", F.Id("Type")),
            Bound("B", F.Id("Type")),
            Bound("e", Arrow(stateType, evidenceType)),
            Bound("l", Arrow(stateType, boolean)),
            Bound("x", stateType),
            Bound("y", stateType),
        ];
}
