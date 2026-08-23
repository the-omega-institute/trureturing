using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Answering;

internal sealed class SafeAnswerCoverageMaximalityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Answering/SafeAnswerCoverageMaximality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical safe answer is zero-error and covers every zero-error answer on "
            + "an inhabited fiber, while an empty fiber supplies the necessary counterexample.",
        H("Safe Answer Coverage Maximality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-safe-answer-has-zero-error"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "canonical_safe_answer_zero_error"),
                H("The canonical safe answer has zero error"),
                StatementSource.FromAuthor(CanonicalZeroErrorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The canonical answerer responds at a concept value only when the admitted "
                        + "inputs in that fiber attain one unique target. Every admitted input "
                        + "contributes its own target to the fiber, so uniqueness forces the "
                        + "chosen answer to equal that target. Thus every answer it makes is "
                        + "correct."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "canonical-safe-answer-covers-zero-error-answers-on-inhabited-fibers"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "safe_answer_coverage_maximality"),
                H("The canonical safe answer covers every safe inhabited-fiber answer"),
                StatementSource.FromAuthor(CoverageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose a zero-error answerer returns y at b and some admitted input "
                            + "lies over b. Zero error identifies that input's target with y.")),
                    Paragraph(Text(
                        "Any two targets attained in the same fiber are witnessed by admitted "
                            + "inputs receiving the same answer y. Zero error therefore forces "
                            + "both targets to equal y, making the fiber the singleton {y}. The "
                            + "canonical answerer consequently returns y as well."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("an-empty-fiber-defeats-unconditional-coverage"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "empty_fiber_counterexample"),
                H("An empty fiber defeats unconditional coverage"),
                StatementSource.FromAuthor(EmptyFiberCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take one admitted input with concept value false and target false, and let "
                        + "the competing answerer return each Boolean observation itself. It has "
                        + "zero error on the only inhabited fiber. At true, however, the fiber "
                        + "is empty: the competing answerer returns true while the canonical "
                        + "answerer abstains. Hence the inhabitation premise in the maximality "
                        + "theorem cannot be removed."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ZeroError(
        Formula admission,
        Formula concept,
        Formula target,
        Formula answerer) =>
        Call("ZeroError", admission, concept, target, answerer);

    private static Formula Canonical(
        Formula admission,
        Formula concept,
        Formula target,
        Formula fiber) =>
        Call("canonicalSafeAnswer", admission, concept, target, fiber);

    private static Formula Some(Formula value) => Call("some", value);

    private static Formula FiberInhabited(
        Formula inputType,
        Formula admission,
        Formula concept,
        Formula fiber)
    {
        Formula input = F.Id("x");
        Formula body = And(
            Apply(admission, input),
            Equal(Apply(concept, input), fiber));

        return new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("x"),
            inputType,
            body);
    }

    private static Formula CanonicalZeroErrorFormula()
    {
        Formula inputType = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula admission = F.Id("A");
        Formula concept = F.Id("C");
        Formula target = F.Id("T");
        Formula canonical = Call("canonicalSafeAnswer", admission, concept, target);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                .. ContextVariables(
                    inputType,
                    conceptType,
                    targetType,
                    admission,
                    concept,
                    target),
            ],
            ZeroError(admission, concept, target, canonical)));
    }

    private static Formula CoverageFormula()
    {
        Formula inputType = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula admission = F.Id("A");
        Formula concept = F.Id("C");
        Formula target = F.Id("T");
        Formula answerer = F.Id("g");
        Formula fiber = F.Id("b");
        Formula value = F.Id("y");
        Formula hypotheses = And(
            ZeroError(admission, concept, target, answerer),
            And(
                FiberInhabited(inputType, admission, concept, fiber),
                Equal(Apply(answerer, fiber), Some(value))));
        Formula conclusion = Equal(
            Canonical(admission, concept, target, fiber),
            Some(value));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                .. ContextVariables(
                    inputType,
                    conceptType,
                    targetType,
                    admission,
                    concept,
                    target),
                Bound("g", Arrow(conceptType, Call("Option", targetType))),
                Bound("b", conceptType),
                Bound("y", targetType),
            ],
            ImpliesFormula(hypotheses, conclusion)));
    }

    private static Formula EmptyFiberCounterexampleFormula()
    {
        Formula unit = Call("Fin", Num(1));
        Formula boolean = F.Id("Bool");
        Formula admission = F.Id("A");
        Formula concept = F.Id("C");
        Formula target = F.Id("T");
        Formula answerer = F.Id("g");
        Formula fiber = F.Id("b");
        Formula value = F.Id("y");
        Formula body = And(
            ZeroError(admission, concept, target, answerer),
            And(
                new Formula.Not(FiberInhabited(unit, admission, concept, fiber)),
                And(
                    Equal(Apply(answerer, fiber), Some(value)),
                    Equal(
                        Canonical(admission, concept, target, fiber),
                        F.Id("none")))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("A", Arrow(unit, F.Id("Prop"))),
                Bound("C", Arrow(unit, boolean)),
                Bound("T", Arrow(unit, boolean)),
                Bound("g", Arrow(boolean, Call("Option", boolean))),
                Bound("b", boolean),
                Bound("y", boolean),
            ],
            body));
    }

    private static Formula.BoundVariable[] ContextVariables(
        Formula inputType,
        Formula conceptType,
        Formula targetType,
        Formula admission,
        Formula concept,
        Formula target) =>
        [
            Bound("X", F.Id("Type")),
            Bound("B", F.Id("Type")),
            Bound("Y", F.Id("Type")),
            Bound("A", Arrow(inputType, F.Id("Prop"))),
            Bound("C", Arrow(inputType, conceptType)),
            Bound("T", Arrow(inputType, targetType)),
        ];

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
