using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Answering;

internal sealed class RefinementSafeCoverageMonotonicityDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Answering/RefinementSafeCoverageMonotonicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concept refinement preserves canonical safe answers and monotonically enlarges both "
            + "their admitted domain and its probability.",
        H("Refinement-Monotone Safe Coverage"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("safe-coverage"),
                DeclarationHandle.Create(DeclarationPrefix + "safeCoverage"),
                H("Safe coverage"),
                StatementSource.FromAuthor(SafeCoverageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Safe coverage is constructed by measuring the canonical admitted "
                        + "safe-answer domain under the supplied probability law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("refinement-preserves-answers-domains-and-safe-coverage"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "refinement_safe_coverage_monotonicity"),
                H("Refinement monotonically enlarges safe coverage"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first public conjunct applies the frozen pointwise theorem: every "
                            + "canonical answer at an admitted state survives refinement with the "
                            + "same target value.")),
                    Paragraph(Text(
                        "The second conjunct exposes inclusion of admitted answer domains. The "
                            + "third measures that same inclusion under an arbitrary probability "
                            + "law and applies measure monotonicity."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula coarseType = F.Id("C");
        Formula fineType = F.Id("D");
        Formula targetType = F.Id("Y");
        Formula probability = F.Id("P");
        Formula admission = F.Id("A");
        Formula coarse = F.Id("qC");
        Formula fine = F.Id("qD");
        Formula target = F.Id("T");
        Formula state = F.Id("x");
        Formula value = F.Id("y");
        Formula coarseAnswer = Equal(
            Call("canonicalSafeAnswer", admission, coarse, target, Apply(coarse, state)),
            Call("some", value));
        Formula fineAnswer = Equal(
            Call("canonicalSafeAnswer", admission, fine, target, Apply(fine, state)),
            Call("some", value));
        Formula pointwise = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", stateType), Bound("y", targetType)],
            Implies(And(Apply(admission, state), coarseAnswer), fineAnswer));
        Formula coarseDomain = Call("answerDomain", admission, coarse, target);
        Formula fineDomain = Call("answerDomain", admission, fine, target);
        Formula domainInclusion = new Formula.Relation(
            coarseDomain, FormulaRelationOperator.SubsetOf, fineDomain);
        Formula coverageOrder = new Formula.Relation(
            Call("safeCoverage", probability, admission, coarse, target),
            FormulaRelationOperator.LessThanOrEqual,
            Call("safeCoverage", probability, admission, fine, target));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("C", F.Id("Type")),
                Bound("D", F.Id("Type")),
                Bound("Y", F.Id("Type")),
                Bound("mX", Call("MeasurableSpace", stateType)),
                Bound("P", Call("ProbabilityMeasure", stateType)),
                Bound("A", Arrow(stateType, F.Id("Prop"))),
                Bound("qC", Arrow(stateType, coarseType)),
                Bound("qD", Arrow(stateType, fineType)),
                Bound("T", Arrow(stateType, targetType)),
            ],
            Implies(
                Call("Refines", coarse, fine),
                And(pointwise, And(domainInclusion, coverageOrder)))));
    }

    private static Formula SafeCoverageFormula()
    {
        Formula stateType = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula probability = F.Id("P");
        Formula admission = F.Id("A");
        Formula concept = F.Id("q");
        Formula target = F.Id("T");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("B", F.Id("Type")),
                Bound("Y", F.Id("Type")),
                Bound("mX", Call("MeasurableSpace", stateType)),
                Bound("P", Call("ProbabilityMeasure", stateType)),
                Bound("A", Arrow(stateType, F.Id("Prop"))),
                Bound("q", Arrow(stateType, conceptType)),
                Bound("T", Arrow(stateType, targetType)),
            ],
            Equal(
                Call("safeCoverage", probability, admission, concept, target),
                Call(
                    "measure",
                    probability,
                    Call("answerDomain", admission, concept, target)))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
