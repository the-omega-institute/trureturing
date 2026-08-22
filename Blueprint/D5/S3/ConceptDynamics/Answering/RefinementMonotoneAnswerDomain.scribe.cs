using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Answering;

internal sealed class RefinementMonotoneAnswerDomainDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Answering/RefinementMonotoneAnswerDomain.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical safe answers and their admitted answer domain grow monotonically under "
            + "concept refinement.",
        H("Refinement-Monotone Answer Domain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinement-preserves-the-canonical-answer-value"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "refinement_monotone_answer_domain"),
                H("Refinement preserves the canonical answer value"),
                StatementSource.FromAuthor(AnswerPreservationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose a coarse concept canonically answers y at an admitted state x. "
                            + "A refinement splits coarse fibers without merging distinct ones, "
                            + "so every state in the refined fiber of x still has target y.")),
                    Paragraph(Text(
                        "The coarse canonical answer supplies a zero-error answerer on refined "
                            + "fibers by composition with the factor map. Since x inhabits the "
                            + "relevant refined fiber, safe-answer coverage maximality forces "
                            + "the refined canonical answer to return the same value y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-admitted-answer-domain-is-monotone-under-refinement"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "answer_domain_monotone"),
                H("The admitted answer domain is monotone under refinement"),
                StatementSource.FromAuthor(AnswerDomainMonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The answer domain contains exactly the admitted states where the "
                            + "canonical safe answerer returns some target value. Extracting that "
                            + "value and applying answer preservation shows that every state "
                            + "answered by a coarse concept is also answered by any refinement.")),
                    Paragraph(Text(
                        "The Boolean smoke instance shows that the containment can be strict: a "
                            + "constant concept cannot safely distinguish false from true, while "
                            + "the identity refinement answers both admitted states."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula Canonical(
        Formula admission,
        Formula concept,
        Formula target,
        Formula fiber) =>
        Call("canonicalSafeAnswer", admission, concept, target, fiber);

    private static Formula Some(Formula value) => Call("some", value);

    private static Formula AnswerDomain(
        Formula admission,
        Formula concept,
        Formula target) =>
        Call("answerDomain", admission, concept, target);

    private static Formula AnswerPreservationFormula()
    {
        Formula stateType = F.Id("X");
        Formula coarseType = F.Id("C");
        Formula fineType = F.Id("D");
        Formula targetType = F.Id("Y");
        Formula admission = F.Id("A");
        Formula coarse = new Formula.Subscript(F.Id("q"), coarseType);
        Formula fine = new Formula.Subscript(F.Id("q"), fineType);
        Formula target = F.Id("T");
        Formula state = F.Id("x");
        Formula value = F.Id("y");
        Formula coarseAnswer = Equal(
            Canonical(admission, coarse, target, Apply(coarse, state)),
            Some(value));
        Formula fineAnswer = Equal(
            Canonical(admission, fine, target, Apply(fine, state)),
            Some(value));
        Formula hypotheses = And(
            Refines(coarse, fine),
            And(Apply(admission, state), coarseAnswer));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                .. ContextVariables(
                    stateType,
                    coarseType,
                    fineType,
                    targetType,
                    admission,
                    coarse,
                    fine,
                    target),
                Bound("x", stateType),
                Bound("y", targetType),
            ],
            ImpliesFormula(hypotheses, fineAnswer)));
    }

    private static Formula AnswerDomainMonotonicityFormula()
    {
        Formula stateType = F.Id("X");
        Formula coarseType = F.Id("C");
        Formula fineType = F.Id("D");
        Formula targetType = F.Id("Y");
        Formula admission = F.Id("A");
        Formula coarse = new Formula.Subscript(F.Id("q"), coarseType);
        Formula fine = new Formula.Subscript(F.Id("q"), fineType);
        Formula target = F.Id("T");
        Formula inclusion = new Formula.Relation(
            AnswerDomain(admission, coarse, target),
            FormulaRelationOperator.SubsetOf,
            AnswerDomain(admission, fine, target));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                .. ContextVariables(
                    stateType,
                    coarseType,
                    fineType,
                    targetType,
                    admission,
                    coarse,
                    fine,
                    target),
            ],
            ImpliesFormula(Refines(coarse, fine), inclusion)));
    }

    private static Formula.BoundVariable[] ContextVariables(
        Formula stateType,
        Formula coarseType,
        Formula fineType,
        Formula targetType,
        Formula admission,
        Formula coarse,
        Formula fine,
        Formula target) =>
        [
            Bound("X", F.Id("Type")),
            Bound("C", F.Id("Type")),
            Bound("D", F.Id("Type")),
            Bound("Y", F.Id("Type")),
            Bound("A", Arrow(stateType, F.Id("Prop"))),
            Bound("qC", Arrow(stateType, coarseType)),
            Bound("qD", Arrow(stateType, fineType)),
            Bound("T", Arrow(stateType, targetType)),
        ];

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
