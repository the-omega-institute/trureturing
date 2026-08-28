using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class PositivePriorConditionalIndependenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Completion/PositivePriorConditionalIndependence."
            + "positive_prior_sufficiency_iff_conditional_independence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a finite state space with a pointwise positive prior, stochastic target "
            + "sufficiency is equivalent to conditional independence given the concept.",
        H("Positive-Prior Conditional Independence"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-prior-sufficiency-is-conditional-independence"),
            DeclarationHandle.Create(Declaration),
            H("Stochastic sufficiency is conditional independence"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite source state has a pointwise positive PMF prior and a "
                        + "PMF-valued target kernel. A deterministic concept readout and "
                        + "these two probability primitives construct the displayed joint law.")),
                Paragraph(Text(
                    "The kernel factors through the concept exactly when the target and "
                        + "source state satisfy the cross-multiplied conditional-product "
                        + "identity on every concept value.")),
                Paragraph(Text(
                    "Positivity is used in the reverse direction to cancel both the state "
                        + "mass and the mass of its concept fiber. This upgrades the usual "
                        + "almost-sure statement to full-domain stochastic factorization."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Entropy/Submodularity/MarkovDataProcessing"))]));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula stateType = F.Id("X");
        Formula conceptType = F.Id("C");
        Formula targetType = F.Id("Y");
        Formula state = F.Id("x");
        Formula conceptValue = F.Id("c");
        Formula targetValue = F.Id("y");
        Formula prior = F.Id("mu");
        Formula kernel = F.Id("K");
        Formula concept = F.Id("concept");
        Formula reduced = F.Id("Kbar");
        Formula joint = F.Id("jointLaw");
        Formula pmfTarget = Call("PMF", targetType);
        Formula jointCell = ApplyMany(joint, state, conceptValue, targetValue);
        Formula priorCell = Apply(prior, state);
        Formula kernelCell = Apply(Apply(kernel, state), targetValue);
        Formula sameConcept = Relation(
            conceptValue, FormulaRelationOperator.Equal, Apply(concept, state));
        Formula jointDefiniens = Call(
            "ite",
            sameConcept,
            Multiply(Call("toReal", priorCell), Call("toReal", kernelCell)),
            new Formula.Number(0));
        Formula jointLet = F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp, joint, F.Sp, F.Colon, F.Eq, F.Sp,
            F.Open, state, F.Comma, F.Open, conceptValue, F.Comma, targetValue,
            F.Close, F.Close, F.Sp, F.Mapsto, F.Sp, jointDefiniens, F.Semi, F.Sp);
        Formula positivePrior = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            stateType,
            Relation(new Formula.Number(0), FormulaRelationOperator.LessThan, priorCell));
        Formula factorization = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("Kbar"),
            Arrow(conceptType, pmfTarget),
            Relation(kernel, FormulaRelationOperator.Equal,
                Call("compose", reduced, concept)));
        Formula yFirst = Call("yFirstLaw", joint);
        Formula conditionalIdentity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("x", stateType),
                Bound("c", conceptType),
                Bound("y", targetType),
            ],
            Relation(
                Multiply(jointCell, Call("marginal", yFirst, conceptValue)),
                FormulaRelationOperator.Equal,
                Multiply(
                    Call("xyProjection", joint, state, conceptValue),
                    Call("xzProjection", yFirst, conceptValue, targetValue))));
        Formula instancePremise = And(
            Call("Fintype", stateType),
            Call("Fintype", targetType));
        Formula jointBinder = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("mu", Call("PMF", stateType)),
                Bound("K", Arrow(stateType, pmfTarget)),
                Bound("concept", Arrow(stateType, conceptType)),
            ],
            Implies(
                positivePrior,
                F.Seq(jointLet,
                    Logic(factorization, FormulaLogicOperator.Iff, conditionalIdentity))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("C", type),
                Bound("Y", type),
            ],
            Implies(instancePremise, jointBinder)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula ApplyMany(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Relation(
        Formula left,
        FormulaRelationOperator operation,
        Formula right) => new Formula.Relation(left, operation, right);

    private static Formula Logic(
        Formula left,
        FormulaLogicOperator operation,
        Formula right) => new Formula.Logic(left, operation, right);

    private static Formula And(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        Logic(premise, FormulaLogicOperator.Implies, conclusion);
}
