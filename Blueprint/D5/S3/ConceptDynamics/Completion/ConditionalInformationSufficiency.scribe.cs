using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class ConditionalInformationSufficiencyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Completion/ConditionalInformationSufficiency."
            + "conditional_information_zero_iff_support_sufficiency";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a finite prior and stochastic target kernel, zero conditional information "
            + "is equivalent both to conditional independence and to target-kernel "
            + "constancy on every positive-prior concept fiber.",
        H("Conditional Information and Support Sufficiency"),
        Blocks(Describe.Lean(
            DescribeId.Create("zero-conditional-information-is-support-sufficiency"),
            DeclarationHandle.Create(Declaration),
            H("Zero conditional information characterizes support sufficiency"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite PMF prior, a PMF-valued target kernel, and a deterministic "
                        + "concept readout construct the displayed joint law. The concept "
                        + "coordinate is moved first before conditional information is read.")),
                Paragraph(Text(
                    "The first equivalence is the conditional-product law on every occupied "
                        + "concept fiber. The second equivalence says precisely that two "
                        + "positive-prior states with the same concept have the same target law.")),
                Paragraph(Text(
                    "For the reverse implication, one positive-prior representative is chosen "
                        + "from each occupied fiber. Its target law supplies a normalized "
                        + "channel, and the resulting Markov factorization forces zero "
                        + "conditional information."))),
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
        Formula otherState = F.Id("xprime");
        Formula conceptValue = F.Id("c");
        Formula targetValue = F.Id("y");
        Formula prior = F.Id("mu");
        Formula kernel = F.Id("K");
        Formula concept = F.Id("concept");
        Formula joint = F.Id("jointLaw");
        Formula conditioned = F.Id("conditionedLaw");
        Formula pmfTarget = Call("PMF", targetType);
        Formula stateTargetType = Call("Prod", stateType, targetType);
        Formula targetStateType = Call("Prod", targetType, stateType);

        Formula priorCell = Apply(prior, state);
        Formula kernelCell = Apply(Apply(kernel, state), targetValue);
        Formula sameConcept = Equal(conceptValue, Apply(concept, state));
        Formula jointDefiniens = Call(
            "ite",
            sameConcept,
            Multiply(Call("toReal", priorCell), Call("toReal", kernelCell)),
            new Formula.Number(0));
        Formula jointLet = F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp, joint, F.Sp, F.Colon, F.Eq, F.Sp,
            Lambda(Pair(state, Pair(conceptValue, targetValue)), jointDefiniens),
            F.Semi, F.Sp);
        Formula conditionedLet = F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp, conditioned, F.Sp, F.Colon, F.Eq,
            F.Sp, Call("yFirstLaw", joint), F.Semi, F.Sp);

        Formula informationZero = Equal(
            Call("conditionalMutualInformation", conditioned), new Formula.Number(0));
        Formula conditionalSlice = Call("conditional", conditioned, conceptValue);
        Formula stateMarginal = Call("marginal", conditionalSlice, state);
        Formula swappedConditional = Lambda(
            Typed(Pair(targetValue, state), targetStateType),
            Call("conditional", conditioned, conceptValue, state, targetValue));
        Formula targetMarginal = Call("marginal", swappedConditional, targetValue);
        Formula productSlice = Lambda(
            Typed(Pair(state, targetValue), stateTargetType),
            Multiply(stateMarginal, targetMarginal));
        Formula conditionalProduct = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("c"),
            conceptType,
            Implies(
                NotEqual(Call("marginal", conditioned, conceptValue), new Formula.Number(0)),
                Equal(conditionalSlice, productSlice)));

        Formula otherPriorCell = Apply(prior, otherState);
        Formula supportPremises = And(
            LessThan(new Formula.Number(0), Call("toReal", priorCell)),
            And(
                LessThan(new Formula.Number(0), Call("toReal", otherPriorCell)),
                Equal(Apply(concept, state), Apply(concept, otherState))));
        Formula supportConstancy = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("x", stateType),
                Bound("xprime", stateType),
            ],
            Implies(
                supportPremises,
                Equal(Apply(kernel, state), Apply(kernel, otherState))));
        Formula characterization = And(
            Iff(informationZero, conditionalProduct),
            Iff(informationZero, supportConstancy));

        Formula instances = And(
            Call("Fintype", stateType),
            And(Call("Fintype", conceptType), Call("Fintype", targetType)));
        Formula dataBinders = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("mu", Call("PMF", stateType)),
                Bound("K", Arrow(stateType, pmfTarget)),
                Bound("concept", Arrow(stateType, conceptType)),
            ],
            F.Seq(jointLet, conditionedLet, characterization));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("C", type),
                Bound("Y", type),
            ],
            Implies(instances, dataBinders)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Pair(Formula first, Formula second) =>
        F.Seq(F.Open, first, F.Comma, second, F.Close);

    private static Formula Typed(Formula binder, Formula domain) =>
        F.Seq(binder, F.Colon, F.Sp, domain);

    private static Formula Lambda(Formula binder, Formula body) =>
        F.Seq(F.Open, binder, F.Sp, F.Mapsto, F.Sp, body, F.Close);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
}
