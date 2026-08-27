using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TargetRisk;

internal sealed class MaximumFactorCompatibleSubdomainDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/TargetRisk/MaximumFactorCompatibleSubdomain."
            + "maximum_factor_compatible_subdomain";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Largest target-consistent fiber blocks give the sharp factor-compatible domain size.",
        H("Maximum Factor-Compatible Subdomain"),
        Blocks(Describe.Lean(
            DescribeId.Create("maximum-factor-compatible-subdomain"),
            DeclarationHandle.Create(Declaration),
            H("Largest target blocks give the exact compatible-domain size"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The bound is constructed directly from the finite state carrier. For each "
                        + "realized concept value, it counts the largest joint concept-target "
                        + "block and then sums those maxima.")),
                Paragraph(Text(
                    "Fiberwise factorization makes every admitted concept fiber fit inside one "
                        + "such block. Conversely, selecting one maximizing target block in every "
                        + "realized concept fiber gives an admitted domain attaining the bound."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/ConceptFiberDecomposition")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula stateType = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula concept = F.Id("C");
        Formula target = F.Id("T");
        Formula admitted = F.Id("A");
        Formula conceptValue = F.Id("b");
        Formula representative = F.Id("r");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula admittedType = Call("Finset", stateType);

        Formula ConceptAt(Formula state) => Apply(concept, state);
        Formula TargetAt(Formula state) => Apply(target, state);
        Formula Member(Formula state, Formula domain) =>
            Seq(state, Sp, InMacro, Sp, domain);

        Formula BlockCard(Formula b, Formula r) => Call(
            "card",
            new Formula.SetBuilder(
                And(
                    Equal(ConceptAt(left), b),
                    Equal(TargetAt(left), TargetAt(r))),
                left,
                stateType));

        Formula conceptFiber = new Formula.SetBuilder(
            Equal(ConceptAt(representative), conceptValue),
            representative,
            stateType);
        Formula fiberMaximum = Call(
            "max",
            representative,
            conceptFiber,
            BlockCard(conceptValue, representative));
        Formula coverageBound = Call(
            "sum",
            conceptValue,
            Call("image", concept, stateType),
            fiberMaximum);

        Formula FactorsOn(Formula domain) => new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", stateType), Bound("y", stateType)],
            Implies(
                And(
                    And(Member(left, domain), Member(right, domain)),
                    Equal(ConceptAt(left), ConceptAt(right))),
                Equal(TargetAt(left), TargetAt(right))));

        Formula upperBound = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("A"),
            admittedType,
            Implies(
                FactorsOn(admitted),
                LessOrEqual(Call("card", admitted), coverageBound)));
        Formula attained = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("A"),
            admittedType,
            And(
                FactorsOn(admitted),
                Equal(Call("card", admitted), coverageBound)));

        Formula conclusion = And(upperBound, attained);
        Formula finitePremise = Call("Fintype", stateType);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("B", type),
                Bound("Y", type),
                Bound("C", Arrow(stateType, conceptType)),
                Bound("T", Arrow(stateType, targetType)),
            ],
            Implies(finitePremise, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
