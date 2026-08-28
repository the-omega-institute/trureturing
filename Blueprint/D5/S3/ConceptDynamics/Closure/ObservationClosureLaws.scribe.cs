using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Closure;

internal sealed class ObservationClosureLawsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Closure/ObservationClosureLaws."
            + "observation_closure_laws";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observation closure has the three closure laws and adds no distinctions.",
        H("Observation Closure Laws"),
        Blocks(Describe.Lean(
            DescribeId.Create("observation-closure-laws"),
            DeclarationHandle.Create(Declaration),
            H("Observation closure is extensive, monotone, idempotent, and redundant"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "DefinitionClosure is the canonical source-semantic closure constructed "
                        + "from the common observational kernel. The first three public clauses "
                        + "are its extensive, monotone, and idempotent laws.")),
                Paragraph(Text(
                    "The final public clause quantifies over every candidate in the closure. "
                        + "Inserting such a readout leaves the canonical joint kernel unchanged, "
                        + "so it cannot split a state pair left indistinguishable by the source "
                        + "family."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/Closure/SourceClosureThreeLaws")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/DefinitionEscapeLaws/"
                    + "SemanticClosureZeroGainCriterion")),
        ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula sources = F.Id("Q");
        Formula larger = F.Id("Q2");
        Formula candidate = F.Id("p");
        Formula readout = F.Id("q");
        Formula concept = Call("Concept", state, output);
        Formula familyType = Call("Set", concept);
        Formula closedSources = Call("DefinitionClosure", sources);
        Formula closedLarger = Call("DefinitionClosure", larger);

        Formula Kernel(Formula family) => Call(
            "jointKernel",
            Seq(LambdaLower, Sp, readout, Colon, Sp, family, Comma, Sp,
                Call("val", readout)));

        Formula redundant = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("p"), concept)],
            Implies(
                new Formula.Relation(
                    candidate,
                    FormulaRelationOperator.MemberOf,
                    closedSources),
                Equal(Kernel(Call("insert", candidate, sources)), Kernel(sources))));

        Formula clauses = And(
            SubsetOf(sources, closedSources),
            And(
                Implies(
                    SubsetOf(sources, larger),
                    SubsetOf(closedSources, closedLarger)),
                And(
                    Equal(Call("DefinitionClosure", closedSources), closedSources),
                    redundant)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("O"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("Q"), familyType),
                new Formula.BoundVariable(FormulaIdentifier.Create("Q2"), familyType),
            ],
            clauses));
    }
}
