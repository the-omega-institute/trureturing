using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Closure;

internal sealed class IndexedObservationClosureLawsDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Closure/IndexedObservationClosureLaws."
            + "indexed_observation_closure_laws";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An arbitrary indexed universe of heterogeneous observations induces an "
            + "extensive, monotone, idempotent closure with redundant added members.",
        H("Indexed Observation Closure Laws"),
        Blocks(Describe.Lean(
            DescribeId.Create("indexed-observation-closure-laws"),
            DeclarationHandle.Create(Declaration),
            H("Heterogeneous indexed observations generate a Galois closure"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observation universe is an arbitrary index type. Each index may "
                        + "have its own output type, so the statement does not collapse the "
                        + "source language to one shared codomain or to all functions into it.")),
                Paragraph(Text(
                    "The selected kernel K records pairs identified by every chosen index, "
                        + "and I returns exactly the indices whose observations are invariant "
                        + "on a relation. The first public clause exposes Cl(Q) = I(K(Q)).")),
                Paragraph(Text(
                    "The remaining public clauses state extensivity, monotonicity, "
                        + "idempotence, and the unchanged-kernel criterion for every "
                        + "observation admitted by the closure."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion"))]));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula EqualFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula MemberOf(Formula member, Formula set) =>
        new Formula.Relation(member, FormulaRelationOperator.MemberOf, set);

    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);

    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = And(clauses[index], result);
        }
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula outputFamily = F.Id("Y");
        Formula observations = F.Id("q");
        Formula index = F.Id("i");
        Formula family = F.Id("Q");
        Formula larger = F.Id("Q2");
        Formula familyType = Call("Set", indexType);
        Formula observationType = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Arrow(stateType, Apply(outputFamily, index)));

        Formula Kernel(Formula selected) =>
            Call("selectedObservationKernel", observations, selected);
        Formula Invariants(Formula relation) =>
            Call("invariantObservationIndices", observations, relation);
        Formula Closure(Formula selected) =>
            Call("indexedObservationClosure", observations, selected);

        Formula closedFamily = Closure(family);
        Formula redundancy = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Implies(
                MemberOf(index, closedFamily),
                EqualFormula(
                    Kernel(Call("insert", index, family)),
                    Kernel(family))));

        Formula clauses = Conjoin(
            EqualFormula(Closure(family), Invariants(Kernel(family))),
            SubsetOf(family, closedFamily),
            Implies(
                SubsetOf(family, larger),
                SubsetOf(closedFamily, Closure(larger))),
            EqualFormula(Closure(closedFamily), closedFamily),
            redundancy);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", type),
                Bound("X", type),
                Bound("Y", Arrow(indexType, type)),
                Bound("q", observationType),
                Bound("Q", familyType),
                Bound("Q2", familyType),
            ],
            clauses));
    }
}
