using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Closure;

internal sealed class SourceClosureThreeLawsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Closure/SourceClosureThreeLaws."
            + "source_closure_three_laws";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Source-semantic closure is extensive, monotone, and idempotent.",
        H("Source Closure Three Laws"),
        Blocks(Describe.Lean(
            DescribeId.Create("source-closure-three-laws"),
            DeclarationHandle.Create(Declaration),
            H("Source closure is extensive, monotone, and idempotent"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "DefinitionClosure is the canonical closure generated from the common kernel "
                        + "of the supplied source concepts; no target-defined closure is introduced.")),
                Paragraph(Text(
                    "The three public conjuncts respectively include the generating family, "
                        + "preserve inclusion into a larger family, and make a second closure pass "
                        + "equal to the first."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois"))]));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("O");
        Formula sources = F.Id("S");
        Formula larger = F.Id("T");
        Formula conceptType = Call("Concept", stateType, outputType);
        Formula familyType = Call("Set", conceptType);
        Formula closureSources = Call("DefinitionClosure", sources);
        Formula closureLarger = Call("DefinitionClosure", larger);
        Formula extensive = SubsetOf(sources, closureSources);
        Formula monotone = Implies(
            SubsetOf(sources, larger),
            SubsetOf(closureSources, closureLarger));
        Formula idempotent = Equal(
            Call("DefinitionClosure", closureSources),
            closureSources);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("O", type),
                Bound("S", familyType),
                Bound("T", familyType),
            ],
            And(extensive, And(monotone, idempotent))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula SubsetOf(Formula subset, Formula superset) =>
        new Formula.Relation(subset, FormulaRelationOperator.SubsetOf, superset);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
