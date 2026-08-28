using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Knowledge;

internal sealed class RelationalWeakestPreconditionCompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/Knowledge/RelationalWeakestPreconditionComposition."
            + "universal_weakest_precondition_composition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal weakest preconditions compose in reverse process order.",
        H("Relational Weakest-Precondition Composition"),
        Blocks(Describe.Lean(
            DescribeId.Create("universal-weakest-precondition-composition"),
            DeclarationHandle.Create(Declaration),
            H("Weakest preconditions propagate backward through a composite"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The two relations have the source, intermediate, and final carriers shown in "
                    + "the formula. The predicate transformer is the canonical relational core, "
                    + "and the proof applies the pinned library composition law directly."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ObserverMemory/Knowledge/RelationalPreconditionAdjunction"))]));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula sourceType = F.Id("X");
        Formula middleType = F.Id("Y");
        Formula targetType = F.Id("Z");
        Formula first = F.Id("R");
        Formula second = F.Id("S");
        Formula target = F.Id("Q");
        Formula composite = Call("SetRelComp", first, second);
        Formula left = Call("universalWeakestPrecondition", composite, target);
        Formula right = Call(
            "universalWeakestPrecondition",
            first,
            Call("universalWeakestPrecondition", second, target));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("Y", type),
                Bound("Z", type),
                Bound("R", Call("SetRel", sourceType, middleType)),
                Bound("S", Call("SetRel", middleType, targetType)),
                Bound("Q", Call("Set", targetType)),
            ],
            Equal(left, right)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
