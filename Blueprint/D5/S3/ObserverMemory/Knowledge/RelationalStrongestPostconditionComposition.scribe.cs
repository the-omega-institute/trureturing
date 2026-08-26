using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Knowledge;

internal sealed class RelationalStrongestPostconditionCompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/Knowledge/RelationalStrongestPostconditionComposition."
            + "relational_strongest_postcondition_composition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relational strongest postconditions compose in forward process order.",
        H("Relational Strongest-Postcondition Composition"),
        Blocks(Describe.Lean(
            DescribeId.Create("relational-strongest-postcondition-composition"),
            DeclarationHandle.Create(Declaration),
            H("Strongest postconditions follow the process order"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The displayed equality is between set transformers. Relational composition "
                    + "first applies R and then S, while relational image first propagates through "
                    + "R and then through S; the proof is the pinned library image law."))),
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
        Formula composite = Call("SetRelComp", first, second);
        Formula left = Call("relationalStrongestPostcondition", composite);
        Formula right = Call(
            "compose",
            Call("relationalStrongestPostcondition", second),
            Call("relationalStrongestPostcondition", first));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("Y", type),
                Bound("Z", type),
                Bound("R", Call("SetRel", sourceType, middleType)),
                Bound("S", Call("SetRel", middleType, targetType)),
            ],
            Equal(left, right)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
