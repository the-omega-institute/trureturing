using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Irrationality;

internal sealed class TwoFacedPrivilegeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var v1 = Id("v1");
        var v2 = Id("v2");
        var naturals = Id("N");

        var quadratic = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("v1"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("v2"), naturals),
            ],
            Equal(Call("deficit", v1, v2), Call("deficitContraction", v1, v2)));

        var statement = new Formula.Logic(
            quadratic,
            FormulaLogicOperator.And,
            Call("Irrational", Subtract(Num(1), Id("tribonacciConstant"))));

        const string declarationPrefix =
            "D5/S3/Constants/Irrationality/TwoFacedPrivilege.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Deficit integrality holds on two faces and does not transfer to three.",
            H("Two Faced Privilege"),
            Blocks(
                Paragraph(Text(
                    "On the quadratic tower the deficit read on the expanding face equals the "
                        + "one read on the contracting face, and it is an integer. The reason is "
                        + "structural: those two faces are the entire conjugate set, so the "
                        + "irrational parts cancel when they are subtracted.")),
                Paragraph(Text(
                    "On the cubic tower that cancellation is unavailable. Splitting off the "
                        + "expanding root leaves a pair whose sum is one minus the base, and "
                        + "that number is irrational. Integrality of the deficit is therefore a "
                        + "privilege of having exactly two faces, which is what the source "
                        + "claims and what this conjunction states.")),
                Paragraph(Text(
                    "Both halves were already proved and neither is restated. What did not "
                        + "exist was any statement putting them together, so a claim whose two "
                        + "halves were green had no formal counterpart. Building the cubic "
                        + "deficit itself would require an integer-indexed naming layer that "
                        + "does not exist; the contrast needs none of it.")),
                Describe.Lean(
                    DescribeId.Create("integrality-is-a-two-faced-privilege"),
                    DeclarationHandle.Create(
                        declarationPrefix + "integrality_is_a_two_faced_privilege"),
                    H("Integrality is a two-faced privilege"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The displayed left conjunct is the agreement of the two faces, which is "
                            + "the mechanism; the integrality it yields is carried alongside it "
                            + "in the theorem. The right conjunct is the cubic obstruction."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S3/Constants/Irrationality/CubicConjugateTrace")),
            ]));
    }
}
