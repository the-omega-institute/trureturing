using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualHeightFourteenSectorDocument : IScribeDocumentDefinition
{
    private static Formula Statement() => Call("StrictAntiOn", Call("weight"), Call("Ioi", Call("threshold")));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic finite reciprocal-product sector calculus",
        H("Generic Finite Reciprocal-Product Sector Calculus"),
        Blocks(Describe.Lean(
            DescribeId.Create("actualheightfourteensector"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualHeightFourteenSector.strictAntiOn_weight_u"),
            H("Strict decrease in the height parameter"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every positive finite index size, every nonnegative shift family, and every " +
                "p in the closed interval [0,1/4], the real part of the reciprocal product is " +
                "strictly decreasing in u above the explicit threshold 4*(N+1)^2/pi^2. " +
                "The proof supplies the reusable polar-angle positivity, u- and p-derivative " +
                "signs, the endpoint continuity argument, and the signed-imaginary-part reduction. " +
                "No six-pole constants or zeta data occur in this generic source."))),
            DescribeRole.Theorem))));
}
