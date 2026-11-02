using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramDualPairingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/LengthGramDualPairing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse-Gram dual vectors pair with the realizing rows by the Kronecker delta.",
        H("Inverse-Gram Dual Pairing"),
        Blocks(
            Paragraph(Text(
                "Given a realizing matrix M for the six-length Gram matrix G, "
                + "form the dual vector D_i from row i of G inverse and the rows "
                + "of M. The Lorentz pairing of D_i with the j-th realizing row "
                + "is then exactly the Kronecker delta. The negative determinant "
                + "assumption supplies the nonsingularity needed for the inverse.")),
            Describe.Lean(
                DescribeId.Create("length-gram-dual-pairing"),
                DeclarationHandle.Create(Prefix + "dual_pairing"),
                H("Dual vectors recover the realizing row coordinates"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof expands the Lorentz bilinear form and rearranges the "
                    + "finite sums into the matrix product G inverse times G. "
                    + "Nonsingular inverse cancellation reduces that product to "
                    + "the identity matrix entry."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        var l = F.Id("l");
        var M = F.Id("M");
        var i = F.Id("i");
        var j = F.Id("j");
        var gramEntry = Eq(
            Call("lorentz", Call("row", M, i), Call("row", M, j)),
            Call("entry", Call("lengthGram", l), i, j));
        var dualEntry = Eq(
            Call("lorentz",
                Call("dualVector", Call("lengthGram", l), M, i),
                Call("row", M, j)),
            Call("delta", i, j));
        return All("l", F.Id("Length6"),
            All("M", F.Id("Mat4"),
                Impl(
                    All("i", F.Id("Fin4"),
                        All("j", F.Id("Fin4"), gramEntry)),
                    Impl(
                        Less(Call("det", Call("lengthGram", l)), F.D(0)),
                        All("i", F.Id("Fin4"),
                            All("j", F.Id("Fin4"), dualEntry))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula Impl(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
