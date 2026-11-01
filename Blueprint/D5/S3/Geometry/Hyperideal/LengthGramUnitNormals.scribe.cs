using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramUnitNormalsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/LengthGramUnitNormals.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive inverse-Gram diagonals normalize the dual vectors to unit Lorentz normals.",
        H("Unit Normals from the Inverse-Gram Dual Basis"),
        Blocks(
            Paragraph(Text(
                "For a realizing matrix M of a positive six-length Gram matrix, "
                + "the inverse-Gram dual vector at each coordinate has positive "
                + "Lorentz square. Dividing by the positive square root of that "
                + "square produces a unit normal. The realizing rows themselves "
                + "are unit because the diagonal of the length Gram matrix is one.")),
            Describe.Lean(
                DescribeId.Create("length-gram-dual-unit-normal"),
                DeclarationHandle.Create(Prefix + "dual_unit_normal"),
                H("The normalized dual vector is unit"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inverse-diagonal positivity theorem supplies a positive "
                    + "normalizing denominator. The inverse-Gram dual metric then "
                    + "reduces the Lorentz square to that denominator squared, "
                    + "and the finite bilinear expansion finishes the normalization."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        var l = F.Id("l");
        var M = F.Id("M");
        var i = F.Id("i");
        var gram = Call("lengthGram", l);
        var gramEntry = Eq(
            Call("lorentz", Call("row", M, i), Call("row", M, i)),
            Call("entry", gram, i, i));
        var dualEntry = Eq(
            Call("lorentz", Call("unitDualNormal", gram, M, i),
                Call("unitDualNormal", gram, M, i)),
            F.D(1));
        var positiveLength = All("k", F.Id("Fin6"), Greater(Call("l", F.Id("k")), F.D(0)));
        return All("l", F.Id("Length6"), All("M", F.Id("Mat4"),
            Impl(
                All("i", F.Id("Fin4"), gramEntry),
                Impl(positiveLength,
                    Impl(Less(Call("det", gram), F.D(0)),
                        All("i", F.Id("Fin4"), dualEntry))))));
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

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
