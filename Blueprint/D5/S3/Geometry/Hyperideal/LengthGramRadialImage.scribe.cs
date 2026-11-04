using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramRadialImageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/LengthGramRadialImage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized radial image is exactly the nonnegative coefficient slice cut out by the Gram halfspaces.",
        H("Radial Image as a Gram Halfspace Slice"),
        Blocks(
            Paragraph(Text(
                "The common cut body is defined by nonnegative coefficients, unit total mass, "
                + "and the four Gram row inequalities. Radial normalization removes the unit-mass "
                + "scale while preserving the signs. Conversely, a nonzero vector on the unit "
                + "negative quadric and in these eight coefficient halfspaces has positive total "
                + "mass; dividing by that mass returns a point of the cut body whose radial image "
                + "is the original vector.")),
            Describe.Lean(
                DescribeId.Create("length-gram-radial-image-halfspace-slice"),
                DeclarationHandle.Create(Prefix + "radial_image_halfspace_slice"),
                H("The radial image equals the Gram halfspace slice"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The reverse inclusion is constructive: the sum of the nonnegative coordinates "
                    + "is positive because the quadratic value is -1. Normalizing by this sum "
                    + "preserves every Gram inequality and makes the radial denominator exactly "
                    + "the reciprocal of the sum."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        var l = F.Id("l");
        var positiveLength = All("k", F.Id("Fin6"), Greater(Call("l", F.Id("k")), F.D(0)));
        return All("l", F.Id("Length6"),
            Impl(positiveLength,
                Eq(Call("image", Call("radial", l), Call("cutBody", l)),
                    Call("halfspaceSlice", l))));
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
}

