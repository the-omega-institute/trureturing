using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class SL2F5InvolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-one determinant-one matrices over the field with five elements are only the two central signs.",
        H("The SL2(F5) square-one classification"),
        Blocks(
            Paragraph(Text("For every determinant-one two by two matrix over ZMod 5, if its square is the identity, then the matrix is either the identity or its negative. This is the finite-field calculation used by the center-lift obstruction: a nontrivial projective involution cannot lift to a square-one element.")),
            Describe.Lean(
                DescribeId.Create("sl2-zmod5-square-one-eq-one-or-neg-one"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/SL2F5Involution.sl2_zmod5_square_one_eq_one_or_neg_one"),
                H("Square-one classification in SL2(F5)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every A in the determinant-one two by two matrices over ZMod 5 with A squared equal to the identity is either the identity matrix or the negative identity matrix."))),
                DescribeRole.Theorem))));
}
