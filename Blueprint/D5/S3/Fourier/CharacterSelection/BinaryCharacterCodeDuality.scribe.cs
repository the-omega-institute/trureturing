using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class BinaryCharacterCodeDualityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary character code is exactly the orthogonal complement of its relations.",
        H("Binary Character Code Duality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("standard-coordinate-pairing"),
                DeclarationHandle.Create(Prefix + "standardCoordinatePairing"),
                H("Standard coordinate pairing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the standard dot-product bilinear form on the finite "
                        + "coordinate space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("character-relation-space"),
                DeclarationHandle.Create(Prefix + "characterRelationSpace"),
                H("Character relation space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A coefficient vector is a relation when its linear combination "
                        + "of the character family vanishes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("character-code"),
                DeclarationHandle.Create(Prefix + "characterCode"),
                H("Character code"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The code is the range of the joint character-profile map into "
                        + "the finite coordinate space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("character-orthogonal-complement"),
                DeclarationHandle.Create(Prefix + "characterOrthogonalComplement"),
                H("Character orthogonal complement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Orthogonal complementation is taken relative to the named standard "
                        + "coordinate pairing."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("character-code-equals-relation-space-orthogonal"),
                DeclarationHandle.Create(
                    Prefix + "character_code_eq_relation_space_orthogonal"),
                H("Character code is the relation orthogonal"),
                StatementSource.FromAuthor(DualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For FPOD 93.1 the coefficient field is F2. The Lean theorem "
                            + "proves the same equality over every field.")),
                    Paragraph(Text(
                        "One inclusion evaluates every vanishing character combination. "
                            + "The reverse inclusion follows from dual-map rank equality, "
                            + "rank-nullity, and nondegeneracy of the dot product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("standard-orthogonal-complement-involutive"),
                DeclarationHandle.Create(
                    Prefix + "standard_orthogonal_complement_involutive"),
                H("Double orthogonal complementation returns the space"),
                StatementSource.FromAuthor(InvolutionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The standard dot product is symmetric and nondegenerate, so every "
                        + "subspace of the finite coordinate space equals its double "
                        + "orthogonal complement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("field-coefficients-are-necessary"),
                DeclarationHandle.Create(Prefix + "field_coefficients_are_necessary"),
                H("General coefficient rings need not satisfy code duality"),
                StatementSource.FromAuthor(IntegerCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over the integers, the single functional given by multiplication "
                        + "by two has zero relation space, but its realized code is only "
                        + "the even integers rather than the full orthogonal."))),
                DescribeRole.Theorem))));

    private static Formula DualityFormula()
    {
        Formula character = F.Id("chi");
        Formula code = new Formula.Subscript(F.Id("C"), character);
        Formula relations = new Formula.Subscript(F.Id("R"), character);
        Formula orthogonal = Seq(relations, Caret, Grp(Perp));
        return Disp(Seq(code, Sp, Eq, Sp, orthogonal, Dot));
    }

    private static Formula InvolutionFormula()
    {
        Formula space = F.Id("S");
        Formula orthogonal = Seq(space, Caret, Grp(Perp));
        Formula doubleOrthogonal = Seq(Open, orthogonal, Close, Caret, Grp(Perp));
        return Disp(Seq(doubleOrthogonal, Sp, Eq, Sp, space, Dot));
    }

    private static Formula IntegerCounterexampleFormula()
    {
        Formula state = F.Id("z");
        Formula coefficient = F.Id("a");
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula doubledState = Seq(state, Sp, Mapsto, Sp, D(2), state);
        Formula doubledCoefficient = Seq(coefficient, Sp, Mapsto, Sp, D(2), coefficient);
        Formula range = Seq(Operatorname, Grp(F.Id("range")), Open, doubledState, Close);
        Formula kernel = Seq(Operatorname, Grp(F.Id("ker")), Open, doubledCoefficient, Close);
        Formula orthogonal = Seq(kernel, Caret, Grp(Perp));
        return Disp(Seq(
            state, Comma, Sp, coefficient, Colon, Sp, integers, SemiSpace,
            range, Sp, Neq, Sp, orthogonal, Dot));
    }
}
