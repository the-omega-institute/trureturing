using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class OriginalOrbifoldMoonshineCharacterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Golay–Leech orbifold character equals the normalized level-one modular invariant.",
        H("Original Golay–Leech orbifold moonshine character"),
        Blocks(
            Describe.Lean(DescribeId.Create("orbifold-moonshine-character"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/OriginalOrbifoldMoonshineCharacter.character_eq_eisensteinCube_div_discriminant_sub_744"),
                H("The character as the Eisenstein cube divided by the discriminant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The shifted conformal zero-mode character of the original Golay–Leech orbifold equals the cube of the weight-four Eisenstein series divided by the level-one discriminant, with 744 subtracted, at every point of the upper half-plane.")),
                    Paragraph(Text("At each nonnegative integer weight, the original conformal zero-mode eigenspace is linearly isomorphic to the product of its theta-fixed lattice sector and its negative-parity twisted sector. The character uses the sum of the two dimensions, which equals the full eigenspace dimension at that weight.")),
                    Paragraph(Text("Multiplying the character by the discriminant gives a weight-twelve level-one modular form. The proof uses slash invariance, holomorphy and boundedness at the cusp. It subtracts the cube of the weight-four Eisenstein series to obtain a modular form of the same weight.")),
                    Paragraph(Text("The constant and linear q coefficients of the character times the discriminant are 1 and −24. The corresponding coefficients of the Eisenstein cube are 1 and 720. Thus the difference has zero constant coefficient and linear coefficient −744.")),
                    Paragraph(Text("The zero constant coefficient makes the difference a cusp form. Every weight-twelve level-one cusp form is a scalar multiple of the discriminant. The discriminant has linear q coefficient 1, so comparing linear coefficients gives the scalar −744. The discriminant has no zeros in the upper half-plane, so dividing the resulting identity gives the character formula."))),
                DescribeRole.Theorem)
        )));
}
