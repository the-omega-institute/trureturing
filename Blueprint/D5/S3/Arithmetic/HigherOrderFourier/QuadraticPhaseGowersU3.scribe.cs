using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arithmetic.HigherOrderFourier;

internal sealed class QuadraticPhaseGowersU3Document
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arithmetic/HigherOrderFourier/QuadraticPhaseGowersU3.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit quadratic phases have constant second multiplicative derivatives and maximal finite U3 energy.",
        H("Quadratic Phases and Finite U3 Energy"),
        Blocks(
            Def("energy", "finiteGowersU3Energy", "Finite U3 energy",
                "Two-direction second derivative correlations define the unnormalized eighth-power U3 energy."),
            Def("quadratic", "IsUnitQuadraticPhase", "Unit quadratic phase",
                "Every second multiplicative derivative is independent of the base point and has unit norm."),
            Thm("nonnegative", "finiteGowersU3Energy_nonneg", "U3 energy is nonnegative",
                "The finite energy is a double sum of squared correlation norms."),
            Thm("maximal", "finiteGowersU3Energy_eq_card_pow_four_of_quadratic", "Quadratic phases have maximal U3 energy",
                "Base-point independent unit second derivatives give the exact unnormalized energy equal to the fourth power of group cardinality."),
            Thm("characters", "additiveCharacter_isUnitQuadraticPhase", "Additive characters are degenerate quadratic phases",
                "A unitary additive character has constant first derivative and unit second derivative."),
            Thm("character-energy", "finiteGowersU3Energy_character", "Characters have maximal U3 energy",
                "The quadratic-phase theorem applies to every unitary additive character."),
            Thm("zero", "finiteGowersU3Energy_zero", "Zero function has zero U3 energy",
                "All iterated multiplicative derivatives of the zero function vanish.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Arithmetic/HigherOrderFourier/GowersTranslationModulationInvariance")),
        ]));

    private static DocumentBlock.Describe Def(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
