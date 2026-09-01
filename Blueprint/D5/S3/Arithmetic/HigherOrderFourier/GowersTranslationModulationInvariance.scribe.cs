using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arithmetic.HigherOrderFourier;

internal sealed class GowersTranslationModulationInvarianceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arithmetic/HigherOrderFourier/GowersTranslationModulationInvariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite U2 derivative energy is invariant under additive translation and unitary-character modulation.",
        H("Gowers Translation and Modulation Invariance"),
        Blocks(
            Def("translate", "translateFunction", "Additive translation",
                "A finite-group function is shifted by adding one fixed group element to its input."),
            Def("character", "FiniteUnitaryAdditiveCharacter", "Unitary additive character",
                "The character is multiplicative under group addition and has unit complex norm."),
            Def("modulate", "modulateFunction", "Character modulation",
                "A function is multiplied pointwise by a unitary additive character."),
            Thm("derivative-translate", "multiplicativeDerivative_translate", "Derivative translates its evaluation point",
                "Translation of a function becomes translation of every derivative evaluation."),
            Thm("energy-translate", "finiteGowersU2Energy_translate", "U2 energy is translation invariant",
                "Finite additive reindexing preserves every directional correlation norm."),
            Thm("character-derivative", "multiplicativeDerivative_character", "Character derivative is directional phase",
                "The multiplicative derivative of a unitary character is constant in the base point."),
            Thm("derivative-modulate", "multiplicativeDerivative_modulate", "Modulation factors derivatives",
                "A modulated derivative is the original derivative multiplied by the unit directional phase."),
            Thm("energy-modulate", "finiteGowersU2Energy_modulate", "U2 energy is modulation invariant",
                "Unit character phases do not change directional correlation norms."),
            Thm("character-energy", "finiteGowersU2Energy_character_eq_one", "Characters have maximal affine energy",
                "Every unitary additive character has the same U2 energy as the constant unit function.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Arithmetic/HigherOrderFourier/FiniteGowersCubeMoment")),
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
