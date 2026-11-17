using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class QuadraticPhaseEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite quadratic additive-character phases over an odd finite field have energy equal to the field cardinality.",
        H("Quadratic additive-character phase energy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-phase-energy"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/QuadraticPhaseEnergy.quadratic_phase_energy"),
                H("Quadratic phase energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite field of odd characteristic, a nontrivial complex "
                        + "additive character, a nonzero quadratic coefficient, and any "
                        + "linear coefficient, the product of the two opposite quadratic "
                        + "phase sums equals the field cardinality. The proof expands the "
                        + "double sum, translates one variable, and applies additive-character "
                        + "orthogonality to the resulting linear sum."))),
                DescribeRole.Theorem))));
}
