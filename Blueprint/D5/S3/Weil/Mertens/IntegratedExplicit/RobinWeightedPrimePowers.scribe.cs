using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RobinWeightedPrimePowersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedPrimePowers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-root bound for the actual prime-power correction in the weighted Robin tail.",
        H("Weighted prime-power correction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-root-bound"),
                DeclarationHandle.Create(Prefix + "powerCorrection_le_roots"),
                H("Square, cube and fifth-root responses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For j at least 1 and x greater than 1, integrate Costa Pereira's three-root bound "
                    + "against the nonnegative Robin weight. For each root degree r in {2, 3, 5}, "
                    + "the contribution is the integral of the power t^(1/r) against that weight "
                    + "plus J(rj, x^(1/r))/r. The three power integrals converge because 1/r is less than j."))),
                DescribeRole.Theorem))));
}
