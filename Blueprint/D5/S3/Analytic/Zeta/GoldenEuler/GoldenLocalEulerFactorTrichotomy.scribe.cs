using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta.GoldenEuler;

internal sealed class GoldenLocalEulerFactorTrichotomyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Zeta/GoldenEuler/GoldenLocalEulerFactorTrichotomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic charge values generate the split, inert, and ramified local Euler shapes.",
        H("Golden Local Euler Factor Trichotomy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-local-factor-trichotomy"),
                DeclarationHandle.Create(Prefix + "charged_local_factor_trichotomy"),
                H("Three charge values give three local Euler factors"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The local model multiplies a neutral factor by a quadratic charge "
                            + "factor.")),
                    Paragraph(Text(
                        "Charge one gives two degree-one factors, charge minus one combines them "
                            + "into a degree-two factor, and charge zero removes the nontrivial "
                            + "factor.")),
                    Paragraph(Text(
                        "The theorem is universal field algebra. Residue classes modulo five are "
                            + "handled by the separate arithmetic classification."))),
                DescribeRole.Theorem))));
}
