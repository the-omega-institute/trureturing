using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class LiCurvatureLevyDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circle probability measures, the existing negative-power Fourier moments, and the existing Toeplitz matrices.",
        H("LiCurvatureLevyDecomposition"),
        Blocks(
            Describe.Lean(DescribeId.Create("geometric-energy-at-identity"),
                DeclarationHandle.Create(Prefix + "geometric_energy_at_identity"), H("The identity contributes a quadratic term"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original finite geometric polynomial has energy n squared at the circle identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("geometric-energy-off-identity"),
                DeclarationHandle.Create(Prefix + "geometric_energy_off_identity"), H("The same energy is the compensated jump kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Away from the identity, derive the exact quotient from the finite geometric-sum identity and unit modulus. The denominator is proved nonzero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("li-jump-integrable"),
                DeclarationHandle.Create(Prefix + "li_jump_integrable"), H("Keep the cancellation inside the integral"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compensated jump expression is integrable for every finite source measure. Finite total mass of the singular jump weight is not assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reconstructed-li-levy-decomposition"),
                DeclarationHandle.Create(Prefix + "reconstructed_li_levy_decomposition"), H("Separate the identity atom and the jump contribution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact original energy contains its identity mass times n squared and the compensated positive jump expression. No probability-process existence theorem is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("identity-atom-energy-floor"),
                DeclarationHandle.Create(Prefix + "identity_atom_energy_floor"), H("Identity mass forces quadratic growth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative scale, the remaining jump contribution is nonnegative and the identity atom gives a quadratic lower bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("identity-atom-vanishes-of-subquadratic"),
                DeclarationHandle.Create(Prefix + "identity_atom_vanishes_of_subquadratic"), H("Subquadratic growth excludes the Cayley boundary atom"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive scale and a subquadratic limit force zero mass at the actual circle identity, which is absent from every finite real Cayley image."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-curvature-jump-representation"),
                DeclarationHandle.Create(Prefix + "normalized_curvature_jump_representation"), H("Construct the pure jump representation from curvature data"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All normalized curvature matrices, the original recurrence, positive first coefficient and subquadratic growth construct the same moment measure, exclude its identity atom, and represent each original coefficient by the compensated jump integral."))), DescribeRole.Theorem))));
}
