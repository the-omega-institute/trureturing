using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class ActualDuhamelDifferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/ActualDuhamelDifference.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two actual projected row-divergence heat paths satisfy a full-frequency difference bound.",
        H("Actual Duhamel Difference"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-duhamel-difference"),
                DeclarationHandle.Create(Prefix + "actual_duhamel_difference"),
                H("Full-frequency Duhamel difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix positive viscosity and a positive closed time interval. For four continuous weighted square-summable coefficient paths x,y,z,w over all integer-pair frequencies, assume nonnegative uniform bounds Mx, My, Mz, Mw and nonnegative bounds Dx, Dy for x-z and y-w. The theorem constructs continuous Hilbert-valued Duhamel paths Dxy and Dzw from the actual weighted tensor convolutions of x,y and z,w. Both start at zero and have their individual 32 Mx My sqrt(t/nu) and 32 Mz Mw sqrt(t/nu) bounds. Their coefficients are the interval Bochner integrals of the same positive-i projected row-divergence heat kernel, with the tensor row index i and derivative index j in their original orientation.")),
                    Paragraph(Text("On every time in the original closed interval, the norm of Dxy(t)-Dzw(t) is at most 32 (Dx My + Mz Dy) sqrt(t/nu). The proof forms the difference of the two actual tensor paths, clamps it to the closed interval, applies the full-lattice Bochner heat construction to that difference, and proves by coefficientwise interval-integral linearity that the resulting path is exactly Dxy-Dzw on the interval.")),
                    Paragraph(Text("This supplies a quantitative nonlinear comparison for the eventual mild-solution map. It does not assert real symmetry, an invariant divergence-free path space, a fixed point, unrestricted uniqueness, pressure, or smooth continuation."))),
                DescribeRole.Theorem))));
}
