using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class RightStripZeroDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Density of actual zeta zeros in a fixed right strip",
        H("Density of actual zeta zeros in a fixed right strip"),
        Blocks(Describe.Lean(
            DescribeId.Create("right-strip-dyadic-count-power-saving"),
            DeclarationHandle.Create("D5/S3/Weil/RightStripZeroDensity.rightStripDyadicCount_power_saving"),
            H("Sublinear dyadic zero count by a power"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For each fixed real σ greater than one half, the multiplicity-weighted number of actual "
                + "zeta zeros with real part above σ and T < |Im ρ| ≤ 2T is bounded by D T^(1−η), with D ≥ "
                + "0 and η > 0 independent of T. The argument proves this quantitative conclusion by a "
                + "finite Möbius convolution, the actual zeta truncation mean square, and weighted disk "
                + "overlap."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("summable-right-strip-inverse-height"),
            DeclarationHandle.Create("D5/S3/Weil/RightStripZeroDensity.summable_rightStrip_inverse_height"),
            H("Reciprocal heights are summable with multiplicity"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The reciprocal absolute ordinates of the same zeros are summable with their analytic "
                + "multiplicities. This supplies the finite total support lengths for compact positive "
                + "filters built from the high zeros in a fixed right strip."))),
            DescribeRole.Theorem))));
}
