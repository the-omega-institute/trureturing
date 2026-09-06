using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class GoldenRobustLawSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/WeylChronology/GoldenRobustLawSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The deterministic robust Ramsey fringe margin is exactly a total-variation margin for the canonical Bool readout law.",
        H("Golden Robust Law Separation"),
        Blocks(
            Paragraph(Text(
                "This file is a cross-library adapter. GoldenRobustCalibration owns the "
                    + "deterministic fringe margin, while BernoulliBiasPairDistance owns the "
                    + "generic exact total-variation identity. No new testing or "
                    + "concentration inequality is introduced.")),
            Describe.Lean(
                DescribeId.Create("robust-law"),
                DeclarationHandle.Create(Prefix + "robustChronologyLaw"),
                H("Canonical robust Bool law"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A robust plus-port probability p is encoded by the existing positiveBiasLaw at bias p-1/2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("probability-data"),
                DeclarationHandle.Create(Prefix + "robust_chronology_probability_data"),
                H("Unit-interval robust fringes are probability data"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the robust fringe lies between zero and one, the existing closed-range Bernoulli theorem supplies nonnegativity and unit mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-tv"),
                DeclarationHandle.Create(Prefix + "robust_law_total_variation"),
                H("Robust probability gap equals total variation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The one-shot total variation of two robust laws is exactly the absolute gap between their actual plus-port probabilities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("robust-tv-lower"),
                DeclarationHandle.Create(Prefix + "robust_total_variation_lower_bound"),
                H("Calibration margin lower-bounds total variation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Nominal fringe gap minus the two certified calibration budgets is a lower bound on the actual one-shot total variation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("robust-tv-positive"),
                DeclarationHandle.Create(Prefix + "robust_total_variation_pos_of_nominal_margin"),
                H("Positive nominal margin gives positive robust total variation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the nominal gap exceeds both calibration budgets, the two robust one-shot laws are quantitatively separated in total variation."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The next step can now stay inside the existing estimation lane: use the "
                    + "certified positive total-variation margin to bound affinity or testing "
                    + "risk before considering any new statistical theorem."))))));
}
