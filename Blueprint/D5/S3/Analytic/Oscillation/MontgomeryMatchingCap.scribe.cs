using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomeryMatchingCapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/MontgomeryMatchingCap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint close-pair defects amplify into a strict Lorentz cap under a conditional row budget.",
        H("Disjoint close-pair defects and a strict Lorentz cap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-matching-defect"),
                DeclarationHandle.Create(Owner + ".finite_matching_defect"),
                H("Finite matching defect inequality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A finite collection of copies carries the inclusive closed radius-one neighborhoods. Two injective endpoint maps with disjoint row owners amplify the pair residual by the squared triangle inequality on the circle.")),
                    Paragraph(Text("The Lorentz weight is at least one half for both endpoint rows and every column in the first endpoint neighborhood. Summing nonnegative rows without duplication gives the ordered defect bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-normalized-cap-of-matching"),
                DeclarationHandle.Create(Owner + ".strict_normalized_cap_of_matching"),
                H("Multiplicity and normalized conditional cap"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The finite sigma type of multiplicity copies rewrites the ordered copy sum as the existing Montgomery pair sum through the inclusive cutoff.")),
                    Paragraph(Text("A lower bound on the number of disjoint pairs, a uniform phase residual, and a logarithmic neighborhood size produce a fixed normalized margin. The theorem remains conditional on the row budget and its normalized baseline, while the corresponding zeta gap hypotheses remain open."))),
                DescribeRole.Theorem))));
}
