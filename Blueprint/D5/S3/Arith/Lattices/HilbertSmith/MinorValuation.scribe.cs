using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.HilbertSmith;

internal sealed class MinorValuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/HilbertSmith/MinorValuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Cauchy product for a Hilbert minor has a valuation determined by residue populations.",
        H("Prime-power layers of Hilbert minors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cauchyminor-pos"),
                DeclarationHandle.Create(Prefix + "cauchyMinor_pos"),
                H("Positive Cauchy product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive scale, the Cauchy product for any two finite index sets is positive. Its "
                        + "numerator uses only positive differences and its denominator uses positive sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cauchyminor-valuation"),
                DeclarationHandle.Create(Prefix + "cauchyMinor_valuation"),
                H("Exact valuation by residue layers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonzero scale and row and column sets of size k within the length-n interval, count the ordinary "
                        + "row residues and the reflected column residues at each positive prime-power layer through the cutoff. Twice the "
                        + "valuation of the Cauchy product equals twice k times the scale valuation minus the "
                        + "logarithmic cutoff, with that difference taken before multiplication, plus the sum of "
                        + "the squared count differences. The cutoff is the base-p logarithm of 2n minus one, with "
                        + "the logarithm taken after subtraction. Doubling the valuation pairs the two orientations "
                        + "of every within-set difference so that the within-set and cross-set counts combine into "
                        + "squares."))),
                DescribeRole.Theorem))));
}
