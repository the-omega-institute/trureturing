using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalAllChargeBrstMultiplicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/OriginalAllChargeBrstMultiplicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal original critical BRST energy-sector quotients have an all-charge, all-integer-level and all-integer-ghost-degree multiplicity classification.",
        H("Original All-Charge BRST Multiplicities"),
        Blocks(
            Paragraph(Text("Fix the original lattice data and both inverse-Gram equations at critical rank twenty-six. Levels and ghost degrees range over all integers. For nonzero charge the actual real quadratic signature is rank minus two. This signature condition supplies the previously constructed frame; no independently supplied frame replaces its construction. The zero-charge branch does not require a positivity hypothesis.")),
            Describe.Lean(DescribeId.Create("literal-off-shell-contraction"),
                DeclarationHandle.Create(Prefix + "original_off_shell_zero"),
                H("Off-Shell Original Quotient Vanishes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("originalSectorEquiv compares the kernel and range quotient of the actual restricted energyOriginalQ with the literal OriginalBrstReassembly.Cohomology. The established original_off_shell_cycle_boundary uses the actual original Ward identity and the charge-energy projection of the inverse-energy-scaled antighost contraction. Transporting that precise boundary, rather than an ambient-image dimension, kills every off-shell class. The split inclusion of each integral ghost-degree quotient into the full quotient is injective, so full off-shell vanishing also kills every off-shell graded quotient."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-original-charge-multiplicities"),
                DeclarationHandle.Create(Prefix + "original_all_charge_multiplicities"),
                H("Complete Integral Multiplicity Formula"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On shell, nonzero charge has multiplicity p24(level) in ghost degrees one and two, zero in every other degree, and total dimension twice p24(level). This is the existing OriginalColoredBrstMultiplicity result together with the original constructed-frame vanishing theorem. Zero charge is on shell exactly at level one; its dimensions are one, twenty-six, twenty-six and one in degrees zero through three, and total fifty-four. Off shell every degree and the full quotient vanish. The new zero-charge quotient identification supplies the exceptional branch; none of the previous native dimensions or p24 suppliers is reproved."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("negative-integral-levels"),
                DeclarationHandle.Create(Prefix + "original_negative_level_multiplicities"),
                H("Negative Levels Are Included"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every negative integer level both the full and all graded multiplicities vanish. The colored partition supplier defines p24 to be zero at negative level. A zero-charge negative-level sector is off shell, since its mass-shell equation would force level one."))),
                DescribeRole.Theorem),
            Paragraph(Text("literalOriginalSummandEquiv identifies the exact sector quotient with the corresponding projection range in the literal ambient OriginalCohomology. original_ambient_representative verifies that this inclusion is the class of the unchanged original representative. The mass-shell equation is checked separately for each charge and integer level; the statement does not put all levels of a fixed charge on shell simultaneously. Finite multiplicities under the stated nonzero-charge signature hypothesis do not establish arbitrary-signature energy-fiber finiteness. No descent of an arbitrary nonrelative C0 form, all-charge positivity, denominator identity, Monster construction, complete string theory or AdS/CFT conclusion follows from these multiplicities.")))));
}
