using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class GoldenBase4ResidueBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/GoldenBase4ResidueBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The residues of four-to-the-n modulo five and seven recover n modulo six, while prime-axis factorization sees only the exponent 2n on prime two.",
        H("Base-Four Residue Bridge"),
        Blocks(
            Describe.Lean(DescribeId.Create("phi4-residue-code"), DeclarationHandle.Create(Prefix + "powerResidueCode"), H("Power residue code"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The finite pair of mod-five and mod-seven power residues indexed by a residue class modulo six."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("phi4-residue-code-injective"), DeclarationHandle.Create(Prefix + "powerResidueCode_injective"), H("Six residue pairs are distinct"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact finite arithmetic separates all six exponent classes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phi4-mod5-period-six"), DeclarationHandle.Create(Prefix + "four_pow_mod_five_add_six"), H("Mod-five period divides six"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Adding six to the exponent leaves the mod-five residue unchanged."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phi4-mod7-period-six"), DeclarationHandle.Create(Prefix + "four_pow_mod_seven_add_six"), H("Mod-seven period divides six"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Adding six to the exponent leaves the mod-seven residue unchanged."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phi4-mod5-reduce-six"), DeclarationHandle.Create(Prefix + "four_pow_mod_five_reduce_six"), H("Reduce mod-five powers by exponent class"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The mod-five power equals the power at the exponent remainder modulo six."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phi4-mod7-reduce-six"), DeclarationHandle.Create(Prefix + "four_pow_mod_seven_reduce_six"), H("Reduce mod-seven powers by exponent class"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The mod-seven power equals the power at the exponent remainder modulo six."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phi4-power-residue-code"), DeclarationHandle.Create(Prefix + "power_residues_eq_code"), H("Actual residues equal the finite code"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The pair of actual power residues factors exactly through n modulo six."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phi4-mod-six-recovery"), DeclarationHandle.Create(Prefix + "mod_six_of_equal_power_residues"), H("Recover the exponent class"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Equal mod-five and mod-seven residues imply equal exponent remainders modulo six."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phi4-mod3-trivial"), DeclarationHandle.Create(Prefix + "four_pow_mod_three"), H("Modulo three is constant"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every base-four power is congruent to one modulo three, so this prime contributes no exponent-class distinction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phi4-prime-axis-exponent"), DeclarationHandle.Create(Prefix + "four_pow_eq_two_pow_even"), H("Prime-two axis exponent"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The factorization-side description is two to the exponent 2n. This is kept distinct from the Zeckendorf word of the integer four-to-the-n read by the DFAO."))), DescribeRole.Theorem)),
        []));
}
