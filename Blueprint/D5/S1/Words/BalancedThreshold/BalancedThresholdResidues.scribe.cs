using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdResiduesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The computed denominators preserve an infinite eight-state residue orbit.",
        H("Uniform denominator residues"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-denominator-residues"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdResidues.uniform_denominator_residues"),
            H("Residues at every convergent index N at least one"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The actual denominators of the computed frequency-ratio continued "
                + "fraction are integral. Modulo t, their residues in order of "
                + "N modulo eight are -1, 2, 1, 0, 1, -2, -1, 0. Modulo t+1, "
                + "odd indices have residue one and even indices residue zero. "
                + "Two-step induction carries the ordered denominator state through "
                + "the alternating tail coefficients. The eight transitions are "
                + "local to that induction. The initial pair involving denominator "
                + "zero is excluded from the periodic orbit. No coprimality or "
                + "primality of t is required."))),
            DescribeRole.Theorem))));
}
