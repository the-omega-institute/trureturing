using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct balanced sequences attaining the odd-alphabet critical-exponent bound.",
        H("The remaining odd-alphabet case"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-odd-alphabet-result"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/BalancedThreshold.result"),
            H("Every odd alphabet of size at least thirteen attains the threshold"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every odd integer d at least thirteen, there is a balanced "
                + "sequence over Fin d using every letter whose critical exponent is "
                + "(d-1)/(d-2). Write d=2t+3. The explicit quadratic mechanical slope "
                + "has frequency ratio [0;t+2,t,overline(t-2,t+1)]. Colour minority "
                + "occurrences by a two-cycle and majority occurrences by the "
                + "interleaving of disjoint cycles of lengths t and t+1, with zero "
                + "phases. Balance follows from occurrence-rank rounding, and "
                + "infinite occurrence sets supply all colours. The attaining prefix "
                + "has length 2t+2 and period 2t+1. Bispecial projection classification, "
                + "continued-fraction return displacements, residue exclusions and "
                + "short-factor estimates bound every physical periodic window. "
                + "Taking the supremum gives the matching upper bound. The statement "
                + "is the remaining odd case of the conjecture of Dvorakova, "
                + "Opocenska, Pelantova and Shur, arXiv:2112.02854."))),
            DescribeRole.Theorem))));
}
