using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdDesubstitutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The characteristic word is reconstructed from its majority occurrence ranks.",
        H("Mechanical majority desubstitution"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-majority-desubstitution"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdDesubstitution.mechanical_majority_desubstitution"),
            H("Exact majority positions and physical block reconstruction"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every frequency alpha strictly between zero and one half, "
                + "the characteristic mechanical word has its majority letter "
                + "of rank k at k plus floor((k+1) alpha/(1-alpha)). "
                + "Its prefix before that letter is the concatenation of the "
                + "first k blocks read from the characteristic mechanical word "
                + "at the frequency ratio: false gives [false], and true gives "
                + "[false,true]. Inverting both endpoint floor crossings gives "
                + "the occurrence positions. Induction then reconstructs every "
                + "physical prefix from these variable-length blocks. Rational "
                + "frequencies and exact floor boundaries are included. This "
                + "supplier identifies the actual majority-index rotation; it "
                + "does not classify bispecial return vectors."))),
            DescribeRole.Theorem))));
}
