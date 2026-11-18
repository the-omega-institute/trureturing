using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class SlaterCutPhaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/SlaterCutPhase.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spatial cuts and fixed-occupation shuffle phases",
        H("Spatial cuts and fixed-occupation shuffle phases"),
        Blocks(
            Paragraph(Text("The sites have a linear order. The retained side is a set of sites and the traced side is its complement. An occupation label on either side specifies a finite set of occupied sites.")),
            Entry("Alternates", "Four alternating sites",
                "Read four strictly increasing sites. Membership in the retained side alternates at each step, starting on either side.",
                DescribeRole.Definition),
            Entry("not_alternates_iff", "One side is an interval",
                "The cut has no four alternating sites exactly when one side is order connected. A hole between two retained sites forces every traced site between those endpoints. A retained site between two such traced sites would complete an alternating quadruple.",
                DescribeRole.Theorem),
            Entry("crossCount", "Cross-inversion count",
                "For each occupied retained site the sum counts occupied traced sites to its left. These are exactly the pairs that cross when the retained sites are placed first.",
                DescribeRole.Definition),
            Entry("reduction_charpoly", "Characteristic polynomial of the signed marginal",
                "The amplitude matrix is supported on occupations of total size k. When the retained side is an interval, the sign depends only on the traced occupation and cancels in the marginal. When the traced side is an interval, the sign depends only on the retained occupation and gives a diagonal unitary conjugation. An empty side gives sign one. The two Gram matrices thus have identical characteristic polynomials, including all zero roots with multiplicity.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string name, string title, string explanation, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("slater-cut-phase-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);
}
