using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMSharedLocalReadoutsPilotDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMSharedLocalReadoutsPilot.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full shared-readout acceptance for the original actual suffix",
        H("Full shared-readout acceptance for the original actual suffix"),
        Blocks(
            Paragraph(Text("The receipts check every original row/action/lower readout and every actual row of the 2497-context suffix. Sharing an equal local partial assignment removes repeated readout data, while every actual bound leaf still checks all 32 original projections and the same original numerical sum. The root retains its original nonempty depth-12 prefix. The resulting theorem forces a smaller bad event for a compatible bad completion; it supplies no universal score bound or unconditional triangle-locality refutation.")),
            Node("triangle-accepted", "triangle_accepted", "Check all 647 original triangle readouts", "Kernel evaluation verifies each complete transported assignment and original lower value."),
            Node("singleton-accepted", "singleton_accepted", "Check all 425 original singleton readouts", "Kernel evaluation verifies the entire singleton family independently."),
            Node("rows-accepted", "rows_accepted", "Check all 2497 actual rows", "Every bound leaf checks its sixteen triangle and sixteen singleton projections and original sum; every split checks all four complete child assignments and level descent; every symmetry cut checks strict original rank dominance."),
            Node("suffix-smaller-bad-event", "suffix_smaller_bad_event", "The original checked suffix forces a smaller bad event", "For any full event compatible with the actual prefix whose original score is below 6987435, annotated level descent reaches a sound bound or a score-preserving symmetry cut of strictly smaller event rank. The smaller event may leave the prefix domain, as the original global symmetry argument requires."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
