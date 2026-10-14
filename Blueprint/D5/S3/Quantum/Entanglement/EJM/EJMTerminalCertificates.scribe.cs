using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMTerminalCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual complete-event and integer-comparison premises of the EJM local certificate.",
        H("Literal terminal events, transport witnesses and scaled inequalities"),
        Blocks(
            Paragraph(Text("Each numerical terminal check reads the actual complete event and proposed coordinate/outcome witness, checks exact transport to the referenced contraction representative, and verifies the required integer lower-bound comparison. The whole-domain tag checks identify every complete row with its literal terminal event, so a proof cannot silently replace a row's event. Correctness of the stored contraction integer remains a separate premise discharged by EJMContractionCertificates. Terminal-bound soundness combines these premises on the actual original centered score.")),
            Describe.Lean(DescribeId.Create("triangle-terminals"),
                DeclarationHandle.Create(Prefix + "triangle_terminals"),
                H("All 4588 triangle terminal checks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every literal triangle complete row passes its actual transport and scaled integer-comparison check. This is a premise of triangle_all_terminal_bounds, consumed together with all actual contraction receipts and the complete-row tag check."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-terminals"),
                DeclarationHandle.Create(Prefix + "singleton_terminals"),
                H("All 1192 singleton terminal checks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every literal singleton complete row passes its transport and integer comparison, retaining the singleton centered-score factor 64. The theorem covers the entire actual terminal domain without assuming an external minimum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-tags"),
                DeclarationHandle.Create(Prefix + "triangle_tags"),
                H("The terminal tag of every actual triangle row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All 41294 triangle row tags are checked. A complete row must have an index in the literal terminal domain and its actual event must equal the indexed terminal event; split rows supply no replacement terminal inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-tags"),
                DeclarationHandle.Create(Prefix + "singleton_tags"),
                H("The terminal tag of every actual singleton row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The corresponding check covers all 8689 singleton row tags, identifying every complete row's original event before its terminal inequality is transported into full local acceptance."))),
                DescribeRole.Theorem))));
}
