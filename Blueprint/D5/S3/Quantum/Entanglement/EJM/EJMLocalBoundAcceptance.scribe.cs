using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMLocalBoundAcceptanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMLocalBoundAcceptance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete actual local-row acceptance on the path to the original EJM refutation.",
        H("Exact original scores, structural checks and all numerical premises meet"),
        Blocks(
            Paragraph(Text("Each local acceptance theorem applies the generic complete/split assembly to the actual row interpreter. Structural receipts cover every split branch and actual assignment. Exact contraction receipts, all terminal witness checks and all event-tag checks supply the original centered-score inequality of every complete row. None of these numerical acceptance families is assumed in the final local theorem. The accepted local rows are consumed by the actual-context cache lower-bound theorem. Acceptance of the complete global DAG and its positive score margin remains a separate obligation.")),
            Describe.Lean(DescribeId.Create("triangle-accepted"),
                DeclarationHandle.Create(Prefix + "triangle_accepted"),
                H("Every original triangle local row is fully accepted"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual checkRow for triangleCentered F1 and the original triangle partial action returns true at every one of the 41294 actual rows. Its structural and terminal premises are supplied by the complete original numerical receipt families, providing the full local premise used by the actual cache lower-bound theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-accepted"),
                DeclarationHandle.Create(Prefix + "singleton_accepted"),
                H("Every original singleton local row is fully accepted"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The corresponding original singletonCentered F2 check returns true at all 8689 actual rows, with its factor 64 and all exact event/transport conditions retained. Together with triangle acceptance, this supplies the original local row bounds consumed by the actual cache lower-bound theorem."))),
                DescribeRole.Theorem))));
}
