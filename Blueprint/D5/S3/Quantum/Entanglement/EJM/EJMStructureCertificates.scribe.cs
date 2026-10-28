using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMStructureCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMStructureCertificates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete structural premises of the actual EJM local bound DAGs.",
        H("Every actual row and every value branch is structurally checked"),
        Blocks(
            Paragraph(Text("The structural checks use the original partial-row interpreters and actual local actions. Every complete row must equal its stated completed event. Every split must cover every outcome value, point to an earlier row, inherit a valid lower bound and match the entire transported child assignment. These checks supply structural premises only. Exact centered-score inequalities at complete rows are earned separately before the generic complete/split assembly produces full checkRow acceptance.")),
            Describe.Lean(DescribeId.Create("triangle-structure"),
                DeclarationHandle.Create(Prefix + "triangle_structure"),
                H("All 41294 actual triangle rows pass the structural check"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Private kernel computations cover the entire triangle row domain, and the exported theorem dispatches to the corresponding checked chunk for every index. EJMLocalBoundAcceptance consumes this complete structural premise together with the independently earned terminal inequalities."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-structure"),
                DeclarationHandle.Create(Prefix + "singleton_structure"),
                H("All 8689 actual singleton rows pass the structural check"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same whole-domain structural check covers every singleton row. Complete-row score inequalities are supplied by the exact terminal and contraction receipts. Full local acceptance then supplies the actual-context cache lower bound."))),
                DescribeRole.Theorem))));
}
