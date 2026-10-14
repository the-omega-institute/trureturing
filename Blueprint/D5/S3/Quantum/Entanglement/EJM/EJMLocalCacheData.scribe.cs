using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMLocalCacheDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact local row data for the original EJM checker.",
        H("Exact local row data for the original EJM checker."),
        Blocks(
            Paragraph(Text("Literal rows and incidence tables are proposals. The raw mirror checker tests the original base-five assignment hash and the original integer lower after the unchanged scale factor. The proved bridge recovers the entire assignment and lower fields from those checks. Transition soundness and complete global acceptance are separate obligations.")),
            Describe.Lean(DescribeId.Create("checkrawmirror"),
                DeclarationHandle.Create(Prefix + "checkRawMirror"),
                H("Raw assignment-hash and scaled-lower equality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The checker compares both literal fields against the decoded original row, including both terminal and branch cases."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checked-raw-mirror-eq"),
                DeclarationHandle.Create(Prefix + "checked_raw_mirror_eq"),
                H("Raw equality preserves the complete original assignment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Acceptance entails equality of the full partial-event functions and of the exact scaled lower, for either original row constructor."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("readtransition"),
                DeclarationHandle.Create(Prefix + "readTransition"),
                H("All four local outcome transitions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected unknown-coordinate slot supplies the next original row index and the complete local coordinate and outcome action. Those proposals require complete transition receipts."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trianglecompose"),
                DeclarationHandle.Create(Prefix + "triangleCompose"),
                H("Exact triangle-action composition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The new coordinate and outcome actions compose with the existing earned action in their actual contravariant and covariant orders."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("singletoncompose"),
                DeclarationHandle.Create(Prefix + "singletonCompose"),
                H("Exact singleton-action composition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The singleton state uses the same complete action convention."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("triangleincidence"),
                DeclarationHandle.Create(Prefix + "triangleIncidence"),
                H("Incidence of each original coordinate in all triangle blocks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each original global coordinate has a proposed local incidence in each of the sixteen original triangle blocks."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("singletonincidence"),
                DeclarationHandle.Create(Prefix + "singletonIncidence"),
                H("Incidence in all singleton blocks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The incidence table retains every original singleton block and each local coordinate."))), DescribeRole.Definition)))));
}
