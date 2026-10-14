using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMCacheStateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMCacheState.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local row states retain every original EJM block.",
        H("Local row states retain every original EJM block."),
        Blocks(
            Paragraph(Text("The cache stores sixteen actual triangle states and sixteen actual singleton states. Each state retains the original row index, its complete earned action, and all fields of the corresponding mirror row. This executable state representation alone proves neither global acceptance nor nonlocality.")),
            Describe.Lean(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"),
                H("All original root block states"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every block begins at its original root row and the identity action."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trianglestep"),
                DeclarationHandle.Create(Prefix + "triangleStep"),
                H("A complete earned triangle-state update"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The old earned action transports the original coordinate and outcome to the local row, then the checked proposed next action composes with it."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("singletonstep"),
                DeclarationHandle.Create(Prefix + "singletonStep"),
                H("A complete earned singleton-state update"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The singleton transition keeps the same full state and transport convention."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("step"),
                DeclarationHandle.Create(Prefix + "step"),
                H("Update exactly the affected original blocks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Original-block incidence determines which triangle and singleton states change; every unaffected state is retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lower"),
                DeclarationHandle.Create(Prefix + "lower"),
                H("The sum of all thirty-two original local lower fields"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The executable sum contains all sixteen triangle and all sixteen singleton contributions, with no row-completeness or producer premise."))), DescribeRole.Definition)))));
}
