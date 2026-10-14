using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMSingletonCacheDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMSingletonCacheData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual singleton row mirrors retain every original assignment.",
        H("Actual singleton row mirrors retain every original assignment."),
        Blocks(
            Paragraph(Text("The 8689 mirror rows contain the complete original 9-coordinate assignment hash, exact scaled lower, and all proposed unknown-coordinate transition payloads. Every literal proposal requires the corresponding full kernel receipts; the data definitions imply no global bound.")),
            Describe.Lean(DescribeId.Create("mirror"),
                DeclarationHandle.Create(Prefix + "mirror"),
                H("The complete actual indexed mirror row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Lookup retains the original hash, exact scaled lower, slot map, and future transition payload."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("assignment"),
                DeclarationHandle.Create(Prefix + "assignment"),
                H("The full original partial assignment proposal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All base-five coordinates decode to known Fin 4 outcomes or unknown values."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lower"),
                DeclarationHandle.Create(Prefix + "lower"),
                H("The exact scaled lower proposal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer literal is checked against the original scaled lower."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transition"),
                DeclarationHandle.Create(Prefix + "transition"),
                H("A complete row and action transition proposal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each original row, local coordinate, and four-valued outcome selects its proposed next row and full earned action."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checkmirrorfields"),
                DeclarationHandle.Create(Prefix + "checkMirrorFields"),
                H("Check original hash and scaled lower once"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The generic kernel-proved bridge recovers equality of the entire assignment from the checked hash."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checkmirror"),
                DeclarationHandle.Create(Prefix + "checkMirror"),
                H("The full assignment-and-lower checker"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This predicate compares the complete original assignment function and its scaled lower."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checktransitions"),
                DeclarationHandle.Create(Prefix + "checkTransitions"),
                H("Exhaust every unknown coordinate and all four outcomes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each proposed next assignment must equal the earned action applied to the original updated full partial assignment."))), DescribeRole.Definition)))));
}
