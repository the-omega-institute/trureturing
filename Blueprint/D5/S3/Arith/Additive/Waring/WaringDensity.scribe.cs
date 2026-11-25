using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Density of a sumset",
        H("Density of a sumset"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("density"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringDensity.add_density"),
                H("Density of a sumset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("If A and B contain zero and have rational lower density bounds α and β with β nonnegative, their sumset has lower bound α + β − αβ. Partitioning each initial segment at the elements of A accounts for the additional elements supplied by B."))),
                DescribeRole.Theorem)
        )));
}
