using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ky Fan graph maxima and the asymptotic gap predicate.",
        H("Ky Fan gap definitions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ky-fan-sum"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/Defs.kyFan"),
                H("Ky Fan singular-value sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("For a real square matrix, sum the first k singular values, with the natural zero extension."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("xi-graph-maximum"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/Defs.xi"),
                H("Finite graph maximum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("The value xi k n is the maximum Ky Fan k sum over simple graphs on Fin n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ky-fan-gap-conjecture"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/Defs.conjecture"),
                H("Asymptotic gap predicate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("Infinitely many indices have a limiting normalized graph maximum below the universal square-root bound."))),
                DescribeRole.Definition))));
}
