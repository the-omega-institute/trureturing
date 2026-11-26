using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class FillingTheoremDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Filling Theorem", H("Filling Theorem"),
        Blocks(
            Paragraph(Text("Translates of the columns fill the rows. For every subspace F of the rows, some level translate of the projected Poincaré series keeps, modulo F, ramified columns of dimension at least nearly ½(1 − dim F/dim rows) times that of all columns, so rows exist and few translates span almost all rows, which gives the basis for the Gram determinant. Spanning by Poincaré series and the link between least second moment and tight frames are known. Related work: Petersson, Über die Entwicklungskoeffizienten der automorphen Formen, 1932; Benedetto–Fickus, Finite normalized tight frames, 2003; Muić, Compactly supported Poincaré series and existence of cusp forms, 2010.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/FillingTheorem.finrank_rows_ne_zero"),
                H("finrank_rows_ne_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For admissible data D, the space of rows has nonzero finite dimension over ℂ.")))))));
}
