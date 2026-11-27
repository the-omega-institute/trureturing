using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class LatticeChartDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice Chart", H("Lattice Chart"),
        Blocks(
            Paragraph(Text("Continuity and norm formulas for the product Bessel function, kernel and amplitudes. H∩K read as congruence subgroup fixing the mark; class sums as finite sums.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/LatticeChart.isIntMatrix_scaleAt_sub_one"),
                H("isIntMatrix_scaleAt_sub_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let the finite idele p be a unit at w or w̄ for each w, and k integral unitary with row o congruent to that of 1 modulo pÔ. Then k − 1, with row o divided by p and column o by p̄, is integral.")))))));
}
