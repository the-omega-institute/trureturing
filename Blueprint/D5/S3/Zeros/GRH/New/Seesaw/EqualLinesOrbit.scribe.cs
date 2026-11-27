using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class EqualLinesOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal Lines Orbit", H("Equal Lines Orbit"),
        Blocks(
            Paragraph(Text("Lattice bases adapted to the flag, their diagonal lines, nearness and glue conditions. Lattices with equal adapted lines lie in one double coset, by integral Witt.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/EqualLinesOrbit.exists_mem_besselFin"),
                H("exists_mem_besselFin"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For E stably unramified (StablyUnram): if x, x′ have adapted bases whose string diagonal entries β_i, β′_i have equal valuations at all finite places whenever 2i < s, then x′kx⁻¹ lies in Grading.besselFin for some k in K_0.")))))));
}
