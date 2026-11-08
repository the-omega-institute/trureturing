using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFullIOPentagonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite FullIO pentagon", H("Finite-target FullIO pentagon"), Blocks(
            Describe.Lean(
                DescribeId.Create("latticesectorfulliopentagon-fullio-pentagon"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagon.fullIO_pentagon"),
                H("Finite-target FullIO pentagon"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The five explicit reassociation vertices of the finite FullIO "
                        + "pentagon are compared through the existing universal incoming "
                        + "equivalences. The short path and the long path are equal as "
                        + "concrete linear equivalences for every lattice datum, inverse "
                        + "Gram matrix, four charges and finite target sector. This is an "
                        + "algebraic finite-target identity and does not assert analytic "
                        + "sewing, convergence, braiding or a physical realization."))),
                DescribeRole.Theorem))));
}
