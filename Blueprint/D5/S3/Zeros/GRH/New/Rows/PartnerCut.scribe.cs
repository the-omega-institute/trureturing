using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class PartnerCutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partner Cut", H("Partner Cut"),
        Blocks(
            Paragraph(Text("Stabiliser subgroup, data on columns; on that subgroup the datum is a product.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/PartnerCut.columnDatum_mul_ite_eq"),
                H("columnDatum_mul_ite_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let F be invariant under left multiplication by H = rowStabilizer, z square. Then columnDatum at the columns e of z, times F(y) if FixesColsOff e z and 0 if not, equals χ(det z)F(z⁻¹y) for z ∈ H and 0 otherwise.")))))));
}
