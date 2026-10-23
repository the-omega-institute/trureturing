using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient;

internal sealed class WeightedExtractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted local extraction for the actual two branches",
        H("Weighted local extraction for the actual two branches"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("slice-quotient-weighted-extraction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/WeightedExtraction.actual_two_branch_supplier"),
                H("Weighted local extraction for the actual two branches"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("A finite Laurent numerator has a signed local collision formula with all weighted spectator poles retained. Shifting the numerator removes negative powers for partial-fraction decomposition; the origin contribution has zero collision jump, while each nonzero pole contributes its local residue.")),
                    Paragraph(Text("The resulting weighted fiber identity identifies complete current/source local residues in the supported triple carriers. Combining it with the actual homogeneous Laurent carrier supplier and native current inverse gives both the actual J/A branch and the swapped J/B branch for one numerator and all signed modes. These two branches feed the arbitrary-cutoff quotient comparison; no finite Taylor identification is asserted.")),
                    Paragraph(Text("Classical local-field provenance is Matsuo–Nagatomo and Bakalov–Kac (math/0402315). The source retains the mathlib Hahn/Laurent and partial-fraction authors and Scott Carnahan/vertexAlg composition attribution under Apache 2.0."))),
                DescribeRole.Theorem))));
}
