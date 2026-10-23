using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient;

internal sealed class SupportedReadoutsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supported complete nested residue readouts",
        H("Supported complete nested residue readouts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("slice-quotient-supported-readouts"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/SupportedReadouts.supportedNestedLeftReadout_eq"),
                H("Supported complete nested residue readouts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("The finite fractional product uses the lawful complete residue Calculus.Q. Its scalar readout is the signed forward-minus-reverse binomial residue, and full-field locality makes the complete outer residue sum equal to any sufficient cutoff.")),
                    Paragraph(Text("The two supported inner pair extractions are computed coefficient by coefficient in the Hahn carriers. Their nested left and right formulas preserve the spectator modes and the same total signed mode. The left and swapped current/second-source computations are used together in the actual two-branch supplier. A finite cutoff on the fractional product does not assert separate support of either ordered residue term.")),
                    Paragraph(Text("Classical local-field provenance is Matsuo–Nagatomo and Bakalov–Kac (math/0402315). The source retains the mathlib Hahn/Laurent and partial-fraction authors and Scott Carnahan/vertexAlg composition attribution under Apache 2.0."))),
                DescribeRole.Theorem))));
}
