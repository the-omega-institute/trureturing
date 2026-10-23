using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient;

internal sealed class ActualLaurentCarriersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite homogeneous Laurent carriers",
        H("Actual finite homogeneous Laurent carriers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("slice-quotient-actual-laurent-carriers"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/ActualLaurentCarriers.actual_finite_laurent_carriers"),
                H("Actual finite homogeneous Laurent carriers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("The actual current and two physical source slices have three independent locality orders. Their weighted common cleared array has finite homogeneous coefficient slices. For every actual input tensor, linear functional, signed lifts and signed total degree, a finite Laurent polynomial represents that slice in every ordered Hahn expansion.")),
                    Paragraph(Text("The construction first supplies the actual common array and supported carriers. Homogeneous multiplication by each labelled difference shifts degree by one; division by the homogeneous clearing polynomial then identifies all ordered scalar coefficients. Negative degrees and zero slices are included. The resulting carriers supply the two actual local branches of the arbitrary-cutoff quotient theorem.")),
                    Paragraph(Text("Classical local-field provenance is Matsuo–Nagatomo and Bakalov–Kac (math/0402315). The source retains the mathlib Hahn/Laurent and partial-fraction authors and Scott Carnahan/vertexAlg composition attribution under Apache 2.0."))),
                DescribeRole.Theorem))));
}
