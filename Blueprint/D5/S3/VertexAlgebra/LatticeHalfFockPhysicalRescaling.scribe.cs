using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockPhysicalRescalingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical slices reconstruct the original native normal words",
        H("Physical slices reconstruct the original native normal words"),
        Blocks(
            Paragraph(Text("physicalSlice samples the original cover coefficient at twice the physical exponent minus the retained shift. physicalJet is the original jetScalar times tensorCurrent at every signed integer mode. Pointwise lower truncation follows from the existing current cutoff and the actual native field order, without a source or target occupation cutoff.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockphysicalrescaling-insertion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_normalInsertion"),
                H("The original negative-mode split is exactly the physical normal-product split"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The two original natural-offset sums are compared term by term with the actual normalMinusOne coefficients. The native jetShift retains its factor two times the frequency plus three; the physical convolution has the rest mode n minus m minus one. The resulting external cover shift is two times the frequency plus one, not plus three. There is no exponent-sign replacement of the original m less than zero split and no exchange of infinite sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockphysicalrescaling-word"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.normalWord_physical_reconstruction"),
                H("Every original normal word is the sum of two shifted physical lifts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("wordShift is the sum over the actual indices of two times the frequency plus one. Normal insertion induction identifies each parity slice with the nested physical normal word. Integer division and the complementary even and odd remainder cases then reconstruct every native coefficient, including all negative exponents. This is a coefficient identity of the original normalWord, not a replacement state-field definition."))),
                DescribeRole.Theorem),
            Paragraph(Text("The original charged monodromy is consumed by physicalCharge_parity_mode: twice the parity slice is exactly the coefficient of A_a plus the parity sign times A_minus_a. Reconstruction also works directly with the half-sized slices and does not assume an all-state involution. Full twisted Jacobi and the string/AdS bridge remain open. Compiled mathematical identities do not alone provide four-slot escape admission.")))));
}
