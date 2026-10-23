using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class NativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite native kernels for both actual physical residue branches.",
        H("Supported Native Physical Rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-residue-supported-native-row"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/Native.chargedPhysicalResidueRow_native"),
                H("Each ordering has its own finite contraction expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("On every pure actual tensor p tensor g, the complete row with matching sector signs "
                    + "(-1)^gamma=projectedSign epsilon and (-1)^delta=projectedSign eta is the difference of two "
                    + "finite sums of nativeOrderedKernel and nativeReversedKernel. The four reflected charged "
                    + "components are expanded before regrouping with the two matching sector equations. All integer "
                    + "indices and both lifts remain signed; the second ordering swaps charges and coefficient exponents.")),
                    Paragraph(Text("For charges c,d and right exponent e, the contraction cutoff is "
                    + "(e+chargeNorm D d+sup{t(1):t in support(pairTranslation D c d p)}+1).toNat. "
                    + "Each occurrence uses its own e and pair-translated polynomial. The outer forward range comes "
                    + "from the order of B(p tensor g); the outer reverse range comes from the order of A(p tensor g). "
                    + "Common-kernel exchange and actual ground-action exchange put the reverse sum in the same "
                    + "orientation, with its exact paritySign(bilinear sigma tau) factor. The chargeScalar factors remain exact.")),
                    Paragraph(Text("This finite kernel formula does not identify these sums with the binomial transform "
                    + "of collision coefficients. That change of variables is a further mathematical obligation."))),
                DescribeRole.Theorem))));
}
