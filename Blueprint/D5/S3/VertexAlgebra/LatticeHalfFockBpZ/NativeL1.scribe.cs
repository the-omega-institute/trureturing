using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class NativeL1Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original corrected native fields satisfy homogeneous BPZ transposition with the actual ordinary Sugawara one-mode.",
        H("Native BPZ and Ordinary Conformal Descendants"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("originalnativebpzhomogeneous"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/NativeL1.original_native_bpz_homogeneous"),
                H("Every Homogeneous Ordinary Source and Both Native Inputs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let u belong to the original lattice grade h, let e be any integer coefficient, and let v,w be any original NativeTensor states. Put L1=sugawaraMode(data,explicitLeechSpectrum.inverse,1) and K=oscillatorBound(data,u). Then tensorPairing(Ytw(u).coeff(e)(v),w) equals paritySign(h) times the sum over k from zero through K of inverse(k!) times tensorPairing(v,Ytw((L1^k)(u)).coeff(-e-4*h+2*k)(w)). The carrier, corrected field, complex-bilinear pairing and quadratic Sugawara operator retain their original definitions.")),
                    Paragraph(Text("On each fixed charge sector, the actual Sugawara-current commutator and the positive-mode charged-ground equation identify L1 with the derivation sending X(axis,0) to C(bilinear(unitCharge(axis),charge)) and X(axis,r+1) to (r+2) times X(axis,r). Both actual inverse-Gram equations are consumed. A polynomial flow for this derivation has coefficients (k!) inverse times the actual L1 powers; its product expansion retains independent positional choices and the zero-current endpoint.")),
                    Paragraph(Text("The original ground square gives groundReflection(charge)=paritySign(q) times the native identity, where N=bilinear(charge,charge) and q=N/2. For a word of oscillator weight S and a reflected selection of retained weight M, the lowering is k=S-M. The relation 2*q=N turns -2*N-e-2*S-2*M into -e-4*(q+S)+2*k. The ground phase combines with (-1)^S to give paritySign(q+S). Thus the unrestricted corrected-word reflection supplies precisely the ordinary L1 sum, with no additional power of two.")),
                    Paragraph(Text("For an arbitrary homogeneous source, the original finite charge-monomial coefficients have common total energy h. The actual oscillator support supremum supplies one common K, and the original Sugawara local-nilpotence theorem removes all larger powers. Linearity then combines the word identities on the original carrier. No cutoff, covariance, transpose, Jacobi or conformal-normalization law is assumed.")),
                    Paragraph(Text("The polynomial flow describes the ordinary source derivation. The native normal-order evaluation used in the corrected-word theorem remains a linear map. This algebraic BPZ identity does not assert twisted Jacobi, Moonshine gluing, fusion, string theory or an AdS/CFT correspondence."))),
                DescribeRole.Theorem))));
}
