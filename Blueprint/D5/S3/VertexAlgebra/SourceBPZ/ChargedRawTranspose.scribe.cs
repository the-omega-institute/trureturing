using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceBPZ;

internal sealed class ChargedRawTransposeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The charged raw BPZ transpose derived by finite Wick induction on the original integer lattice carrier.",
        H("Original Charged Raw Transpose"),
        Blocks(
            Paragraph(Text("D is arbitrary symmetric integral LatticeData with even diagonal. Both states are arbitrary elements of the original finite-charge Carrier(D), and k ranges over all integers. No positivity, nondegeneracy, Gram inverse or desired adjointness hypothesis is used. The pairing is the complex bilinear OriginalSourcePairing.sourcePairing, with opposite charges and signed integer oscillator contractions.")),
            Paragraph(Text("The actual annihilation_creation recurrence and the integerWick creation/lowering transposes prove the creation/translation coefficient adjunction by terminating polynomial induction in the second oscillator slot, universally quantifying the first slot and the signed coefficient index. The constant case uses the existing weighted homogeneity of the actual creation exponential. Negative translation indices vanish exactly.")),
            Paragraph(Text("Applying this adjunction to each actual convolution term gives a double finite sum over the two translated-polynomial supports, restricted by c-d=s. Swapping the finite sums and using oscillator symmetry reflects s to -s. raw_single_convolution and the literal opposite-charge pairing then lift this identity to single charge sectors and finite-charge linearity. The existing integral_cocycle_square supplies the half-norm sign in the charge reflection.")),
            Describe.Lean(DescribeId.Create("charged-raw-transpose-source-pairing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceBPZ/ChargedRawTranspose.sourcePairing_rawCoeff"),
                H("Charged raw BPZ transpose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D, charge a, integer k and original-carrier states u,v, sourcePairing(D,rawCoeff(D,a,k)(u),v) equals paritySign(bilinear(D,a,a)/2) times sourcePairing(D,u,rawCoeff(D,a,-k-bilinear(D,a,a))(v))."))),
                DescribeRole.Theorem),
            Paragraph(Text("This is the standard lattice-VOA invariant bilinear form calculation, using the actual field formulas of Bakalov--Kac, arXiv math/0402315v1, section 4.1. The finite proof adapts the repository half-frequency SignedOscillatorWick creation/translation induction to the original integer suppliers; it asserts no literature novelty. Mathlib material retains its Apache-2.0 license and original authorship. All-state sourceFlow BPZ, mixed Jacobi, three-M, fusion, string theory and AdS/CFT remain further obligations."))
        ), []));
}
