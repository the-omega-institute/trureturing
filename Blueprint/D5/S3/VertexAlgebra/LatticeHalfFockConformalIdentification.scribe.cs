using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockConformalIdentificationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual corrected original conformal state",
        H("Native all-state conformal identification"),
        Blocks(
            Paragraph(Text("The source is exactly LatticeActualConformalState.omega D H: the neutral single charge of one half times the finite matrix-weighted sum of X(i,0)X(j,0). The field is the original LatticeHalfFockAllStateField.Ytw, composed from actual Corr, normalPolynomial and shiftLinear. The target is the existing tensorStressField on the complete ActualTensor D hu. No alternate stress state, field assignment or compatibility axiom is introduced.")),
            Paragraph(Text("The occurrence multiset of single(i,0,1)+single(j,0,1) admits the two-entry word [(i,0),(j,0)] also when the colours coincide. correctionWord_matching and labelledRemainders retain its unique remaining occurrence. The neutral singleton term vanishes. The genuine pairPolynomial uses pairScalar(1,1)=1/8 and total source weight two. Applying optionEquivLeft and actual shiftCoefficients yields precisely shift zero with X(i,0)X(j,0), plus shift two with the constant G(i,j)/8. Shift two is multiplication by w^-4 in the double cover.")),
            Paragraph(Text("normalPolynomial_monomial_enumeration identifies the original quadratic polynomial with two physical normal insertions. normalInsertion_integer_modes supplies its pointwise finite support before coefficient comparison. For every integer e, the inner current coefficient at e+2j+3 vanishes unless e is even. For even e, put m=(-e-4)/2; its physical half-index is m-j-1. The original tensorPair_eq uses j<0 for creation, including j=-1. No cover normalMinusOne product or exponent-based split is substituted.")),
            Paragraph(Text("The actual tensorPair_finite and tensor_rawL_finsum suppliers identify the finite tensor normal sums with the original tensorRawL. For arbitrary H, the coefficient is tensorRawL_m on even exponents and zero on odd exponents, plus delta_(e,-4) times sum_(i,j) H(i,j)G(i,j)/16 times the native vector. This organizational lemma is consumed inside the retained equality, not claimed as an independent new endpoint.")),
            Describe.Lean(
                DescribeId.Create("half-fock-original-conformal-identification"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockConformalIdentification.Ytw_omega"),
                H("Actual Ytw of original omega equals the existing tensor stress field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Assume hu:IsUnit D.G.det and H*gramComplex D=1. The existing inverse_trace supplier contracts the actual symmetric integral Gram to rank; the second inverse equation is unnecessary for this equality. The resulting correction is exactly rank/16 at e=-4 and is zero elsewhere. For even e, m=0 is equivalent to e=-4, so the original L and stressCoeff give the coefficient identity. For odd e both operators vanish. Coefficient extensionality proves full field equality on every native finite oscillator tensor vector. Arbitrary rank, rank zero, repeated colours and nonorthonormal indefinite lattices remain in scope."))),
                DescribeRole.Theorem),
            Paragraph(Text("The Reg mirror gives the full dependent source telescope and an exact equivalence between this field equality and its all-integer, all-vector native paired readout law. It does not assert a completed four-slot Contract.Registration: variation, sensitivity and lawful enrolled-template evidence remain source-admission obligations. No sensitivity is manufactured from the identically zero difference readout.")),
            Paragraph(Text("Bakalov-Kac math/0402315v1 section 4.1 and Dong-Nagatomo math/9808088v1 section 3.2 supply the classical twisted correction and conformal context already acknowledged by the original suppliers. The finite normal-support architecture retains its existing Kytola Apache-2.0 attribution. This is a native constructor comparison, not a claim of literature novelty. Canonical owning Scribe emission depends on the separate technical release; source-only Scribe is not emitted material.")),
            Paragraph(Text("Twisted all-state Jacobi and translation, Monster realization, fusion, anomalies, full CFT, string theory, spacetime geometry and AdS/CFT remain open. This equality supplies only the precise native conformal interface.")))));
}
