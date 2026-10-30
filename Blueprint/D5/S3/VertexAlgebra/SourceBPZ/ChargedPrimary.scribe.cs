using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceBPZ;

internal sealed class ChargedPrimaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual charged-primary transpose for the original complex bilinear lattice pairing, on every finite-charge state.",
        H("Original Lattice Charged-Primary Transpose"),
        Blocks(
            Paragraph(Text("D is any LatticeGeneratingFieldLocality.LatticeData: its rank is natural, its Gram matrix is integral and symmetric, and each diagonal entry is even. Charge(D)=Fin D.rank -> Int, Oscillator(D)=MvPolynomial (Fin D.rank x Nat) Complex, and Carrier(D)=Charge(D) ->_0 Oscillator(D) are the literal original types. Rank zero, indefinite forms and degenerate forms are included. Neither positive definiteness nor an invertible Gram matrix is required.")),
            Paragraph(Text("B is exactly OriginalSourcePairing.sourcePairing D, the opposite-charge finite-support lift of the integer-frequency signed Wick form. It is complex bilinear. Y is exactly LatticeAllStateField.Y, and the charged state e_a is single a 1. The existing stateField_ground identifies Y(e_a) with the actual lattice exponential field. The existing actual_modes identifies standard mode m with raw coefficient -m-1.")),
            Paragraph(Text("The two-ground coefficient uses the actual creationCoeff, not a substitute Fock representation. Its oscillator constant coefficient is one at series index zero and zero at every other signed index: the positive-index vanishing follows from the existing weighted homogeneity, while negative indices vanish by definition. Opposite-charge support forces gamma=-(a+delta). The diagonal cocycle has epsilon(a,a)=paritySign(chargeEnergy(a)); multiplicativity and invariance under charge negation supply the required sign.")),
            Paragraph(Text("The raw reflection is k'=-k-bilinear(a,a). First, induction on the right oscillator polynomial proves the transpose with a ground state on the left. Moving a negative current through B and using the actual positive-current/raw commutator reduces this to the preceding polynomial and a shifted raw index. Positive currents annihilate every ground state. A second induction on the left oscillator polynomial uses the same exact all-integer commutator and the concrete current transpose, with the right state arbitrary. Finite-charge induction then gives the assertion for all u,v in Carrier(D). Every helper lies on this proof path.")),
            Describe.Lean(DescribeId.Create("original-source-charged-primary-transpose"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceBPZ/ChargedPrimary.sourcePairing_charged_primary"),
                H("All charged-primary modes on all original states"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D, charge a, integer m and u,v:Carrier(D), put q=chargeEnergy D a=bilinear D a a/2. Then B(Y(e_a)[[m]]u,v)=paritySign(q)*B(u,Y(e_a)[[2*q-m-2]]v). The equality 2*q=bilinear(a,a) fixes the exact reflected standard index. All charges, signed modes and finite-support vectors are quantified; no primary or BPZ law is assumed."))),
                DescribeRole.Theorem),
            Paragraph(Text("This is the concrete charged-primary supplier for further word-field or all-state BPZ arguments. It does not by itself establish full BPZ, Jacobi, fusion, crossing, anomaly cancellation, Monster moonshine, string theory or AdS/CFT. The construction applies classical invariant-bilinear-form mathematics with the repository's exact lattice conventions, without a novelty claim. Sources are Frenkel--Lepowsky--Meurman, Vertex Operator Algebras and the Monster, and Bakalov--Kac, math/0402315v1, section 4.1. Existing oscillator, current and polynomial suppliers retain their original attribution and licenses."))
        ), []));
}
