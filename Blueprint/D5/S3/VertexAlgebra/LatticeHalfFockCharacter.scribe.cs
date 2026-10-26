using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockCharacter.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The character of the original half-Fock kernel grades is an absolutely convergent inserted trace series with an eta normalization and an even-rank S transformation.",
        H("Actual Half-Fock Analytic Character"), Blocks(
            Paragraph(Text("Let D be arbitrary integral symmetric even-diagonal lattice data and hu an invertible Gram determinant. The oscillator-first ActualTensor and ActualGround, the original actualInverse and tensorL zero-mode, and every ground endomorphism A are retained. At natural grade N, actualGrade is the kernel of tensorL0 minus (rank/16+N/2) times the identity. LatticeHalfFockGradedTrace supplies its finite basis and the restriction of TensorProduct.map id A, without an extra positivity, parity, preservation or module-law hypothesis.")),
            Node("actualTraceTerm", "Actual restricted trace terms",
                "For complex q and every N, the term is LinearMap.trace of actualGroundInsertRestrict on actualGrade(D,hu,N), multiplied by q^N. The definition contains the actual restricted operator. It is not defined from an Euler product or an eta quotient, and it never takes a trace on the infinite ambient tensor space.", DescribeRole.Definition),
            Node("actualInsertedCharacter", "The normalized inserted character",
                "The character at tau is exp(2*pi*I*tau*rank/48) times the sum of actualTraceTerm at q=exp(pi*I*tau). The shift is rank/16-rank/24=rank/48, and the odd oscillator grade N contributes N/2. The definition is meaningful as a complex tsum everywhere; the theorems assert its genuine convergence when Im(tau)>0.", DescribeRole.Definition),
            Node("actual_trace_series", "Coefficient identification and absolute convergence",
                "For every D, hu, A and complex q with norm(q)<1, every term equals partitionCount(rank,N)*trace(A)*q^N; the norms of all terms are summable; and their HasSum is trace(A)*oddCoefficientSeries(rank,q). The independently defined partition sum uses odd-part multichoose allocations. Its colouredMultiplicityEquiv and card_colouredFiber identify that count with the occupation fibre. The supplier's actual_grade_insert_trace_bRank computes the restricted trace, and AnalyticOddOccupation.summable_norm_odd_coefficients supplies the majorant. No duplicate counting or Euler proof is introduced. Rank zero, q=0, A=0, trace(A)=0 and arbitrary complex phases remain in scope.", DescribeRole.Theorem),
            Node("actual_character_modular", "Analytic eta and S character law",
                "For all D, hu, A and tau with Im(tau)>0, the vacuum-normalized actual trace terms are absolutely summable and have HasSum trace(A)*(eta(tau)/eta(tau/2))^rank. The trace-defined character equals that value. For every natural m with rank=2*m, its value at -1/tau is trace(A)*(2^m)^(-1)*(eta(tau)/eta(2*tau))^(2*m). These are ordinary complex sums, not formal power-series evaluation. EtaOddOccupation.normalized_odd_character_eq_eta and normalized_odd_character_S are consumed after the actual trace-series identification. The even-rank S law explicitly retains its rank equality and the doubled argument 2*tau. It uses the existing square identities and does not assert multiplicativity of principal square roots.", DescribeRole.Theorem),
            Paragraph(Text("The same theorem retains the actual groundRepresentation insertion: for every quotient element x with nonzero quotientCharge, if A is groundRepresentation(D,hu,x), every actual trace term vanishes, the normalized series has HasSum zero and the character is zero. This clause consumes the actual ground and grade trace-cancellation laws and the analytic HasSum proof, without a separate wrapper theorem.")),
            Paragraph(Text("The finite-support diagonalization and finite trace calculation come from the half-Fock supplier. The analytic count and eta reasoning reuse the repository occupation modules and Mathlib's DedekindEta and Discriminant results by Chris Birkbeck and David Loeffler under Apache 2.0. The construction is an analytic consequence for the specified half-Fock operator. It proves no Monster vacuum identification, canonical lift or parity projection, full twisted module or orbifold, fusion or anomaly law, physical CFT, complete string theory, spacetime reconstruction or AdS/CFT duality."))), []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("actual-half-fock-character-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
