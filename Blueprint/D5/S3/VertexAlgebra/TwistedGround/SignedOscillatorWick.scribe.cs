using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;
internal sealed class SignedOscillatorWickDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Bilinear Oscillator Wick Form", H("Signed Bilinear Oscillator Wick Form"), Blocks(
            Paragraph(Text("For every original integral symmetric even lattice D, define a complex bilinear factorial form F on the original MvPolynomial oscillator, using the existing occupation factorial weight. Its creation/derivative identity reuses FactorialFockMetric.mul_X_pderiv_pairing by conjugating polynomial coefficients once. No Hermitian metric or positive-definiteness premise is substituted.")),
            Paragraph(Text("At natural half-mode k use the signed matrix A_k=-(k+1/2)G. The existing OriginalCurrentMetric substitution and its inverse act on the same variables, at the same mode. W(p,q)=F(Phi(p),q). A polynomial generator chain rule and Leibniz extend the signed creation/lowering identities to arbitrary polynomials. Integer IsUnit D.G.det supplies the inverse matrix and both-sided nondegeneracy; no determinant or form symmetry is assumed as a new premise.")),
            Paragraph(Text("The actual half_annihilation_creation theorem gives the signed creation/translation transpose for every integer coefficient n, with negative indices literally zero. Expanding both input translation polynomials gives a finite double-support rectangle. Exchanging this rectangle sends c-d=e+N to d-c=-e-N, giving the same-charge coefficient reflection e to -e-2N. No infinite Hahn support is reversed and no vector-valued charged support is assumed finite.")),
            Paragraph(Text("Rank zero, empty supports, zero charges, zero vectors and indefinite lattices remain in the full quantified scope. This is classical algebraic Wick/Fock normalization with no literature novelty claim. The ground pairing and tensor charged adjoint are separate consumers. Ground symmetry, PCT, analytic completion, intertwining fields, Jacobi, fusion, Monster, string theory and AdS/CFT do not follow from this oscillator module.")),
            Paragraph(Text("Information-escape registration remains unfinished: the faithful compiled Reg mirrors currently report declared_unresolved. The source-reconstruction diagnostics and missing binding certificates are recorded at https://github.com/the-omega-institute/trureturing/issues/21134 under the repository linked-issue exception. Compilation does not assert a validated registration.")),
            Paragraph(Text("FactorialBilinear.P, FactorialBilinear.form and FactorialBilinear.monomial_left, together with modeMatrix and complex_det_unit, are available at this original owner for direct reuse by OriginalSourceCoevaluation. Their definitions and proof bodies are unchanged. The monomial formula is F(monomial alpha c,p)=weight(alpha)*c*p.coeff alpha; modeMatrix remains the negative half-frequency Gram matrix. The integer source consumer derives its retuning and actual inverse from these owners, without copying private proofs or adding a new inverse axiom.")),
            Describe.Lean(DescribeId.Create("wick"),
                DeclarationHandle.Create(Prefix + "wick"),
                H("wick"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Complex bilinear form W on the original Oscillator D, formed from the existing factorial weight and signed same-mode Gram substitution."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wick-creation"),
                DeclarationHandle.Create(Prefix + "wick_creation"),
                H("wick creation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Multiplication by X_(i,k) transposes to -(k+1/2) times the actual Gram-weighted annihilation map. This helper is consumed by the creation/translation proof."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("wick-lowering"),
                DeclarationHandle.Create(Prefix + "wick_lowering"),
                H("wick lowering"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The converse transpose direction follows from the polynomial substitution chain rule. It is consumed by oscillator symmetry and the charged transpose induction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("wick-nondegenerate"),
                DeclarationHandle.Create(Prefix + "wick_nondegenerate"),
                H("wick nondegenerate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Both separating directions are obtained from nonzero occupation factorials and the existing invertible substitution. Integer unimodularity is the only additional hypothesis; the tensor consumer uses both directions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("translated-coeff"),
                DeclarationHandle.Create(Prefix + "translatedCoeff"),
                H("translatedCoeff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Signed coefficients of the actual finite translation polynomial, equal to zero for negative indices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("creation-translation-adjoint"),
                DeclarationHandle.Create(Prefix + "creation_translation_adjoint"),
                H("creation translation adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The native half-creation coefficient transposes to the same-charge actual translation coefficient. The proof derives the lowering recurrence from the existing actual annihilation calculation and preserves all signed indices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("oscillator-coefficient-adjoint"),
                DeclarationHandle.Create(Prefix + "oscillator_coefficient_adjoint"),
                H("oscillator coefficient adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every integer exponent e and norm N=bilinear D a a, the native oscillator coefficient at e transposes to the same charge at -e-2N. A finite rectangle of the two translation supports supplies the index exchange. This is consumed by the actual tensor adjoint."))),
                DescribeRole.Theorem))));
}
