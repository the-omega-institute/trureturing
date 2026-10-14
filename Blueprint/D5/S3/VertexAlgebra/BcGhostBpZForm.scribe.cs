using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostBpZFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/BcGhostBpZForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full algebraic bc Fock pairing is constructed from its actual graded-reversed creator word and native top coefficient, with a derived nonconstant phase and all-integral ghost and stress transpose laws.",
        H("Operator-Derived Ghost BPZ Pairing"),
        Blocks(
            Paragraph(Text("The carrier is the unrestricted Fock = (Finset Nat) →₀ Complex. The increasing basisWord is the released creator-word reconstruction, and the product is the real noncommutative Module.End product of the reversed list of bpzSite operators. Its graded factor is (-1)^(card(S)(card(S)-1)/2). Even sites 2r transpose to (-1)^r b(r+2); odd sites 2r+1 transpose to (-1)^r c(r-1). The top vector is the actual c(-1)c(0)c(1)vacuum = -basis{1,3,5}, and topCoeff is minus the coefficient at that finite top set.")),
            Describe.Lean(
                DescribeId.Create("rho-involutive"),
                DeclarationHandle.Create(Prefix + "rho_involutive"),
                H("Finite site involution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The preserved site map exchanges each outside even/odd pair and reverses the three top sites. It uses no infinite complement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chi-involutive"),
                DeclarationHandle.Create(Prefix + "chi_involutive"),
                H("Finite paired occupation set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("chi(S) = rho(S minus Z) union (Z minus rho(S intersect Z)), with Z={1,3,5}. This preserved map is involutive on every finite occupation set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-coefficient"),
                DeclarationHandle.Create(Prefix + "rawBasis_coeff"),
                H("Actual ordered-word coefficient bridge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Signed insertion/deletion coefficient identities pull the native reversed word back from Z, one actual operator at a time. The resulting occupation is chi(S). eps(S) is defined by the genuine raw value on basis(chi(S)), not by an assumed kernel. For every right state y the raw coefficient equals eps(S) y(chi(S)). In particular S={0}, T={1,3,5,7} gives +1, not the constant-sign candidate value -1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonzero-phase"),
                DeclarationHandle.Create(Prefix + "eps_nonzero"),
                H("Derived nonzero phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Distinct creator sites make every coefficient pullback admissible. Its finite product of native signs is nonzero. Coefficient conjugation also fixes eps(S). This is standard bc mathematics, not a novelty or positivity claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-kernel"),
                DeclarationHandle.Create(Prefix + "BPZ_kernel"),
                H("Native finite phase kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite Finsupp extension defines bpz(x) as an actual operator and BPZ(x,y)=topCoeff(bpz(x)y). Its basis value is eps(S) if T=chi(S), otherwise zero. There is no finite occupation or mode cutoff and no record assuming an adjoint or invariant form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-degree"),
                DeclarationHandle.Create(Prefix + "BPZ_degree_selection"),
                H("All-integer ghost degree selection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The preserved degree(S)+degree(chi(S))=3 supplies selection on homogeneous states of arbitrary integer degrees. Mixed states remain genuine superpositions. Pi=parityPart(0)-parityPart(1) is the actual parity operator, not a single sign assigned to a mixed state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("b-transpose"),
                DeclarationHandle.Create(Prefix + "BPZ_b"),
                H("All-integral b transpose"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("BPZ(b(m)x,y)=(-1)^m BPZ(Pi(x),b(-m)y). The proof uses the actual raw creator insertion identity and native deletion coefficients. A parity-p homogeneous left state contributes (-1)^p."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("c-transpose"),
                DeclarationHandle.Create(Prefix + "BPZ_c"),
                H("All-integral c transpose"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("BPZ(c(n)x,y)=(-1)^(n-1) BPZ(Pi(x),c(-n)y), on the same full carrier and for every integral n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normal-pair"),
                DeclarationHandle.Create(Prefix + "BPZ_normalPair"),
                H("Exact normal-order correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The transpose of normalPair(p,q) is -(-1)^(p+q) times normalPair(-p,-q), minus BPZ(x,y) precisely when p is in {-1,0,1} and p+q=0. The scalar middle-mode term is retained, rather than discarded under normal ordering."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stress-transpose"),
                DeclarationHandle.Create(Prefix + "BPZ_stress"),
                H("Finite native stress transpose"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("BPZ(L(m)x,y)=(-1)^m BPZ(x,L(-m)y). Both actual L_interval_sum expressions use the common symmetric interval with radius max(cutoff(m,x),cutoff(-m,y))+2. Negation is a proved finite index bijection. Only the m=0 correction survives to the finite middle set, and its weighted -1+0+1 sum is exactly zero. No unbounded sum is reindexed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("derived-symmetry"),
                DeclarationHandle.Create(Prefix + "BPZ_symmetric"),
                H("Derived symmetry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Symmetry is derived from the actual ordered-word transpose laws, odd total paired parity, and genuine vacuum/top normalization. It is not inherited as an assumption from a constant-sign candidate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ghost-hermitian"),
                DeclarationHandle.Create(Prefix + "Hghost_hermitian"),
                H("Conjugate-left ghost form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Hghost(x,y)=BPZ(conjCoeffs(x),y), with no outer star. Hghost(a x,y)=star(a) Hghost(x,y), and Hghost(x,a y)=a Hghost(x,y). Its Hermitian symmetry follows from the derived BPZ symmetry and real native phase. No positive-definiteness or matter-form assertion follows."))),
                DescribeRole.Theorem),
            Paragraph(Text("Primitive b/c here carry physical integral indices. The released currentMode shifts vertex indices: currentMode(b,1)=b(0) and currentMode(c,-2)=c(0). These are physicalB0 and physicalC0; the primitive b(1) and c(-2) are not that zero-mode pair. On v=e_empty, u=e3, j=e1, k=-e13, z=-e15, w=-e135, the only nonzero ordered scalar pairings are v/w, w/v, u/z, z/u, j/k, k/j, all +1. B0 sends u to v, k to j, w to -z and kills the other three; C0 sends v to u, j to k, z to -w and kills the other three. These scalar values and homogeneous/scalar specializations are transient compiled exact checks, not extra bind-only theorem declarations. They provide no indexed matter delta, charged BPZ phase or orthonormal matter frame.")),
            Paragraph(Text("Original-Q transpose, charged matter/PCT mode transpose, quotient descent and the physical form remain open. A later individual A(n) calculation must retain the exact -(1/2)(-1)^parity n d0(n) BPZtotal(x,C0 y) correction, and cancel it only after the genuine finite symmetric Q sum. Linear lattice theta is not antilinear PCT. Relative C0 is an insertion/lift on actual restricted relative preimages, not a relative endomorphism or a form on arbitrary absolute representatives; ker(B0) isotropy, {Q,C0}=-(1/2)V0 and [B0,V0]=0 still need the genuine total-form interface. Real transverse pullback, isometry, radical, positivity, exceptional/zero-charge sectors and global physics are not claimed. The full moonshine/VOA/CFT/anomaly/fusion/string/AdS objective remains open.")) )));
}
