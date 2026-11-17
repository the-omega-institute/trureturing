using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetCompressionDocument : IScribeDocumentDefinition
{
    private static DocumentBlock D(string selector, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create("coset-compression-" + selector.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression." + selector),
        H(selector), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetCompression", H("Lattice coset compression"), Blocks(
            D("ambient", "For every native LatticeData D, external rank e, integral rectangular B and integral symmetric even-diagonal C, the ambient Gram matrix has blocks G,B,B transpose,C, with old coordinates first. Neither block is required to have positive rank. The native actualVertexAlgebra accepts this ambient without any positivity premise.", DescribeRole.Definition),
            D("liftCharge", "The ambient charge joins an arbitrary original integral charge n to an arbitrary external integral charge a, in that order.", DescribeRole.Definition),
            D("oldCharge", "Restriction of an arbitrary ambient charge to the old coordinates.", DescribeRole.Definition),
            D("externalCharge", "Restriction of an arbitrary ambient charge to the external coordinates.", DescribeRole.Definition),
            D("polynomialInjection", "Rename every original oscillator variable to its old ambient coordinate, preserving its nonnegative oscillator index.", DescribeRole.Definition),
            D("longitudinal", "The rational matrix inverseRat(D) times B; no integral inverse is assumed.", DescribeRole.Definition),
            D("projectionVariable", "Old oscillator variables are fixed. External variable (j,k) is replaced by the sum over old i of the complex cast of (HB)(i,j) times X(i,k).", DescribeRole.Definition),
            D("polynomialProjection", "The complex algebra homomorphism specified by projectionVariable, on all ambient oscillator polynomials.", DescribeRole.Definition),
            D("injection", "For any external charge a, J_a takes every original finite-charge state single(n,p) to single((n,a),rename_old(p)), extended complex linearly.", DescribeRole.Definition),
            D("projection", "For any external charge a, P_a selects exactly that external charge, restricts the remaining charge to the old block, and applies polynomialProjection to its complete oscillator polynomial.", DescribeRole.Definition),
            D("compressed", "For arbitrary external a,b, original state u and integer mode m, Z_ab(u,m) is the complex linear map P_(a+b) composed with the actual ambient mode Y_E(J_a u)[m] composed with J_b. These are the native all-state fields, with their original epsilon and half-diagonal term.", DescribeRole.Definition),
            D("schur", "For arbitrary external integral a,b, the rational scalar a transpose (C minus B transpose H B)b, in the displayed charge order.", DescribeRole.Definition),
            D("correction", "For arbitrary external a,b and natural j, the complex scalar (-1)^j times the rational binomial choose(schur(a,b),j).", DescribeRole.Definition),
            D("projection_weightedPartial", "For positive definite original D, arbitrary B,C as above, every old direction i, natural frequency r and every ambient polynomial p, applying the old Gram-weighted positive Heisenberg derivative and then polynomialProjection equals applying polynomialProjection and then the original Gram-weighted derivative. The equation G HB=B is derived using the existing inverseRat API; no ambient positivity is used.", DescribeRole.Theorem),
            D("projection_current_polynomial", "For positive definite original D, every old i, arbitrary ambient charge n, integer mode m and ambient polynomial p, projection of the original ambient current mode equals shiftedCurrentPolynomial on the projected p. The original charge is oldCharge(n), and its integral dual-pairing shift is B times externalCharge(n). This includes negative creation modes, the shifted zero mode and positive annihilation modes.", DescribeRole.Theorem),
            D("compressed_high_modes", "For every external a,b, arbitrary original u,v and integer q, there is a natural N such that Z_ab(u,q+j)v is zero whenever N is at most j. This is actual statewise truncation with no degree restriction on u or v.", DescribeRole.Theorem),
            D("correction_finite", "For all external a,b,c, arbitrary original u,v,w and integers p,q, the proposed correction summand (-1)^j choose(s(a,b),j) times Z_(a,b+c)(u,p-j)(Z_(b,c)(v,q+j)w) has finite support on natural j. The inner actual field supplies the cutoff.", DescribeRole.Theorem),
            Paragraph(Text("The field conventions and classical construction are those of Bakalov-Kac, math/0402315v1, section 4.1. The imported native normal products and residue constructions retain their Carnahan Apache-2.0 attribution. These definitions and truncation bounds supply the prerequisites and exact finite summand support used by LatticeCosetOperatorCorrection. Phase descent, analytic CFT and string-theory or AdS/CFT realization are outside these statements.")))));
}
