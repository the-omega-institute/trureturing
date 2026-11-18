using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSSpectralExtractionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite spectral extraction, full raw boundary transport and inverse canonicalization", H("Canonical-to-native finite spectral bridge"), Blocks(
            Def("A", "Reuse of the canonical core", "A(c) is exactly OpenBoundaryMPSTwoSiteMinimality.core at (c,0,0). The final two canonical boundary coordinates do not affect these matrices. There is no competing canonical core."),
            Def("L", "Reuse of the canonical left row", "L(c) is the same original left row (c0,1)."),
            Def("h", "Trace difference", "h=c4-c1."),
            Def("D", "Spectral discriminant", "D=h squared plus 4 c2 c3."),
            Def("t0", "First canonical offset", "t0=c1-c0 c2."),
            Def("t1", "Second canonical offset", "t1=1+c3-c0 c4."),
            Def("U", "Diagonal-product numerator", "U=h t0 t1-c2 t1 squared+c3 t0 squared."),
            Def("Admissible", "Exact algebraic exclusions", "For arbitrary five complex coordinates c and complex e, require e squared=D and c2 D U (U+D) nonzero. There is no polynomial-dependent restriction, dimension assumption or assumed gauge conclusion."),
            Def("lam", "First eigenvalue", "lambda=(h+e)/(2 c2)."),
            Def("mu", "Second eigenvalue", "mu=(h-e)/(2 c2). Both square-root branches are allowed."),
            Def("T", "Canonical spectral frame", "T=A0 times the matrix with rows (1,1) and (lambda,mu)."),
            Def("K", "Actual conjugated core", "K=T inverse A0 T. Its entries are named u,v,w,t in row order."),
            Def("u", "First conjugated entry", "u=K00, the recovered canonical scalar."),
            Def("v", "Second conjugated entry", "v=K01."),
            Def("w", "Third conjugated entry", "w=K10."),
            Def("t", "Fourth conjugated entry", "t=K11."),
            Def("gap", "Eigenvalue gap", "delta=-e/c2 equals mu-lambda."),
            Def("rho", "Diagonal gauge", "rho=Delta/(delta u v), with Delta=-c2."),
            Def("S", "Full gauge matrix", "S=T diag(1,rho)."),
            Def("z", "Native trial parameter", "z=Delta/(delta u squared)."),
            Def("offset", "Native first offset", "alpha=delta v w/Delta."),
            Def("sector", "Existing native sector", "Use precisely OpenBoundaryMPSInteriorRootRealization.Sector with lambda,mu,a=lambda-alpha. Native G,B and core remain the source of truth."),
            Def("nativeLeft", "Full left boundary", "l=L S."),
            Def("nativeRight", "Full right boundary", "For every natural N and arbitrary complex two-column R, r=u to the power N times S inverse R. This includes the entire raw core scalar."),
            Def("leftNormalizer", "Computed native row normalizer", "K_l has rows l G and l B G. It is computed from the native core and left boundary, not defined by the desired inverse."),
            Thm("spectral_frame", "Spectral frame and entry exclusions", "For every admissible c,e, detT=e, L T=(1,1), and M T=T diag(lambda,mu) for M=A1 A0 inverse. The actual K has detK=-c2, ut=c2 U/D and vw=c2(U+D)/D. Thus u,v,w,t and delta are all nonzero. The entry identities use the equation e squared=D, the exact canonical matrices and the actual inverse of T."),
            Thm("native_extraction", "Exact native core equivalence", "For every admissible c,e, detS and z are nonzero; the native delta is gap, native alpha is offset, native beta=delta u t/Delta, and delta alpha beta is nonzero. Since beta=mu-a and alpha=lambda-a, beta-alpha=delta. The extracted left row is (1,rho). For each binary symbol, A_i S=u S core_native,i. The same existing native sector is Regular if and only if 1+conjugate(lambda) mu is nonzero. The transfer cross factor is separate from distinct eigenvalues."),
            Thm("raw_amplitude", "Every length and arbitrary right boundary", "For every admissible c,e, every natural N including zero, and every original R, the entire raw length-N state with canonical A,L,R equals the native state with the existing sector and z and boundaries l=L S and r=u^N S inverse R. A conjugation MonoidHom and List.smul_prod transport every ordered word, then the actual boundary contraction cancels the gauge. No scalar or boundary component is omitted."),
            Thm("normalizer_inverse", "Measured normalizer and recovered scalar", "For every admissible c,e, the actual native K_l equals u inverse times S. Its actual inverse gives l K_l inverse=u L; the second entry is exactly u. This follows by multiplying the proved symbol identities by OpenBoundaryMPSTwoSiteMinimality.normalized_rows at (c,0,0), reusing the original canonical row theorem directly."),
            Thm("canonicalization_inverse", "Two cores and both boundaries return exactly", "For every admissible c,e, natural N and arbitrary original R, set J=K_l. For both symbols, u J core_native,i J inverse=A_i. The canonical left row u inverse l J inverse=L. The canonical right column u (u^N) inverse J r=R. Thus the same finite gauge has a proved inverse at the scalar recovered from the actual normalizer."),
            Def("witnessC", "Canonical five-complex witness", "c*=(0,0,1/2,0,1)."),
            Def("witnessSector", "Existing native sector", "The original native Sector is (lambda,mu,a)=(2,0,1)."),
            Def("witnessLeft", "Actual native left row", "l=(1,1)."),
            Def("witnessRight", "Actual native right column", "r=(1,I). Its complete column is retained."),
            Def("witnessCanonicalRight", "Length-dependent canonical right column", "R_N=2^N times (1,1+I), for every natural N."),
            Paragraph(Text("For every natural N, the existing native G is [[1,1],[1,-1]] and B=diag(2,0). The actual leftNormalizer is [[2,0],[2,2]], with inverse [[1/2,0],[-1/2,1/2]]. Thus l K_l inverse=(0,1/2), whose second entry is 1/2. Canonicalization at t_can=1/2 gives exactly both original canonical symbol matrices at c*, the original left row (0,1), and the full right column R_N. This is the numerical application of canonicalization_inverse to the same actual native data, with every length-dependent factor retained.")),
            Thm("fixed_witness_extraction", "Return to the very same native witness", "For every natural N, c*,e=1 is admissible, D=1, U=-1/2, U+D=1/2. T=[[1,0],[1,1]], K=[[1/2,1/2],[1/2,-1/2]], rho=1, sector=(2,0,1), z=1 and l=(1,1). With R_N extraction returns exactly r=(1,I). With raw R=(1,1+I), it returns exactly (1/2)^N times (1,I). The separate transfer cross factor 1+conjugate(lambda) mu is one."),
            Thm("fixed_witness_quotient_boundary", "Restore the canonical quotient scale", "For every natural N, the existing OpenBoundaryMPSQuotient.positiveBoundary at (c*,sigma=4^N,eta=1+I) equals R_N. The squared modulus of its first entry is 4^N and the ratio of its second to first entry is 1+I. The theorem also states and proves the exact full raw length-N state equality between this canonical positiveBoundary input and the original native G,B,l,r witness. It transports precisely the same native b, retaining the raw scalar."),
            Paragraph(Text("This supplier preserves the original Ma--Zhang C8 canonical core and left row, with their CC BY 4.0 attribution. It supplies an explicit inverse for a later nonvanishing or dominance argument. It proves no actual-image density, genericity, arbitrary-polynomial descent, realified field norm, positive-environment transport or full C9 result. C9 remains open and solved-open-problem KPI is zero. Static finite algebra adds no dynamics, energy, clock, physical inverse or thermodynamic claim.")))));

    private static DocumentBlock Def(string name, string title, string prose) => Item(name, title, prose, DescribeRole.Definition);
    private static DocumentBlock Thm(string name, string title, string prose) => Item(name, title, prose, DescribeRole.Theorem);
    private static DocumentBlock Item(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("spectral-extraction-" + (name == "U" ? "numerator-u" : name == "T" ? "frame-t" : name.ToLowerInvariant().Replace('_', '-'))),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
