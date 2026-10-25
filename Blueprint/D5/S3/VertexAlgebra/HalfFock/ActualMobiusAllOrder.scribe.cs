using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;
internal sealed class ActualMobiusAllOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original corrected-field formal Mobius covariance",
        H("All orders in the formal parameter"), Blocks(
        Describe.Lean(DescribeId.Create("actual-mobius-all-order-coefficient"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.corrected_field_mobius_coefficient"),
            H("All-source original Mobius coefficient identity"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text("Let T be the original actual tensor mode L1, let Sj be the original source Sugawara mode j with inverse complex Gram matrix, and write A_e(a) for the coefficient of the original corrected field. For every natural n, signed integer e and arbitrary original source a, the sum over i from zero to n of (-1)^(n-i)/(i!(n-i)!) times T^i A_e(a) T^(n-i) equals the sum over the actual finite state energies h and k from zero to n of choose(2h+e/2-k-1,n-k)/k! times A_(e-2n+2k)(S1^k gradeProjection(h,a)). Endomorphisms act right to left. The integer determinant-unit hypothesis supplies the actual inverse; no positivity, primary-state, homogeneity, rank or target nilpotence assumption is present.")),
                Paragraph(Text("The source Virasoro relation gives [S0,S1]=-S1 and hence S0 S1^k a=(h-k)S1^k a for a source of energy h. The original infinitesimal L1 identity then gives the two adjacent descendant coefficients. With alpha=2h+e/2-1, c(n,k)=choose(alpha-k,n-k)/k! satisfies (n+1)c(n+1,k)=c(n,k-1)+(alpha-n-k)c(n,k), with out-of-range indices zero. Induction in n and the actual finite grade projections establish the stated all-source identity. At order two the mixed coefficient is alpha-1."))),
            DescribeRole.Theorem),
        Paragraph(Text("The coordinate is the normalized raw half-coordinate f_u(t)=t(1-u t^2)^(-1/2), whose unit factor has constant coefficient one. For a homogeneous source of signed energy h, the source action is exp(u(1-u t^2)S1)(1-u t^2)^(-2S0), with the right factor applied first. Thus its k-th descendant contribution is u^k/k! times (1-u t^2)^(k-2h) A(S1^k a)(f_u(t)). The original oscillator cutoff makes the source exponential finite on each source. This formula is interpreted order by order in u; it asserts no convergence or numeric target exponential.")),
        Paragraph(Text("The scope includes mixed source energies, signed charges, odd raw exponents, indefinite Gram forms and rank zero. Fixed formal orders are fields on the original actual tensor space: after application to x, their support is bounded below using finitely many original fields at T^j x. The formal parameter is independent of the raw half-coordinate. A global group action, analytic resummation and the full Monster, VOA, CFT, anomaly, fusion, string theory and AdS/CFT constructions require further mathematics.")),
        Paragraph(Text("The classical conventions are those of Frenkel, Lepowsky and Meurman and the original lattice-field suppliers. The binomial power series comes from Scott Carnahan's mathlib construction, with its Apache 2.0 attribution retained. The argument combines the original current, corrected-field, source Virasoro and energy decomposition results; it makes no claim of literature novelty.")))));
}
