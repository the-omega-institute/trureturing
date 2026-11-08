/* GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementActualMoments
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementActualMoments
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual threshold moments recovered from finite quotient detectors and GCD polarization. */

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattySquareDisplacementActualMomentsDocument
    : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bajnokbeatty2024cayleydiameteroriginal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite-group count-threshold moments and arithmetic covariance.",
        H("Rounding moments from finite cyclic quotient detectors"),
        Blocks(Describe.Lean(
            DescribeId.Create("square-displacement-actual-moments"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattySquareDisplacementActualMoments.actual_square_displacement_actual_moments"),
            H("One actual threshold family and its GCD covariance kernel"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("For the full family Params={p:Int | 5<=p and Odd p}, put q_k=2k+3. The theorem chooses one global family T(p,k) of actual square_return_pair crossings. At each p,k, writing tmin=((q_k+1)/2).toNat and tlate=((q_k*p+1)/2).toNat, it retains all five original clauses: tmin<T; Wq<Wa for tmin<=t<T; Wa<=Wq at T; Wa<Wq for every t>T; and T<=tlate. It retains both logarithmic brackets, ((q_k^2-1)*p)/(4*q_k*log(2))+1/(2*q_k)-1/(2*q_k*p)<T and T<=ceil(p*q_k/(4*log(2))). Uniqueness is among all original count crossings, without requiring a competing threshold to satisfy either analytic bracket.")),
                Paragraph(Text("Let D_p(k)=T(p,k)-p*q_k/(4*log(2)), and let avg_N be the finite sum over k<N divided by N. The conclusions are avg_N D_p -> 1/2 and avg_N D_p^2 -> 1/3 for every p. For every p,r, including p=r, let d=gcd(p,r). Then avg_N(D_p*D_r) -> 1/4+d^2/(12*p*r), and the empirical covariance avg_N(D_p*D_r)-(avg_N D_p)*(avg_N D_r) tends to d^2/(12*p*r). Parameters are signed integers with positive real casts supplied by their hypotheses. The diagonal gives the variance 1/12.")),
                Paragraph(Text("The connection is that increasingly fine finite cyclic quotient detectors recover continuous-looking rounding moments. The supplied full actual_square_displacement_threshold_distribution theorem gives the point frequencies of Y_(p,r)=r*T_p-p*T_r. Its closed integer mass is the finite rectangle law d*(V-U), where a=p/d, b=r/d, U ranges over 0,...,a-1 and V over 0,...,b-1. The public mass is converted directly to finite fiber cardinalities. The existing interval-fiber formula and positive GCD coordinates are exposed in the supplier and reused directly; its CRT and equidistribution argument is reused through the distribution theorem. Original crossing uniqueness identifies every pair-specific witness with the one global family, so all detectors and all moments concern the same actual thresholds.")),
                Paragraph(Text("The bracket has an essential normalization role. Pair detectors are unchanged under D_s(k) -> D_s(k)+s*c(k), and therefore do not by themselves determine marginal moments. The logarithmic bracket gives a global bound for each fixed D_s and eventually |D_s|<=1, with a cutoff allowed to depend on s. Consequently each fixed integer detector is globally bounded. The proof partitions its entire observed range and the reference rectangle into one finite integer set. It takes a finite sum of the point-frequency limits to obtain the first and second detector moments. There is no infinite summation of pointwise zero masses and no tail-moment assumption.")),
                Paragraph(Text("Fix a positive odd m and use the pair p,m*p. Its reduced rectangle has a=1,b=m, so Z_m=m*T_p-T_(m*p)=m*D_p-D_(m*p) has the limiting uniform finite law on 0,...,m-1. The normalized detector X_m=Z_m/m has mean limit (m-1)/(2*m) and second-moment limit (m-1)*(2*m-1)/(6*m^2). For this fixed m, eventually |D_p-X_m|<=1/m, |D_p|<=1, |X_m|<=1+1/m and |D_p^2-X_m^2|<=3/m. Each exceptional finite prefix contributes a constant divided by N. These bounds give limiting approximation errors at most 3/(2*m) for the first moment and 7/(2*m) for the second. Given an epsilon, one chooses an odd m sufficiently large first, and then chooses N sufficiently large for that fixed m's finite limits and cutoffs. This proves existence of the marginal limits themselves; it requires no uniform cutoff in m and no simultaneous choice m(N).")),
                Paragraph(Text("For arbitrary p,r, finite sums on the reference rectangle give mean(Y)=(r-p)/2 and second moment (2*p^2+2*r^2-3*p*r-d^2)/6. The algebraic variance of that finite reference law is (p^2+r^2-2*d^2)/12. Independence refers only to the finite uniform reference coordinates U,V used in evaluating the rectangle sum. No independence of the actual coupled errors D_p,D_r is assumed. The exact cancellation Y=r*D_p-p*D_r and the polarization identity 2*p*r*D_p*D_r=r^2*D_p^2+p^2*D_r^2-Y^2 then give the mixed moment. Subtracting the product of the proved empirical mean limits gives the arithmetic covariance kernel. No mixing property of the q-rotation, Gaussian model, spectral theorem or general probability framework is used.")),
                Paragraph(Text("Bajnok and Beatty supply the original quotient-group counting setting referenced by the library note. The exact count-crossing theorem, logarithmic bracket and determinant distribution are reused repository results, with the distribution packaging the full bracket theorem. The finite moment transport, odd-dilation convergence argument and polarization connect those inputs to the moment and covariance conclusions here. This attribution does not assert literature novelty. The Reg realization uses exactly the two actual count roles Wa,Wq, all states (k,t) in Nat x Nat, and the entire infinite parameter family. Its law contains the complete global-family theorem, and an explicit bridge transports every clause in both directions. Killing Wa contradicts the before-crossing inequality at tmin; killing Wq contradicts the after-crossing inequality at T+1. The public actual_counts values at p=5,q=3,t=2 and t=3 witness observational state dependence for both roles. Source selection and occurrence binding remain unfinished under https://github.com/the-omega-institute/trureturing/issues/25856 ."))),
            DescribeRole.Theorem))));
}
