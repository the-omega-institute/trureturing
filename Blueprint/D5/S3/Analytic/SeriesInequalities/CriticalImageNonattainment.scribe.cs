using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class CriticalImageNonattainmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit target has infimal error A/2 on the closed finite-source image, without a nearest point.",
        H("Critical Image Nonattainment"),
        Blocks(Describe.Lean(
            DescribeId.Create("critical-image-nonattainment"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/SeriesInequalities/CriticalImageNonattainment.critical_image_nonattainment"),
            H("Exact distance without attainment"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let K be any real-like field, so the assertion holds for both real "
                    + "and complex arrays. Assume A>0, 0<rho<1 and A rho=(1-rho)^2, and put "
                    + "r=A/2. Write u for the scalar amplitude recurrence. WeightedArray(K) "
                    + "is lp at exponent infinity on pairs of natural numbers. Its coordinate "
                    + "at (n,k) represents rho^(n+k) times the original array entry; its norm "
                    + "is the full supremum over all pairs, including row zero.")),
                Paragraph(Text(
                    "There exist weighted arrays T,U and a sequence B of weighted arrays "
                    + "with the following properties. The unweighted target has first column "
                    + "T(n,0)=-A-r/rho^n and other columns T(n,k)=-u(k)/2 for k>=1. "
                    + "The theorem states these entries after multiplying by rho^(n+k). "
                    + "The target norm equals 3A/2. The array U is the actual weighted "
                    + "extension of the constant boundary -A.")),
                Paragraph(Text(
                    "The set actualImage(A,rho) consists of actual extensions of all "
                    + "K-valued boundaries a with norm(a(n))<=A for every n. The array U "
                    + "belongs to this set, norm(U-T)=r, and the infimum distance from T "
                    + "to the set equals r. For every V in this image, norm(V-T)<=r "
                    + "if and only if V=U. Thus U is its unique nearest output.")),
                Paragraph(Text(
                    "For every natural N, B(N) is the full actual extension of the boundary "
                    + "which is -A for n<N and zero for n>=N. It belongs to finiteSourceImage, "
                    + "the set of outputs of bounded boundaries with finite support. The exact "
                    + "infinite norm error is norm(B(N)-T)=r+A rho^N. These errors strictly "
                    + "decrease and converge to r. The coordinate (N,0) attains the upper "
                    + "bound; the proof bounds every other coordinate.")),
                Paragraph(Text(
                    "Let I0 be the norm closure of finiteSourceImage(A,rho). This set is "
                    + "nonempty and closed, its infimum distance from T equals r, and "
                    + "every V in I0 satisfies r<norm(V-T). Consequently the infimum is "
                    + "not attained. For every natural N>=1, define windowError(V,T,N) "
                    + "as the supremum of norm((V-T)(n,k)) over n+k<N. The value r is "
                    + "the least element of the set of these window errors as V ranges "
                    + "over I0; B(N) attains it.")),
                Paragraph(Text(
                    "The first-column inequality follows from re(a)>=-A and "
                    + "re(z)<=norm(z). Equality forces re(a)=-A, and the disk norm "
                    + "constraint forces a=-A even over the complex field. The negative "
                    + "boundary envelope bounds every nonfirst-column truncation error "
                    + "by r. Finally rho^k u(k)=A/(1+rho) times (1+rho^(2k+1)) keeps "
                    + "the weighted zeroth row of U away from zero. Every member of I0 "
                    + "has vanishing antidiagonal tails, so U is excluded from I0. "
                    + "The same first-column rigidity therefore rules out every minimizer."))),
            DescribeRole.Theorem))));
}
