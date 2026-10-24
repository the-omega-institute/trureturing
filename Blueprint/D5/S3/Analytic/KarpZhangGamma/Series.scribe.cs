using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangGamma;

internal sealed class SeriesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive transformation and the gamma-series half of Conjecture 5.2.",
        H("From the two-variable transform to the gamma series"), Blocks(
            Entry("karp-zhang-gamma-series-coefficient", "gammaCoeff", "Literal gamma-series coefficients",
                "For real t and natural n, gammaCoeff(t,n) is Real.Gamma(t+n) divided by the product of Real.Gamma(2t+n) and n factorial. The degree-n coefficient of the gamma series is y(n) times gammaCoeff(t,n), as defined before Conjecture 5.2 on page 12 of Karp and Zhang.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-series-scale", "scale", "Positive parameter factor",
                "For real t, scale(t) is Real.sqrt(Real.pi) times 2 to the real power 1-2t. It is positive for every real t. Its products obey scale(t+alpha)scale(t+beta)=scale(t)scale(t+alpha+beta), and scale(t+1)=scale(t)/4.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-positive-beta-transform", "positive_beta_transform", "The finite positive beta transformation",
                "For every natural n and positive real t, gammaCoeff(t,n) equals scale(t) times the sum over j=0,...,floor(n/2) of the reciprocal of (n-2j) factorial times j factorial times Real.Gamma(t+1/2+j) times 2 to the natural power n-2j times 16 to the natural power j. This is Lemma 6 in finite coefficient form. Strong induction in n is simultaneous in every positive t. Gamma duplication supplies degree zero, Gamma recurrence supplies degree one, and both sides obey the same two-step recurrence involving t+1. There is no convergence hypothesis.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-transform-coefficient", "transformCoeff", "The positive diagonal substitution",
                "For a real sequence y, real a and natural n, transformCoeff(y,a,n) is the sum over j=0,...,floor(n/2) of y(n) divided by (n-2j) factorial times j factorial times Real.Gamma(a+j) times 2 to the natural power n-2j times 16 to the natural power j. It is the degree-n coefficient obtained from H(a;z,w) by substituting z=x/2 and w=x squared/16. The relation r+2j=n ensures that only finitely many bidegrees contribute.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-series-identification", "series_identification", "Identification with the transformed series",
                "For every real sequence y, positive real t and natural n, y(n)gammaCoeff(t,n)=scale(t)transformCoeff(y,t+1/2,n). This coefficient identity proves the formal series identification with no restriction on growth, signs or log-concavity of y. It follows by multiplying positive_beta_transform by y(n).", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-series-delta", "gammaDelta", "Finite Cauchy coefficient of the gamma Turanian",
                "For a real sequence y, real mu,alpha,beta and natural n, gammaDelta(y,mu,alpha,beta,n) is the sum over k=0,...,n of y(k)gammaCoeff(mu+alpha,k)y(n-k)gammaCoeff(mu+beta,n-k) minus y(k)gammaCoeff(mu,k)y(n-k)gammaCoeff(mu+alpha+beta,n-k). This is the literal degree-n Cauchy coefficient of the gamma-series Turanian.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-half", "gamma_half", "Every coefficient of the gamma-series Turanian is nonnegative",
                "For every real sequence y satisfying D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave, every positive real mu, all nonnegative real alpha,beta and every natural n, gammaDelta(y,mu,alpha,beta,n) is nonnegative. The existing predicate includes nonnegativity and no internal zeros. No shift-integrality, convergence or growth assumption is added. Apply series_identification to the four factors, cancel their common positive scale product, and use the finite diagonal Cauchy identity. The remaining coefficient is the sum over m=0,...,floor(n/2) of Result.transformDelta(y,mu+1/2,alpha,beta,n-2m,m) divided by 2 to the natural power n-2m times 16 to the natural power m. Every summand is nonnegative by Result.two_variable_nonneg.", DescribeRole.Theorem),
            Paragraph(Text("The scalar recurrence for the diagonal transform is (n+2)T(a,n+2)=T(a,n+1)/2+T(a+1,n)/8. The literal gamma coefficient satisfies (n+2)gammaCoeff(t,n+2)=gammaCoeff(t,n+1)/2+gammaCoeff(t+1,n)/2. The factor scale(t+1)=scale(t)/4 aligns these recurrences. Finite fibers r+2j=n justify the Euler-degree identity and every reindexing. For products, the index map sends (k,i,j) to (i+j,i,k-2i), with inverse (m,i,r) maps to (r+2i,i,m-i). This identifies the coefficient of the substituted product with the positive weighted sum of its bivariate coefficients.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangGamma/Series." + name),
            H(title), StatementSource.WithoutFormula(),
            name == "gammaCoeff" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
