using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FejerRelativeLocalizationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FejerRelativeLocalization";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive triangular spectral representation bounds the relative far-time contribution of the Fejer moment.",
        H("Uniform finite-window localization of the Fejer moment"),
        Blocks(
            Paragraph(Text("For a finite family of real frequencies g and nonnegative weights w, fix a natural degree p and let F(t)=|S(t)|^(2p), where S is the weighted complex Fourier score. Given eta>0, let M be the whole-line integral of K_eta F, where K_eta is the angular Fejer kernel. For R with eta R>=1 write I(R) for the integral of K_eta F over [-R,R].")),
            Describe.Lean(DescribeId.Create("relative-truncation"), DeclarationHandle.Create(Owner + ".relative_fejer_truncation"),
                H("Relative tail bound"), StatementSource.FromAuthor(Bound()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The triangular Fourier identity has nonnegative occupation-pair coefficients. Increasing the resolution can only increase the triangular weight of every frequency difference, hence M_b<=M_eta whenever 0<b<=eta. For a radius T>=1/eta, set b=1/T. On [-T,T] the kernel K_b is at least 1/(8 pi T), so the integral of F on this interval is at most 8 pi T M. The quadratic Fejer kernel upper bound then bounds the increment I(2r)-I(r) by 32 M/(eta r) when r>=1/eta. Summing over the dyadic radii from R to 2^n R gives an error at most 64 M/(eta R) times 1-2^(-n). Integrability allows the upper radius to tend to infinity.")),
                    Paragraph(Text("With a moving finite spectrum, weights, degree and resolution, any radius R for which eta R tends to infinity makes the far-time error relatively negligible, including the cases of zero or repeated frequencies. Nonnegative occupation-pair coefficients are essential to the scale comparison. Arithmetic estimates on the intermediate time range between a central Gaussian window and the distant cutoff remain necessary for an absolute whole-line asymptotic."))), DescribeRole.Theorem))));

    private static Formula I(string x) => F.Id(x);
    private static Formula Div(Formula a, Formula b) => F.Seq(F.Frac, F.Grp(a), F.Grp(b));
    private static Formula Bound() => F.Disp(new Formula.Relation(Subtract(I("M"),Call("I",I("R"))),
        FormulaRelationOperator.LessThanOrEqual, Multiply(Div(F.D(6,4),Multiply(I("eta"),I("R"))),I("M"))));
}
