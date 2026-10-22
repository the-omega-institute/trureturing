using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KilbasSaigo;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/boudabsasimon2021kilbassaigo");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hyperbolic bounds for the Kilbas-Saigo function on the negative half-line.",
        H("The two-sided estimate"), Blocks(
            Describe.Lean(DescribeId.Create("kilbas-saigo-conjecture-result"),
                DeclarationHandle.Create("D5/S3/Analytic/KilbasSaigo/Result.result"),
                H("The full parameter range"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real alpha,m,l,x with 0<alpha<=1, m>0, l>m-1/alpha and x>=0, E(alpha,m,l)(-x) is bounded below by 1/(1+Gamma(1+alpha(l-m)) x/Gamma(1+alpha(l-m+1))) and above by 1/(1+Gamma(1+alpha l) x/Gamma(1+alpha(1+l))). The defining series and its derivatives converge on the entire real line. Positive Gamma increment kernels establish the fractional range; affine differential equations establish alpha=1. Strict positivity, decreasingness and convexity give the two estimates."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("boudabsa-simon-2021-kilbas-saigo-hyperbolic-bounds"),
                    ResolutionKind.Proved)))));
}
