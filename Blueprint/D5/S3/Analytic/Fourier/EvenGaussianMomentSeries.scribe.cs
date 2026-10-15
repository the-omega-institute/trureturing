using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class EvenGaussianMomentSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian dominated even-moment cosine series.",
        H("Gaussian dominated even-moment cosine series"),
        Blocks(
            Paragraph(Text("A continuous real signed source p satisfies |p(x)| <= C exp(-x^2) on the whole real line. Its normalized even moment is a_k = integral x^(2k)p(x) dx / (2k)!. The source need not be positive or even.")),
            Describe.Lean(
                DescribeId.Create("gaussian-even-moment-series"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/EvenGaussianMomentSeries.gaussian_even_moment_series"),
                H("The entire even-moment series and its uniform tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(
                    Paragraph(Text("Define S_p(z) = integral p(x) cos(sqrt(z)*x) dx and b_k = (-1)^k a_k. The scalar formal series b has radius infinity and represents S_p on the whole complex plane. For every k, the normalized derivative S_p^(k)(0)/k! equals b_k, including k=0. This conclusion follows from the proved series rather than assuming that the principal square root is analytic at zero.")),
                    Paragraph(Text("For every R >= 0, the absolute coefficient sum sum |a_k|R^k is finite and bounded by M_C(R) = integral C exp(-x^2) cosh(sqrt(R)*|x|) dx. On the closed disk norm(z) <= R, the remainder after terms k < N is bounded by 2 M_C(2R) (1/2)^N. This is one explicit uniform tail budget with the original Gaussian constant and source, valid at R=0 and N=0 as well.")),
                    Paragraph(Text("Gaussian domination supplies an integrable majorant C exp(-x^2) cosh(norm(w)*|x|), expressed as the sum of two Gaussian exponential tilts. Dominated convergence for the cosine series justifies the exchange of series and integral. Applying the same series to |p| at w=i sqrt(R) proves absolute convergence separately; the norm integral inequality and integral monotonicity supply M_C. The coefficient budget at 2R then controls every term by M_C(2R) (1/2)^k, giving the uniform remainder.")),
                    Paragraph(Text("This is classical Fourier and moment analysis, as used for the theta source in Romik (1.11). The formal theorem applies to arbitrary signed Gaussian dominated sources. Evenness is needed in a later Fourier-to-cosine identity, and is not an assumption of this result. The alternating sign is essential when the even moments are subsequently interpreted in square coordinates.")),
                    Paragraph(Text("The result identifies coefficients of the cosine integral. It establishes neither real-rootedness of Jensen polynomials nor any original node/cofactor sign, and it does not prove the Riemann hypothesis."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Fourier/XiThetaTransform"))]));
}
