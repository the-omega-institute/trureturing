using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReciprocalGammaTuran;

internal sealed class SeriesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/kalmykovkarp2013logconcavity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formal reciprocal Gamma series and boundary Turanian coefficients.",
        H("The formal series and its coefficients"), Blocks(
            Entry("reciprocal-gamma-formal-series", "formalSeries", "Formal coefficient sequences",
                "For a real sequence g and real b, formalSeries(g,b) has coefficient g(n)rgamma(n+b) in every natural degree n.", DescribeRole.Definition),
            Entry("boundary-turan-series", "boundarySeries", "The boundary Turanian",
                "For every real t, the formal boundary series is formalSeries(1,0) squared minus formalSeries(1,-t) times formalSeries(1,t).", DescribeRole.Definition),
            Entry("boundary-turan-coefficient", "d", "Boundary coefficients",
                "For real t and natural m, d(t,m) is the degree m coefficient of the formal boundary series.", DescribeRole.Definition),
            Entry("reciprocal-gamma-cauchy-coefficient", "coeff_mul", "Exact formal Cauchy coefficients",
                "For every real sequence g, real mu, alpha and beta, and natural m, the coefficient of formalSeries(g,mu+alpha)formalSeries(g,mu+beta) minus formalSeries(g,mu)formalSeries(g,mu+alpha+beta) equals turanCoeff(g,mu,alpha,beta,m). The finite summation bounds justify replacing the natural difference m-k by its real value.", DescribeRole.Theorem),
            Entry("reciprocal-gamma-boundary-identification", "turanCoeff_one_boundary", "Boundary specialization",
                "For every real t and natural m, turanCoeff(1,-t,t,t,m) equals d(t,m).", DescribeRole.Theorem))));
    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/ReciprocalGammaTuran/Series." + name),
            H(title), StatementSource.WithoutFormula(), name == "formalSeries" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
