using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReciprocalGammaTuran;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/kalmykovkarp2013logconcavity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal Gamma series and coefficient positivity.",
        H("Coefficients and admissible sequences"), Blocks(
            Entry("reciprocal-gamma", "rgamma", "Reciprocal Gamma",
                "For every real x, rgamma(x) is the inverse of the real Gamma value. It is zero at every nonpositive integer.", DescribeRole.Definition),
            Entry("admissible-sequence", "AdmissibleSeq", "Admissible coefficient sequences",
                "A sequence g from the natural numbers to the reals is admissible when it is nonzero at some index, nonnegative at every index, satisfies g(n-1)g(n+1) at most g(n) squared for every n at least one, and has no internal zeros: if a<b<c and g(a) and g(c) are nonzero, then g(b) is nonzero.", DescribeRole.Definition),
            Entry("turan-coefficient", "turanCoeff", "The finite Cauchy coefficient",
                "For a real sequence g, real parameters mu, alpha and beta, and natural m, sum over k from zero to m the product g(k)g(m-k) times the difference rgamma(k+mu+alpha)rgamma(m-k+mu+beta) minus rgamma(k+mu)rgamma(m-k+mu+alpha+beta).", DescribeRole.Definition),
            Entry("coefficient-positivity-clause", "claim", "Universal coefficient positivity",
                "For every admissible sequence g and every real mu, alpha and beta with alpha and beta positive, mu at least minus one, and mu+alpha and mu+beta nonnegative, the Turanian coefficient is positive at every natural degree m.", DescribeRole.Definition),
            Entry("admissible-unit-sequence", "admissible_one", "The constant unit sequence",
                "The sequence with value one at every natural index satisfies all four admissibility conditions.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/ReciprocalGammaTuran/Defs." + name),
            H(title), StatementSource.WithoutFormula(), role == DescribeRole.Definition ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
