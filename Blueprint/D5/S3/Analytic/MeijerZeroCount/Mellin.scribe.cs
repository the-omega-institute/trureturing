using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MeijerZeroCount;

internal sealed class MellinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Gamma quotient is the Mellin transform of a compactly supported Rodrigues kernel.",
        H("Residues and Mellin inversion"), Blocks(
            Entry("meijer-family-residues", "gammaQuot_family", "The finite residue expansion",
                "For natural n and d with d at least two, positive real c, and complex s with positive real part, take a=(n+c,n+c) and b=(c,2n+d+c). The Gamma quotient is the sum over k from zero through N=n+d-1 of A(k)/(s+c+n+k), where A(k)=(-1)^(n+k)(n+k)!/((k!)^2(N-k)!). Gamma recurrence gives the quotient of ascending factorial polynomials. Lagrange interpolation at the consecutive negative integers gives the residues."),
            Entry("meijer-rodrigues-mellin", "mellin_f", "The Mellin transform of the kernel",
                "For the same parameters and every complex s with positive real part, the Mellin transform of f(n,d,c) equals the Gamma quotient. On the unit interval the kernel is the finite sum of A(k) times x^(n+c+k), and outside it the kernel is zero. Each power term has Mellin transform one divided by s+c+n+k. The finite sum is integrable, and endpoint values do not affect the integral."),
            Entry("meijer-rodrigues-inversion", "meijerG_eq_f", "Identification by Mellin inversion",
                "For every natural n, every natural d at least two, every positive real c, and every x strictly between zero and one, Meijer's G for a=(n+c,n+c) and b=(c,2n+d+c) equals f(n,d,c,x). Along s=1+it the norm of the Gamma quotient is at most 1/(1+t^2): pair the n numerator factors with shifted denominator factors, and retain two additional denominator factors. This integrable bound, Mellin convergence, and continuity of the kernel at x discharge Mellin inversion along the line of real part one."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/MeijerZeroCount/Mellin." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
