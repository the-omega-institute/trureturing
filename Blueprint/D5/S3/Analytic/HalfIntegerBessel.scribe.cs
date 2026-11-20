using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class HalfIntegerBesselDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/HalfIntegerBessel.";
    private static readonly LibraryNoteRef Dlmf =
        LibraryNoteRef.Create("D5/L/Analytic/dlmf2010halfintbessel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite complex half-integer carriers and their Wronskians on the right half-plane.",
        H("Complex half-integer modified Bessel carriers"),
        Blocks(
            Node("prefactor", "Common prefactor",
                "The common prefactor is the positive real square root of pi/2 divided by "
                + "the principal complex square root of z.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Dlmf)),
            Node("K", "Decaying carrier",
                "At order m+1/2, K is the prefactor times exp(-z) times P_m(1/z), "
                + "where P_m is the rational factorial polynomial.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Dlmf)),
            Node("L", "Reflected carrier",
                "The growing carrier is the prefactor times exp(z) times P_m(-1/z).",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Dlmf)),
            Node("I", "Regular carrier",
                "The regular carrier I is the difference of L and (-1)^m K divided by pi.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Dlmf)),
            Node("hasDerivAt_K", "Derivative of the decaying carrier",
                "On Re z > 0 the derivative of K is its prefactor times exp(-z) times "
                + "the sum of -(1+1/(2z)) P_m(1/z) and -P_m'(1/z)/z^2.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("hasDerivAt_L", "Derivative of the reflected carrier",
                "On Re z > 0 the derivative of L is its prefactor times exp(z) times "
                + "the sum of (1-1/(2z)) Q_m(1/z) and -Q_m'(1/z)/z^2, "
                + "where Q_m(X) = P_m(-X).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("hasDerivAt_I", "Derivative of the regular carrier",
                "On Re z > 0 the derivative of I is (L' - (-1)^m K')/pi.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("wronskian_KL", "Wronskian of the finite reflected pair",
                "On Re z > 0, z(K L' - K' L) = pi. The square-root terms cancel "
                + "in the derivative difference. Evaluating the rational reflected Wronskian "
                + "at 1/z gives the factor 2, and the squared prefactor is pi/(2z).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("wronskian_KI", "Wronskian of the decaying and regular carriers",
                "On Re z > 0, K I' - K' I = 1/z. The multiple of K cancels and "
                + "the reflected Wronskian is divided by pi.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Dlmf)),
            Node("hasDerivAt_deriv_K", "Ordinary modified Bessel equation",
                "At order nu = m+1/2 and on Re z > 0, the derivative of K' is "
                + "(1+nu^2/z^2) K - K'/z. Differentiating the finite carrier twice "
                + "reduces the equation to the rational polynomial equation at 1/z.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Dlmf)))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("half-integer-bessel-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            provenance, Blocks(Paragraph(Text(prose))), role);
}
