using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicEventualSupportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicEventualSupport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive budget, the two-cosine squared-mass minimizer eventually has a closed front window and all nearest antipodal sites as its positive support.",
        H("Exact eventual support of the cyclic minimizer"),
        Blocks(
            Describe.Lean(DescribeId.Create("cyclic-eventual-exact-support"),
                DeclarationHandle.Create(Owner + ".cyclic_eventual_exact_support"),
                H("Eventual support for both parities and all activation levels"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a positive budget λ, set m = λ/(8π²), and take the integer-lattice activation data at m. " +
                        "The lattice weight at j is (t−j²)₊/Z. For all sufficiently large positive moduli q, " +
                        "a cyclic minimizer exists and both cosine moments equal 1−λ/q². The positive sites " +
                        "of every minimizer are exactly those with centered j² ≤ t and those attaining " +
                        "the smallest sampled first cosine. The cutoff applies to even and odd moduli.")),
                    Paragraph(Text(
                        "Take h = 2π/q and d = 0 or 1/2 on even or odd moduli respectively. " +
                        "Use rows (1, 1−c, (1−c²)/h²) on the front window and the one or two closest " +
                        "antipodal sites. The Gram matrix has an invertible limit because its rows at the " +
                        "center, a front neighbor, and a closest antipode span three dimensions. Its solve " +
                        "matches (1, 2mh², m), with limiting coefficients (t/Z, −(t−d²)/(2Z), −1/Z).")),
                    Paragraph(Text(
                        "The total antipodal weight divided by h² tends to μ = 3m/4. Positive limiting front weights " +
                        "stay positive. At t = N², the front variation has mass −μ and squared-index moment " +
                        "m₄/3 − d²μ, where m₄ is the fourth moment of the lattice law. Adding μ times the lattice law " +
                        "gives zero mass, positive squared-index moment, and quadratic leading coefficient 1/(3Z) " +
                        "in the squared index. The weighted pair identity gives a strictly positive value at N². " +
                        "The lattice law vanishes there, so this is also the sign of the original variation.")),
                    Paragraph(Text(
                        "The two first excluded cosine levels are −cos((d+1)h) and cos((N+1)h), with N the front radius. " +
                        "Their polynomial readings have strictly negative limits. Every excluded cosine lies between them, " +
                        "so convexity gives the strict sign throughout the complement. Exact moments and the squared-distance " +
                        "identity certify the positive part as the unique minimizer."))),
                DescribeRole.Theorem))));
}
