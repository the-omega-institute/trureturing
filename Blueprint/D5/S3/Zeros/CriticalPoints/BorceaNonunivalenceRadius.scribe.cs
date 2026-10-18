using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class BorceaNonunivalenceRadiusDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Zeros/khavinson2011borcea");
    private const string Locator = "arXiv:1010.5167v2, §5, Theorem 5.1 and Conjecture 4";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The polynomial z−z⁴ is injective on the closed disk of radius 5/8, "
        + "although its order-one root moment times sin(π/4) is strictly smaller than 5/8. "
        + "This refutes Conjecture 4's proposed nonunivalence radius.",
        H("A counterexample to the root-moment nonunivalence radius"),
        Blocks(
            Paragraph(Text("D. Khavinson, R. Pereira, M. Putinar, E. B. Saff and S. Shimorin, "
                + "Borcea's variance conjectures on the critical points of polynomials. " + Locator + ".")),
            Paragraph(Text("Theorem 5.1 (Alexander-Kakeya). If a polynomial F of degree n has no critical points in a closed disk of radius R, then it is univalent in the concentric disk of radius R sin(π/n).")),
            Paragraph(Text("Conjecture 4. If F is an nth degree polynomial with F(0) = 0, "
                + "then F is not univalent in any closed disk of radius larger than "
                + "σ_p(F) sin(π/n), p ≥ 1, centered at zero.")),
            Paragraph(Text("Of course, if the conjecture is true for p = 1, then it follows for all p ≥ 1. By the Alexander-Kakeya Theorem, the truth of this conjecture implies the truth of Conjecture 1 for the same value of p. It can be easily seen that the strongest case p = 1 of this conjecture is true for n = 2.")),
            Describe.Lean(
                DescribeId.Create("borcea-nonunivalence-root-moment"),
                DeclarationHandle.Create(Module + ".rootMoment"),
                H("The root moment about a center"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a polynomial F of degree n, the root moment about c is "
                    + "((1/n) times the sum of |z_j−c|^p)^(1/p), with all zeros counted "
                    + "with algebraic multiplicity. Real powers are used, including nonintegral p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("borcea-nonunivalence-sigma"),
                DeclarationHandle.Create(Module + ".sigma"),
                H("The minimum root moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The quantity σ_p(F) is the infimum of the root moment over "
                    + "all complex centers c. Every root moment is nonnegative, so this "
                    + "family is bounded below and its infimum is at most the moment at zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("borcea-nonunivalence-conjecture"),
                DeclarationHandle.Create(Module + ".conjecture"),
                H("Conjecture 4 as stated"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural n≥1, every complex polynomial F of degree n "
                    + "with F(0)=0, every real p≥1 and every real radius r strictly larger than "
                    + "σ_p(F) sin(π/n), the conjecture forbids injectivity on the closed disk "
                    + "centered at zero of radius r. Repeated roots are permitted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("borcea-nonunivalence-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Conjecture 4 is false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take F(z)=z−z⁴, n=4, p=1 and r=5/8. The roots are "
                        + "0, 1, ω and its conjugate, where ω=−1/2+i sqrt(3)/2. The three "
                        + "nonzero roots have norm one. Their order-one moment about zero "
                        + "is 3/4, so σ_1(F) sin(π/4) ≤ 3 sqrt(2)/8 < 5/8.")),
                    Paragraph(Text("For |z|,|w|≤5/8, the identity "
                        + "F(z)−F(w)=(z−w)(1−z³−z²w−zw²−w³) and the estimate "
                        + "|z³+z²w+zw²+w³|≤4(5/8)³=125/128<1 show that the second "
                        + "factor cannot vanish. Thus F is injective on the closed disk. "
                        + "This contradicts the conjecture at its stated strict radius threshold.")),
                    Paragraph(Text("The result refutes the proposed univalence route. "
                        + "Borcea's variance Conjecture 1 is unaffected. A correct sharp "
                        + "universal replacement radius remains undetermined here."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("khavinson-pereira-putinar-saff-shimorin-2011-nonunivalence-radius"),
                    ResolutionKind.Refuted)))));
}
