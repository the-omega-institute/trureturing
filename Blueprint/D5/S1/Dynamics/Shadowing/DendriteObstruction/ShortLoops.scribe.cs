using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing.DendriteObstruction;

internal sealed class DendriteObstructionShortLoopsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/DendriteObstruction/ShortLoops.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrarily short repeated pairs in circle-free Hausdorff spaces.",
        H("DendriteObstruction - Short loops"), Blocks(
        Describe.Lean(DescribeId.Create("short-repeated-pair"), DeclarationHandle.Create(Owner + "short_repeated_pair"),
            H("Actual topological short loops"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let X be any Hausdorff topological space such that every continuous map from AddCircle (1 : Real) to X fails to be injective. If h : Real -> X is continuous on the closed unit interval and is not injective there, then for every delta > 0 there are a,b in that interval with a < b, b-a < delta and h(a)=h(b). No compactness or metric on X is assumed.")),
                Paragraph(Text("Under the negation, all positive repeated-pair gaps are at least delta. The equal-image pairs in the compact interval square with gap at least delta form a nonempty compact set. A minimum-gap pair exists and its gap is positive. Minimality makes the restriction to the half-open minimizing interval injective. Affine rescaling gives a path on [0,1] with equal endpoints, and AddCircle.liftIco_zero_continuous glues it to an actual continuous circle map. The equivalence with [0,1) and the proved injectivity of the rescaled restriction prove injectivity of the quotient map. This contradicts the stated absence of a circle injection."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("short-repeated-pair-finite-prefix"), DeclarationHandle.Create(Owner + "short_repeated_pair_finite_prefix"),
            H("Uniform smallness of the entire finite prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a metric X with the same no-circle condition, let f : X -> X be continuous and let phi : Real -> X be continuous on [0,1]. Fix q before choosing any loop. If t -> f^[q](phi(t)) is not injective on [0,1], every eta > 0 admits a < b in [0,1] with equal terminal images and with dist(f^[j](phi(s)), f^[j](phi(t))) < eta for every j <= q and every s,t in [a,b]. The parameterization need only be continuous, so this applies in particular to every homeomorphically parameterized arc.")),
                Paragraph(Text("Compact uniform continuity for the finite family j < q+1 supplies one positive parameter scale. The topological short-loop theorem is then applied to the terminal iterate. Every two parameters in the resulting closed subinterval are closer than that scale. This controls the entire source subinterval at all inclusive prefix times; no infinite-family uniform continuity is used."))), DescribeRole.Theorem))));
}
