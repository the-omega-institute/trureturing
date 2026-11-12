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
                Paragraph(Text("Under the negation, all positive repeated-pair gaps are at least delta. The equal-image pairs in the compact interval square with gap at least delta form a nonempty compact set. A minimum-gap pair exists and its gap is positive. Minimality makes the restriction to the half-open minimizing interval injective. Affine rescaling gives a path on [0,1] with equal endpoints, and AddCircle.liftIco_zero_continuous glues it to an actual continuous circle map. The equivalence with [0,1) and the proved injectivity of the rescaled restriction prove injectivity of the quotient map. This contradicts the stated absence of a circle injection."))), DescribeRole.Theorem))));
}
