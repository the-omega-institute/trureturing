using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ThreeColorSmallMixedCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ThreeColorSmallMixedCore.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reciprocal population inequality is at least two when three mixed color populations have total between two and five and satisfy the empty-side incidence constraints.",
        H("Small mixed-population certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("small-population-bound"),
                DeclarationHandle.Create(Prefix + "small_population_bound"),
                H("Bounded mixed-population inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let m(i) be three natural mixed populations and x(i,j) the six ordinary populations. Assume x(i,i)=0, the empty-side balance inequalities m(j)+x(j,i)≤m(i) whenever x(i,j)=0, and 2≤Σm≤5. Then the maximum of the attachment-charge and Cauchy expressions from ThreeColorIncidence is at least two.")),
                    Paragraph(Text("After sorting the mixed populations, each opposite-side ordinary pair is represented by a canonical thin or full choice. When at least one directed ordinary entry is absent, clearing the positive common denominator reduces the claim to coefficient nonnegativity; the kernel checks every sorted mixed triple with total 2, 3, 4, or 5 and every allowed choice. When all six entries are positive, elementary pair and color-loss estimates prove the attachment-charge expression is at least two. The ordinary variables remain unrestricted natural numbers."))),
                DescribeRole.Theorem)),
        []));
}
