using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;
internal sealed class SpectralEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp countable spectral envelope, its exact constant and sufficient threshold.",
        H("Countable spectral envelope"), Blocks(
            Node("countable_budget_envelope", "Mass-preserving countable passage",
                "Retain the first n entries of a countable probability sequence and let T and R be the tail mass and squared mass. If R=0 then T=0. Otherwise choose a positive integer L with T^2/L <= R, and replace the tail by L equal entries T/L. The approximant has exactly unit mass and purity no greater than the original. The finite budget theorem applies. The second and third moments converge because T and R tend to zero, and the countable Newton identity passes the inequality to the limit. No mass is lost and no finite-rank minimizer is postulated for the countable problem."),
            Paragraph(Text("For every q in the full closed interval [1/3,3/8], put d=sqrt(6q-2) and x=(2+d)/6. Then 0<=d<=1/2, hence 1/3<=x<=5/12 and 1-2x>=0. The finite-support sequence x,x,1-2x,0,... is summable with unit mass. Its purity is 2x^2+(1-2x)^2=6x^2-4x+1=q, using d^2=6q-2. Its increasing-triple sum is x^2(1-2x)=E(q). This gives equality throughout the abstract interval, including both endpoints, without a separate named sharpness theorem.")),
            Node("third_lower_of_purity_le_three_eighths", "The uniform constant",
                "Combine the lower-purity branch with the decreasing envelope to obtain e3 >= 25/864 whenever q <= 3/8. The endpoint optimizer is (5/12,5/12,1/6), and the difference from 1/32 is exactly 1/432. No physical attainability of this optimizer is established."),
            Node("third_lower_of_purity_le_threshold", "The exact sufficient threshold",
                "The inequality q <= q_c=(17-5 sqrt(5))/16 implies e3 >= 1/32, including equality at the scalar threshold. Indeed q_c is in [1/3,3/8], sqrt(6q_c-2)=(3 sqrt(5)-5)/4, E(q_c)=1/32 and the repeated equality coordinate is (1+sqrt(5))/8. Below 1/3 the coarse branch already suffices; above it monotonicity applies. The threshold equality spectrum is abstract and has no established physical realization."),
            Paragraph(Text("These results are spectral consequences. Their application to a balanced Fock-two channel also requires the actual completed-space all-input purity estimate and an actual trace-class coefficient join. They do not assume those analytic statements, prove a universal physical e3 >= 1/32 theorem, or settle the entropy conjecture.")))));
    private static DocumentBlock Node(string name, string title, string text) => Describe.Lean(
        DescribeId.Create("spectral-envelope-" + name.Replace('_', '-')),
        DeclarationHandle.Create("D5/S3/Entropy/SpectralEnvelope." + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
