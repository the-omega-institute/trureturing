using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;
internal sealed class SpectralEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp countable spectral envelope, its exact constant and sufficient threshold.",
        H("Countable spectral envelope"), Blocks(
            Node("countable_budget_envelope", "Mass-preserving countable passage",
                "Retain the first n entries of a countable probability sequence and let T and R be the tail mass and squared mass. If R=0 then T=0. Otherwise choose a positive integer L with T^2/L <= R, and replace the tail by L equal entries T/L. The approximant has exactly unit mass and purity no greater than the original. The finite budget theorem applies. The second and third moments converge because T and R tend to zero, and the countable Newton identity passes the inequality to the limit. No mass is lost and no finite-rank minimizer is postulated for the countable problem."),
            Node("envelope_sharp", "Abstract sharpness on the full interval",
                "For every q in [1/3,3/8], the sequence x,x,1-2x,0,... with x=(2+sqrt(6q-2))/6 is nonnegative and has unit mass, exact purity q, and third elementary moment E(q). This proves sharpness under the abstract moment constraints alone."),
            Node("third_lower_of_purity_le_three_eighths", "The uniform constant",
                "Combine the lower-purity branch with the decreasing envelope to obtain e3 >= 25/864 whenever q <= 3/8. The endpoint optimizer is (5/12,5/12,1/6), and the difference from 1/32 is exactly 1/432. No physical attainability of this optimizer is established."),
            Node("third_lower_of_purity_le_threshold", "The exact sufficient threshold",
                "The inequality q <= (17-5 sqrt(5))/16 implies e3 >= 1/32, including equality at the scalar threshold. Below 1/3 the coarse branch already suffices; above it, monotonicity and the exact threshold value apply."),
            Paragraph(Text("These results are spectral consequences. Their application to a balanced Fock-two channel also requires the actual completed-space all-input purity estimate and an actual trace-class coefficient join. They do not assume those analytic statements, prove a universal physical e3 >= 1/32 theorem, or settle the entropy conjecture.")))));
    private static DocumentBlock Node(string name, string title, string text) => Describe.Lean(
        DescribeId.Create("spectral-envelope-" + name.Replace('_', '-')),
        DeclarationHandle.Create("D5/S3/Entropy/SpectralEnvelope." + name),
        H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
