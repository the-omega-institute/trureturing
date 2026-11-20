using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class VanishingGapSignTransferDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer.";

    private static DocumentBlock.Describe Theorem(string id, string name, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vanishing forward gaps let a mesh capture fixed positive excursions.",
        H("Sign transfer on meshes with vanishing gaps"),
        Blocks(
            Theorem("eventually-hit-interval", "eventually_hit_interval", "Eventual interval hitting",
                "If y tends to +∞ and its forward increments tend to zero, then for each ε>0 "
                + "and natural K there is a real T such that every t≥T has a sample y(k) in "
                + "[t,t+ε) with k≥K."),
            Theorem("arbitrarily-late-negative-samples", "arbitrarily_late_negative_samples",
                "Transfer positive excursions to negative samples",
                "Let F be uniformly continuous on ℝ. Suppose the real sequence y tends to +∞, its "
                + "forward increments tend to zero, and a(k)+F(y(k)) tends to zero. If c>0 and "
                + "every real T admits t≥T with F(t)≥3c, then every natural K admits k≥K with "
                + "a(k)<−c. Use the uniform continuity radius at tolerance c in the interval-hitting "
                + "theorem and take the sample far enough out that a(k)+F(y(k))<c."),
            Theorem("log-mesh-of-ratio-one", "log_mesh_of_ratio_one", "Logarithmic mesh from ratio one",
                "If the real sequence x tends to +∞ and x(k+1)/x(k) tends to one, then log(x(k)) "
                + "tends to +∞ and its forward increments tend to zero. Divergence gives eventual "
                + "positivity, so the increments eventually equal log of the successive ratio."))));
}
