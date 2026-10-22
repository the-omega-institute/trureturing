using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class LogarithmBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/LogarithmBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Logarithmic bounds for Robin response comparisons and contact estimates.",
        H("Logarithmic bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-loglog-tangent"),
                DeclarationHandle.Create(Prefix + "loglog_tangent"),
                H("Strict tangent for the iterated logarithm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For distinct real x,y>1, log(log(y))-log(log(x))<(y-x)/(x*log(x)). "
                    + "The price function is g(x)=1/(x*log(x)). The inequality follows from "
                    + "the strict logarithm tangent on the outer logarithm and its weak form on the inner one."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("quadratic-logarithmic-tail"),
                DeclarationHandle.Create(Prefix + "neg_log_one_sub_le"),
                H("Quadratic bound for a logarithmic tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing")),
                Blocks(Paragraph(Text(
                    "For 0<=x<=1/2, -log(1-x)<=x+x^2. Monotonicity of "
                    + "log(1-x)+x+x^2 on that interval proves the estimate. For 0<=x<=1/4, "
                    + "the right side is at most 4*x/3, as used in the prefix-lcm tail bound."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("original-first-clock-buffer-log-size"),
                DeclarationHandle.Create(Prefix + "buffer_log_size"),
                H("Logarithms near an endpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real x>=256 and x-2<=z<=x+1, one has 5<log(z)<=x/20. "
                    + "The estimate controls original endpoint windows and gives the lower logarithm "
                    + "bound used for cumulative Mertens peaks at cutoffs at least 10000."))),
                DescribeRole.Lemma))));
}
