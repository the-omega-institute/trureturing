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
                DescribeRole.Lemma))));
}
