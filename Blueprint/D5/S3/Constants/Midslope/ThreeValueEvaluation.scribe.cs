using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Midslope;

internal sealed class ThreeValueEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic, geometric, and harmonic midslope-curvature integrals have exact values.",
        H("Three Midslope-Curvature Values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-midslope-curvature-values"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Midslope/ThreeValueEvaluation.three_value_evaluation"),
                H("The three elementary midslope values are exact"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("J"), Open, D(1), Close, Eq, Minus, Log, Sp, D(2), Sp, Land, Sp,
                    F.Id("J"), Open, D(0), Close, Eq, D(1), Minus, D(2), Sp, Log, Sp, D(2),
                    Sp, Land, Sp,
                    F.Id("J"), Open, Minus, D(1), Close, Eq, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The proof applies the frozen arithmetic, geometric, and harmonic "
                            + "integral evaluations directly, without repeating any integral "
                            + "calculation.")),
                    Paragraph(Text(
                        "The three conjuncts appear in parameter order 1, 0, and -1. No claim "
                            + "about any other parameter or about the full exact-value set is "
                            + "included."))),
                DescribeRole.Theorem))));
}
