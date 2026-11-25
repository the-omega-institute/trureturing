using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzWeightedHessianOptimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The trace-norm quotient has an attained sharp maximum and a unique tangent.",
        H("Sharp weighted trace-norm quotient on the full two-flag fibre"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petz-weighted-hessian-maximum"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PetzWeightedHessianOptimum.weighted_hessian_maximum"),
                H("Attainment and uniqueness on the Hermitian fibre"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Give each matrix entry a positive real weight symmetric under " +
                        "transposition. Let m = l₀l₁/(l₀+l₁), where l₀ and l₁ are the two " +
                        "within-flag coherence weights. Assume nonnegative row weights β and " +
                        "bound each nonpartner entry weight by the arithmetic mean of the " +
                        "corresponding row weights.")),
                    Paragraph(Text(
                        "Let C, f and g be positive. In flag s require the margin " +
                        "8m + fₛ(f+g)/C − 2(β(0,s)+β(1,s)) to be nonnegative, with positive " +
                        "sum across the flags. Here f₀=f and f₁=g. The offset W consists of " +
                        "the two Hermitian coherences with values −f/2 and g/2.")),
                    Paragraph(Text(
                        "Over all Hermitian matrices Z with zero right partial trace, the " +
                        "quotient ‖Z+W‖₁²/(C+E(Z)/2) has maximum 16m+(f+g)²/C. Its unique " +
                        "optimizer has within-flag coherences −4Cm/(f+g) and 4Cm/(f+g), " +
                        "with all other entries zero.")),
                    Paragraph(Text(
                        "The weighted representative of an attaining trace test bounds the " +
                        "quotient by a scalar and matrix sum of squares. The sharp two-flag " +
                        "contraction bound forces either signed swap at equality. Both swaps " +
                        "give the same tangent, and the negative-positive swap gives the " +
                        "matching trace-norm test at that tangent."))),
                DescribeRole.Theorem))));
}
