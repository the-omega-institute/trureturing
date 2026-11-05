using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraPartitionCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraPartitionCount.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact partition by actual residual cores.", H("Exact partition by actual residual cores"),
        Blocks(
            Paragraph(Text("Fiber a b m n K is literally the actual residual/JointReduction/per-side-preserving subtype used in core_positive_vectors_inject. It retains every normalized integer function at the original dimensions. The core index records its two exact dimensions and its full normalized function; no quotient or representative replaces any original array.")),
            Describe.Lean(DescribeId.Create("miurapartitioncount-fiber"),
                DeclarationHandle.Create(Prefix + "Fiber"), H("The unchanged actual fixed-core fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Membership is precisely Residual a b g, JointReduction g to the complete K function, and equivalence of all-minima containment separately on each physical side of the original and reduced rectangles."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miurapartitioncount-unique"),
                DeclarationHandle.Create(Prefix + "residual_core_unique"), H("Distinct cores cannot share an actual array"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every a,b,m,n and every actual unit-edge integer height function h, if h reduces by arbitrary legal joint sequences to K and L in the existing Core a b family, then K=L. The existing joint_reduced_core_unique theorem gives equality of both dimensions and full functions. Injectivity of the finite dependent Core representation transports precisely that equality to the original Core indices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miurapartitioncount-equiv"),
                DeclarationHandle.Create(Prefix + "residualCoreEquiv"), H("An equivalence retaining every original array"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive a,b, total at least five, and both dimensions at least 2(a+b)-1, residualCoreEquiv sends each original residual array to its unique exact Core fiber. Its inverse forgets only the core index and retains the identical full function. Existence uses residual_core_exists, including its derived positive run counts; injectivity uses residual_core_unique. Consequently every original array is present exactly once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miurapartitioncount-sum"),
                DeclarationHandle.Create(Prefix + "residual_count_eq_sum_fibers"), H("The original count is the sum of actual fiber cardinalities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive natural a,b with a+b at least five and every m,n at least 2(a+b)-1, the unchanged residualCount a b m n equals the sum, over every K in the same finite Core a b, of Nat.card (Fiber a b m n K). The original count is converted to the cardinality of its actual residual subtype by the existing finite-set identity. The actual equivalence supplies cardinality equality, and pinned mathlib Nat.card_sigma computes the finite sum. Fiber finiteness follows by injection into the proved finite residual class.")),
                    Paragraph(Text("This equality counts actual fibers. Identification of those fibers with positive length vectors and the final polynomial identity are separate conclusions and are not hypotheses of this partition theorem."))), DescribeRole.Theorem))));
}
