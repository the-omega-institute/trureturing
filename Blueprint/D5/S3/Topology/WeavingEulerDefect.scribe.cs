using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class WeavingEulerDefectDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Topology/WeavingEulerDefect.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual mixed-circle count equals uniform vertices plus selected crossings minus twice spanning rank.",
        H("Euler defect of arbitrary weaving states"), Blocks(
            Paragraph(Text("Let P have n at least two and m at least three, let p be either smoothing parity, and let S be an arbitrary crossing subset. Write v for the number of uniform circles, c(S) for the number of actual mixed circles, and q(S) for v minus the number of connected components of the spanning reference graph on S. Every uniform circle is a graph vertex, including isolated vertices. The empty, full and disconnected states and the cyclic seam all belong to the same finite family.")),
            Describe.Lean(DescribeId.Create("rank-insertion"),
                DeclarationHandle.Create(Module+"q_insert_add_one_iff"),
                H("The exact spanning rank increment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Adding one crossing increases rank by one exactly when its endpoints were in different old spanning components. The one-edge reachability classifier collapses precisely those two component classes, and preserves every other class. This proves the component-cardinality change directly on the full vertex quotient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("monotone-defect"),
                DeclarationHandle.Create(Module+"Delta_monotone"),
                H("Monotonicity of the Euler defect"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Define Delta(S)=v+|S|-2q(S)-c(S) in the integers. When rank increases, distinct reference components force distinct mixed circles and colored surgery merges them, so Delta is unchanged. When rank is unchanged, the universal surgery bound gives c(S union {z})-c(S) at most one, so Delta cannot decrease. Finite insertion induction yields monotonicity under arbitrary subset inclusion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("every-state-count"),
                DeclarationHandle.Create(Module+"mixed_circle_count_nat"),
                H("The circle identity for every state"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The empty defect is zero. For the full state, the reference graph is connected, full switching gives the complementary uniform smoothing, and the two uniform circle counts sum to nm+2. Its defect is therefore zero as well. Every subset lies between the empty and full subsets; monotonicity forces its defect to vanish. Consequently c(S)+2q(S)=v+|S|, without excluding zero-change switches in unrelated matching systems."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("state-exponent"),
                DeclarationHandle.Create(Module+"mixed_circle_exponent"),
                H("The nonnegative state exponent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The actual mixed quotient is nonempty. Thus v-1+|S|-2q(S)=c(S)-1 is nonnegative. This is the exponent needed to compare the graph state sum with the literal mixed-circle state sum."))), DescribeRole.Theorem),
            Paragraph(Text("These identities concern the actual combinatorial state quotients. Identification with the primary source's Jones invariant additionally requires the planar closure trace, the integral Hecke trace restriction, legitimate ring base change and the compatible localized square root. No such identity is an assumption here.")))));
}
