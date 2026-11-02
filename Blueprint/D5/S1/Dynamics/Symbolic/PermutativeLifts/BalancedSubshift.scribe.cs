using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BalancedSubshiftDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recognizable balanced factorial subshift.",
        H("Recognizable balanced factorial subshift"),
        Blocks(
            Describe.Lean(DescribeId.Create("refinement"), DeclarationHandle.Create(Owner + "refineBalancedTiling"),
                H("Actual physical refinement"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A marked level-(n+1) balanced tiling refines to a level-n tiling by the two actual runs of child words. Refinement retains the same physical integer coordinate, rather than replacing the point with a reindexed block sequence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("refinement-readout"), DeclarationHandle.Create(Owner + "read_refineBalancedTiling"),
                H("Refinement preserves the point"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reading the refined marked tiling gives exactly the original binary configuration at every integer coordinate. The proof reuses the generic two-run coordinate-read theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("recognizable-boundary"), DeclarationHandle.Create(Owner + "refineBalancedTiling_boundary_iff"),
                H("Recognizable parent boundaries"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the refined physical tiling, a parent boundary is exactly a child boundary where the preceding child has type true and the current child has type false. Both factorial runs are positive. This recovers boundaries from actual lower-level type transitions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("recognizability"), DeclarationHandle.Create(Owner + "balancedReadTiling_injective"),
                H("Unique marked presentation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At each level the readout map on actual marked balanced tilings is injective. The induction identifies the lower tilings, recovers the parent boundary sets, and uses equal positive lengths together with distinct upper words to recover every marked state. Equal heights are not used as a substitute for distinct words."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nested-images"), DeclarationHandle.Create(Owner + "balanced_subshift_succ_subset"),
                H("Nested visible subshifts"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every visible level-(n+1) balanced tiling reads a visible level-n tiling, using the actual refinement and its readout equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-space"), DeclarationHandle.Create(Owner + "balancedSubshift"),
                H("The actual compact intersection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The carrier is the intersection over all natural levels of the visible images of actual balanced marked tilings. It is closed and shift invariant. It is not a predicate assuming minimality, recurrence or aperiodicity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonempty"), DeclarationHandle.Create(Owner + "balanced_subshift_nonempty"),
                H("A nonempty compact space"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nested nonempty compact visible images have a point in their intersection. The associated BalancedPoint subtype has Nonempty and CompactSpace instances."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decoder"), DeclarationHandle.Create(Owner + "decode"),
                H("The unique compatible decoder"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The decoder selects a marked level-n presentation from actual intersection membership. Its readout is the original point, and recognizability makes the selected presentation unique."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("read-decoder"), DeclarationHandle.Create(Owner + "read_decode"),
                H("Exact decoder readout"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual BalancedPoint, reading its level-n decoder gives the same binary point at all integer coordinates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("continuous-decoder"), DeclarationHandle.Create(Owner + "continuous_decode"),
                H("Continuous tower coordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every level decoder is continuous. The readout is continuous from a compact marked-tiling space into the Hausdorff full shift, and injectivity identifies closed decoder preimages with preimages of compact readout images."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("shift-decoder"), DeclarationHandle.Create(Owner + "decode_shift"),
                H("Shift compatibility"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Decoding an integer shift is exactly the same as shifting the marked decoder. Both readouts agree and the readout map is injective."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nested-decoder"), DeclarationHandle.Create(Owner + "refine_decode"),
                H("Compatibility between levels"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Refining the level-(n+1) decoder gives the level-n decoder of the very same point. This equality follows from actual readouts and recognizability, without an extra compatibility assumption."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("aperiodicity"), DeclarationHandle.Create(Owner + "balanced_no_positive_period"),
                H("No positive global period"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every point in the actual intersection has no positive natural shift period. A hypothetical period p would preserve its unique sufficiently high marked tiling while moving a boundary strictly into a tile of length greater than p, contradicting the internal offset."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("infinite"), DeclarationHandle.Create(Owner + "balanced_nat_orbit_injective"),
                H("Infinitely many points"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nonnegative integer orbit of every point is injective, by cancellation of a common shift and the absence of positive periods. Nonemptiness then supplies the Infinite BalancedPoint instance. No claim about the older unequal-length factorial subshift is made. The public theorem escape registrations are unfinished under https://github.com/the-omega-institute/trureturing/issues/24726; the current scoped report verifies the Lean declarations and standard axiom closure, and does not constitute declared_validated four-slot audit evidence."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords")),
              DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling")),
              DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement")) ]));
}
