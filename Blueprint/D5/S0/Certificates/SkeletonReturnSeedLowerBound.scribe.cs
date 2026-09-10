using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class SkeletonReturnSeedLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/SkeletonReturnSeedLowerBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reached disjoint regions with no incoming zero edge require distinct used return slots.",
        H("Return Seeds Forced by Actual Reachability"),
        Blocks(
            Describe.Lean(DescribeId.Create("return-seed-region-entry"),
                DeclarationHandle.Create(Prefix + "reached_region_has_used_return"),
                H("A reached zero-closed region has a used return entry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction in the original runTransition semantics shows that neither channel could enter the region if every selected return also avoided it. The conclusion supplies a selected slot, not an arbitrary unused allocation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("return-seed-zero-leaf"),
                DeclarationHandle.Create(Prefix + "zero_leaf_is_used_return"),
                H("Every reached zero-indegree state is a return target"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The singleton region of a noninitial state without zero predecessors satisfies the preceding entry theorem. This is the finite leaf obligation used in fixed-zero-map exhaustion."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("return-seed-disjoint-capacity"),
                DeclarationHandle.Create(Prefix + "disjoint_return_regions_bound_slots"),
                H("Disjoint reached regions consume distinct slots"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose one used return entering each region. Disjointness makes the selected slots injective, so their number is at most the original slot capacity. Full-carrier reachability in the numerical search must first be justified by exclusion of smaller reachable realizations. No arbitrary padded machine is assumed reachable."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Certificates/SkeletonSlotCNF"))]));
}
