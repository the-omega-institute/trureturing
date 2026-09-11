using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class SkeletonStateConjugacyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Automata/SkeletonStateConjugacy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit recurrent-state equivalences preserve partial evaluation and canonical cost, allowing verified zero-map witnesses to cover the finite search.",
        H("Recurrent-State Conjugacy of First-Return Skeletons"),
        Blocks(
            Describe.Lean(DescribeId.Create("skeleton-conjugacy-reindex"),
                DeclarationHandle.Create(Prefix + "reindex"), H("Reindex the recurrent carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The start, zero target and optional signature return are transported by one equivalence. Original output and partial-run semantics remain the owners."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("skeleton-conjugacy-eval-from-reindex"),
                DeclarationHandle.Create(Prefix + "evalFrom_reindex"), H("Transport every continuation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction on the original return blocks proves equality for arbitrary continuations, including unsuccessful partial runs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeleton-conjugacy-eval-reindex"),
                DeclarationHandle.Create(Prefix + "eval_reindex"), H("Preserve start-state evaluation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same original block code has exactly the same output after carrier renaming."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeleton-conjugacy-signature-map"),
                DeclarationHandle.Create(Prefix + "signatureMap"), H("Transport used signatures"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An old output-return signature maps to a used signature of the reindexed skeleton. Its return uses the same carrier equivalence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("skeleton-conjugacy-signature-map-injective"),
                DeclarationHandle.Create(Prefix + "signatureMap_injective"), H("No signature is identified"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applying the inverse equivalence to the return coordinate recovers the old signature."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeleton-conjugacy-signature-map-surjective"),
                DeclarationHandle.Create(Prefix + "signatureMap_surjective"), H("No new signature is introduced"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every new signature is witnessed by an original one transition at the inverse image of its source."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeleton-conjugacy-canonical-cost-reindex"),
                DeclarationHandle.Create(Prefix + "canonical_cost_reindex"), H("Preserve exact state cost"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The recurrent carriers and the actual used-signature carriers are bijective. Their sum, the existing canonical cost, is unchanged even with unused states."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeleton-conjugacy-zero-row-conjugacy"),
                DeclarationHandle.Create(Prefix + "zero_row_conjugacy"), H("Use the explicit zero-map witness"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An entry-by-entry conjugacy identity yields exactly the representative zero row on the reindexed candidate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeleton-conjugacy-initial-zero-loop-reindex"),
                DeclarationHandle.Create(Prefix + "initial_zero_loop_reindex"), H("Preserve the initial loop"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The designated initial zero self-loop survives the same transport. No ordinary self-loop is excluded."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeleton-conjugacy-covered-zero-maps-refute-samples"),
                DeclarationHandle.Create(Prefix + "covered_zero_maps_refute_samples"), H("Lift representative exclusions to all covered zero maps"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every cover entry is supported by a real state equivalence fixing the root. Evaluation and exact-cost transport construct the contradiction to its representative exclusion. Concrete cover validation and numerical representative refutations remain separate proof inputs."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Automata/BinaryZeckendorfBlockSkeleton"))]));
}
