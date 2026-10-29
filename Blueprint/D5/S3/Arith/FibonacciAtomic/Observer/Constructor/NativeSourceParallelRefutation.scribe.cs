using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeSourceParallelRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSourceParallelRefutation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parallel original source shifts have no common natural block ranks",
        H("A concrete obstruction in the original comparison graph"), Blocks(
            Describe.Lean(DescribeId.Create("parallel-source-input"),
                DeclarationHandle.Create(Prefix + "branchInput"), H("The original comparisons"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("branchInput is the literal BranchEquation list U=shift(3,V), U=shift(3,V), U=shift(4,V), with U=true and V=false. sourceTerms maps both names to the residual variable false, the common free shape required by these shifts. Thus the selected sort false has three indexed parallel edges, not two deduplicated constraints. Their two orientations retain weights 3,-3,3,-3,4,-4. This is the original source rank-consistency problem of Lemma 2.5, with a one-leaf ground shape and arbitrary natural ranks; neither a rank bound nor a potential is supplied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("parallel-source-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The feasibility assertion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The closed claim asserts that some natural valuation on every labelled occurrence and the singleton leaf carrier satisfies BlockSolution(branchInput,sourceTerms,false). The repeated source equations and their integer signs are unchanged."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("parallel-source-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The checker certifies impossibility"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The result is literally the negation of claim. Exact kernel computation gives checkSourceConsistency(branchInput,sourceTerms,false)=false after six signed-edge relaxation rounds. If the claimed natural ranks existed, selecting their singleton leaf would give an integer potential. NativePositivePotentialCover.zeroCycles_iff would then give zero weight on every original closed walk, and source_consistency_iff would force the same computed checker to accept, a contradiction. Thus the first instance uses both the actual computation and correctness theorem to solve its original natural rank problem. The result is a certified-instance refutation, not a positive finite instance or a new general theorem; it is the first concrete instance of the checker whose general live consumer remains source_sort_minimum_base. The computational rejection lies on its live derivation path. The source graph has the two-edge closed walk of weight 4-3=1; duplicate shift-three comparisons retain separate identities."))), DescribeRole.Theorem)
        )));
}
