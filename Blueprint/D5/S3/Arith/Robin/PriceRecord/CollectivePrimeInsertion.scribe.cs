using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class CollectivePrimeInsertionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/CollectivePrimeInsertion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Collective insertion barriers at the original Robin minimum.",
        H("Collective prime insertion"),
        Blocks(
            Paragraph(Text("For L>1 and an integer k>=1, define B(L,k,x)=L+k log x-L^((1+1/x)^k). Its root is above L and is unique on the full real domain x>1. The barrier is negative below its root and positive above it. For k=1 the formula is the existing insertionBarrier, with no change to its endpoint convention.")),
            Describe.Lean(
                DescribeId.Create("collective-insertion-root-exists-unique"),
                DeclarationHandle.Create(Prefix + "collective_insertion_root_exists_unique"),
                H("Unique all-k nonlinear root and exact signs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real L>1 and every natural k>=1 there exists beta>L with B(L,k,beta)=0. Every zero at x>1 equals beta; for every x>1, B(L,k,x)<0 if and only if x<beta, and 0<B(L,k,x) if and only if beta<x. Bernoulli's inequality and the strict exponential tangent give the negative value at L. A positive value occurs at exp(L^(2^k)); continuity and strict monotonicity give existence and the full sign characterization. This is a necessary-comparison construction and asserts no Robin or Riemann-hypothesis conclusion."))),
                DescribeRole.Theorem))));
}
