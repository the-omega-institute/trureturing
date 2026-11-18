using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.ExceptionCount;

internal sealed class ZetaTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithm of the omitted prime Euler factors has a power-decaying bound uniform over every fixed real zeta-parameter gap.",
        H("Uniform control of omitted Euler factors"),
        Blocks(
            Describe.Lean(DescribeId.Create("uniform-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/ZetaTail.uniform_tail"),
                H("A tail uniform over an unbounded parameter interval"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every delta>0 there is a nonnegative C such that, for every real kappa>=1+delta and P>=2, log(zeta(kappa))+sum_{p<=P}log(1-p^(-kappa)) is at most C*P^(-delta/2). The real part of the complex zeta value is used. The existing convergent Euler-log identity expresses the difference as the sum over omitted primes. Each summand is bounded by 2*p^(-kappa); splitting its decay into P^(-delta/2) times the summable weight p^(-(1+delta/2)) gives one constant independent of both kappa and P. The exponent loss preserves uniformity throughout the unbounded interval. This controls the extra Euler factor in the real-power Robin exception reduction."))), DescribeRole.Theorem))));
}
