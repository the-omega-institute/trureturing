using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class TangZhangRealOrderCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/CriticalPoints/TangZhangRealOrderCounterexample.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct positive roots refute the proposed universal equality characterization at real order one.",
        H("The endpoint equality counterexample"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tang-zhang-order-one-counterexample"),
                DeclarationHandle.Create(Prefix + "counterexample"),
                H("The equality equivalence fails at p=1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "It is false that for every natural n and every nonzero complex family z, equality in the reciprocal-norm moment bound at p=1 is equivalent to all z_j being equal. For n=2 and z=(1,2), P′(Z)=3Z²−6Z+2 has roots 1−sqrt(3)/3 and 1+sqrt(3)/3. Both roots are positive, their reciprocal norm sum is 3, and c(2,1) times (1+1/2) is also 3, while 1 and 2 differ."))),
                DescribeRole.Theorem))));
}
