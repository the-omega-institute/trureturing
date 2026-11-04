using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete physical second-peak equal-outer face",
        H("All natural parameters and finite repetitions"),
        Blocks(Describe.Lean(DescribeId.Create("second-peak-equal-outer-whole-face"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Endpoint.actualSource_second_peak_equal_outer_joint_lift"),
            H("Whole-face endpoint"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every independent natural a,b,c with 2<=a,2<=c,max(a,c)<=b, put k=a+b+c+a and A=1+2^a+2^(a+b)+2^(a+b+c). There is one permutation sigma of every original Fin(k) occurrence and one natural literal cut j<=k with both OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)). For every natural m,n the take(n) of m finite copies of each actual scalar word stays in its exact strip. For every natural m both complete repeated scalar totals are zero, including empty, full and overlong takes. The partition first reuses EqualFirstTwoLast at b=a and EqualOuterThree at c=a, then uses the lower, palindromic and strict physical constructions. The palindromic b=a+1 overlap directly reuses BalancedGaps. Only arithmetic length and exponent equalities are normalized on these overlaps. Full unrestricted J/C3.1 and Circle remain OPEN."))), DescribeRole.Theorem)), []));
}
