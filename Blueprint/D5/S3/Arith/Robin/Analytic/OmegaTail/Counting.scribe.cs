using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class CountingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exponent supplied by fixed prime bins.", H("The exponent supplied by fixed prime bins"), Blocks(
            Describe.Lean(DescribeId.Create("finite-box-lower"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Counting.finite_box_lower"),
                H("Finite bin lower exponent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix a finite inhabited family of disjoint positive intervals (a(j),b(j)], with positive masses r(j)<b(j)-a(j), sum r(j)=1, and lambda+sum r(j)*log(b(j))<0. For every epsilon>0, eventually log(tailCount(lambda,x))/scale(x) is at least sum (b(j)-a(j))*binEntropy(r(j)/(b(j)-a(j)))-epsilon. The prime number theorem gives actual prime capacities in intervals (a(j)*log(x),b(j)*log(x)]. Rounding and adjusting the first box produce exactly floor(threshold(lambda,x))+1 primes. The exact second-order logarithmic cost limit, rather than the first-order total alone, proves that all products fit under x. The finite product bound and moving binomial entropy asymptotic give the lower exponent."))), DescribeRole.Theorem))));
}
