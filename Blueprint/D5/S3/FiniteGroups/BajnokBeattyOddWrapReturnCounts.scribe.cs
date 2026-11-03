using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattyOddWrapReturnCountsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At the first odd wrap, the actual lattice quotient return fibers have exact binomial counts.",
        H("Exact returns at the first odd wrap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-odd-wrap-return-counts"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyOddWrapReturnCounts.actual_odd_wrap_counts"),
                H("Four generator endpoints account for every return"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let p and t be integers with p at least 3, p odd, and t at least 2. Put m=6t-1 and L=(pm).toNat. For the (1,9) quotient take the integer-plane vectors v1=(p(m-1)/2,p(m+1)/2) and v2=(p(m-9)/2,-p(m+9)/2). For the (3,3) quotient use v1=(p(m-3)/2,p(m+3)/2) and v2=(p(m-3)/2,-p(m+3)/2). In each case the relation lattice is the full integer span of its two vectors and F is its actual quotient map. The signed coordinate words, endpoints, and return count W are the existing BajnokBeattyFirstReturnDefect definitions.")),
                    Paragraph(Text("At length L the exact formulas are W19(L)=2[choose(L,(p(m+1)/2).toNat)+choose(L,(p(m+9)/2).toNat)] and W33(L)=4 choose(L,(p(m+3)/2).toNat). All halves are integral because the relevant parameters are odd. The theorem supplies both formulas for the complete original quotient domains; it does not assume an endpoint list or a counting formula.")),
                    Paragraph(Text("The proof first treats arbitrary positive odd a,b<m. In sum-and-difference coordinates the two lattice generators are (pm,-pa) and (-pb,pm). The public Lee/square equivalence converts the word endpoint bound into max(|mq1-bq2|,|-aq1+mq2|) at most m for its integer lattice coefficients q1,q2. If these coefficients differ, the closed boundary forces exactly (1,0), (-1,0), (0,1), or (0,-1). The nonnegative sign regions use the strictly positive gaps m-a and m-b, while opposite signs force an axis endpoint; simultaneous negation covers the remaining regions. If the coefficients agree, the endpoint coordinate sum is a multiple of p(m-b), hence even. The rotated endpoint identity gives that sum the parity of the odd word length L, excluding this case. Thus every return endpoint is exactly one of the four signed lattice generators.")),
                    Paragraph(Text("The four endpoint fibers are disjoint: their coordinate sums are pm, -pm, -pb, and pb, which are distinct for 0<b<m and p>0. PlaneWordEndpointCount.endpoint_card counts a generator endpoint by the two transformed negative-sign subsets. One subset has size zero or L, so its binomial factor is one; the other contributes choose(L,(p(m+a)/2).toNat) or choose(L,(p(m+b)/2).toNat). Binomial symmetry gives the same count at the negative endpoint. Summing these four fibers and specializing to (a,b)=(1,9) and (3,3) proves the displayed formulas. They provide exact inputs for subsequent parameter comparison; no uniform comparison sign or literature novelty is claimed."))),
                DescribeRole.Theorem))));
}
