using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unified low-bit UXWV first ear", H("Independent unbounded gaps and the original physical source"),
        Blocks(Describe.Lean(DescribeId.Create("independent-tail-interior-first-ear"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Endpoint.actualSource_independent_tail_interior_first_ear"),
            H("One old word and its literal cut-zero ear"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For all independent naturals a,b,c,d with c>=2, d>=c+2, a>=c+d and b>=a+1, put k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). The conclusion supplies one sigma of Fin(k) with OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,0)). These full predicates include the exact physical permutation, zero total and both bounds for every natural take-prefix. No allocation, certificate, altered seed, orbit relabeling or existential cut is a premise.")),
                Paragraph(Text("Set z=2^c,w=2^d,lambda=2^(a-c-d),q=2^(b-a-1),x=lambda*z*w and y=2*q*x. Put H=lambda*(w+3*z+2),r=H mod 16,D0=2*floor(H/16),D1=x/8 and W0=min(4*q,floor((4+r)*q/4))-1. In chain order U,V,W,X, the positive mask banks are (u,z/2-1,W0,D0), (3*w/8-1-u,0,0,D1), (w/8,0,4*q-1-W0,x/2-2-D0-D1), and (0,0,y/2-4*q,1), where u=w/(2*z)-1 at c=2 and u=w/(2*z) otherwise. The chain starts are 0,d,d+c,d+c+b. Increasing physical labels within each bank followed by terminals U,X,W,V define sigma. Exact disjoint bit inventories include q=1 and every zero individual mask.")),
                Paragraph(Text("For lambda=1 the three cases c=2,c=3,c>=4 give D0=w/8,w/8+2,(w+3*z)/8 and W0=4*q-1,floor(7*q/2)-1,floor(3*q/2)-1. The latter floor errors lie between 0 and 1/2; every seam and peak slack is affine in that error. For lambda>=2, H is divisible by 4, K=1+(H mod 16)/4 lies between 1 and 4, D0=H/8-(K-1)/2 and W0=K*q-1. Every seam and peak slack is affine in K. Nonnegative polynomial expansions at both affine endpoints cover all the unbounded parameters.")),
                Paragraph(Text("Actual source recurrences and weighted decoded masks identify these seams and peak slacks with both original centered source rows. Positive bank prefixes remain between their starting seam and peak; each terminal reaches the next nonnegative seam, and the final seam is zero. The new row starts with the fresh physical label k of value A, so its full word is literally earWord(k,sigma,0) with unchanged old labels. The unrestricted four-gap Circle J question remains open. No literature novelty or full Circle J claim is made."))), DescribeRole.Theorem)), []));
}
