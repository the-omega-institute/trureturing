using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class CrossingAnchorOrderingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual positive crossing anchor orders two negative LARGE occurrences and all SMALL occurrences between arbitrary checked endpoints.",
        H("A crossing anchor orders both negative gates"),
        Blocks(
            Describe.Lean(DescribeId.Create("crossing-anchor-two-negative-order"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/CrossingAnchorOrdering.exists_order_two_negative"),
                H("Complete ordering with an actual anchor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let Q>=2 and C=2Q-1. A physical list T contains only SMALL steps, |f(i)|<Q. Two distinct physical occurrences v1,v2 outside T are negative LARGE, with Q<=-f(vj)<=C, and T++[v1,v2] is Nodup. Put M=max(-f(v1),-f(v2)) and c=C-M. An actual occurrence a in T has positive value m=f(a) satisfying m<=c and min(-f(v1),-f(v2))<=m+c. Given 0<=b<=Q-1 and 0<=e<=C with b+sum(T)+f(v1)+f(v2)=e, there is a permutation of the ENTIRE T++[v1,v2] staying in [0,C] from b. Its exact endpoint is e, and every natural take, including empty and overlength takes, stays in the strip. In particular e need not lie below c. Distinct labels remain distinct when their weights coincide.")),
                    Paragraph(Text("With just one negative LARGE of magnitude L left and the anchor still present, put c1=C-L. If the current height u>=L, execute it immediately. Otherwise the exact endpoint equation and the nonpositive SMALL mass imply that the full positive filter has mass at least L-u. Reserve the actual anchor a and use the single-anchor selector to construct an actual positive packet R with L-u<=sum(R)<=L-u+c1. The packet is executed, so its monotone prefixes reach a checked height in [L,C]. Execute the negative gate and order the ENTIRE remaining SMALL complement to e by pairwise compatibility. This construction uses no supplied subset and no endpoint bound by c1.")),
                    Paragraph(Text("Call a positive SMALL Bad when its weight exceeds c. If none is Bad, every opposite pair is compatible, including pairs against either LARGE. Otherwise take an actual first Bad i, which fits because b<=Q-1. If i is the sole Bad, execute i and order the ENTIRE pairwise-compatible remainder directly, including both negative LARGE. If a second Bad j exists and [i,j] fits, its height exceeds 2c>=m+c>=l, where l is the smaller negative magnitude: execute that smaller physical negative and finish the maximum negative by the one-negative construction while preserving a. Every other positive SMALL has weight below Q<=l<=m+c, which supplies that construction's size hypothesis. If the pair fails but i alone reaches l, execute the smaller negative and again preserve the anchor for the complete one-negative tail.")),
                    Paragraph(Text("In the remaining failed-pair case the height u after i lies below l. Execute the actual anchor a and then the MINIMUM negative: l<u+m<l+m<=M+m<=C. The new height z=u+m-l lies in [0,m), hence below c. The failed pair gives u+f(j)>C. Now j fits from z, since z+f(j)<=c+Q-1<=C, and reaches z+f(j)>C+m-l>=M. Execute the MAXIMUM negative and order the ENTIRE remaining SMALL complement to e. Thus the explicit gate sequence is i,a,MIN,j,MAX. No bound M<=2c is required. All branches retain every occurrence, including arbitrarily many Bad labels, and check the entire prefix rather than postulating a legal competitor.")),
                    Paragraph(Text("The result is a finite-list ordering theorem for general integer weights. It uses the actual anchor as a physical gate resource and does not assert that an arbitrary source or global minimum supplies such an anchor. Its native centered-doubling application derives that resource from crossing inequalities. No general arbitrary-greedy principle for two incompatible positive steps, and no full Circle C3.1 conclusion, follows from this theorem."))),
                DescribeRole.Theorem)), []));
}
