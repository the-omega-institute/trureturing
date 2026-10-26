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
                    Paragraph(Text("Let Q>=2 and C=2Q-1. A physical list T contains only SMALL steps, |f(i)|<Q. Two distinct physical occurrences v1,v2 outside T are negative LARGE, with Q<=-f(vj)<=C, and T++[v1,v2] is Nodup. Put M=max(-f(v1),-f(v2)) and c=C-M. An actual occurrence a in T has positive value m=f(a) satisfying m<=c, M<=2c and M<=m+c. Given 0<=b<=Q-1 and 0<=e<=C with b+sum(T)+f(v1)+f(v2)=e, there is a permutation of the ENTIRE T++[v1,v2] staying in [0,C] from b. Its exact endpoint is e, and every natural take, including empty and overlength takes, stays in the strip. In particular e need not lie below c. Distinct labels remain distinct when their weights coincide.")),
                    Paragraph(Text("With just one negative LARGE of magnitude L left and the anchor still present, put c1=C-L. If the current height u>=L, execute it immediately. Otherwise the exact endpoint equation and the nonpositive SMALL mass imply that the full positive filter has mass at least L-u. Reserve the actual anchor a and use the single-anchor selector to construct an actual positive packet R with L-u<=sum(R)<=L-u+c1. The packet is executed, so its monotone prefixes reach a checked height in [L,C]. Execute the negative gate and order the ENTIRE remaining SMALL complement to e by pairwise compatibility. This construction uses no supplied subset and no endpoint bound by c1.")),
                    Paragraph(Text("Call a positive SMALL Bad when its weight exceeds c. If none is Bad, every opposite pair is compatible, including pairs against either LARGE. Otherwise take an actual first Bad i, which fits because b<=Q-1. If a second Bad j exists and [i,j] fits, its height exceeds 2c>=M: execute a physical negative of maximum magnitude and finish by the one-negative construction while preserving a. If that pair fails or does not exist but i alone reaches the smaller negative magnitude, execute that smaller negative and again preserve the anchor for the complete one-negative tail.")),
                    Paragraph(Text("In the remaining case the height u after i lies below the smaller negative magnitude. Execute the actual anchor a and then a maximum-magnitude negative: M<u+m<=C. The new height z lies in [0,c]. If i was the sole Bad, the full remainder is pairwise compatible. If a second Bad j exists, the failed pair gives u+f(j)>C. Now j fits from z, since z+f(j)<=c+Q-1<=C, and reaches z+f(j)>c+m>=M. Execute the other physical negative and order the ENTIRE remaining SMALL complement to e. All branches retain every occurrence, including arbitrarily many Bad labels, and check the entire prefix rather than postulating a legal competitor.")),
                    Paragraph(Text("The result is a finite-list ordering theorem for general integer weights. It uses the actual anchor as a physical gate resource and does not assert that an arbitrary source or global minimum supplies such an anchor. Its native centered-doubling application derives that resource from crossing inequalities. No general arbitrary-greedy principle for two incompatible positive steps, and no full Circle C3.1 conclusion, follows from this theorem."))),
                DescribeRole.Theorem)), []));
}
