using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeNegativeCommonCutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common zero cut for the native three-negative equal-gap family",
        H("One physical W mask completes both sources"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-three-negative-common-cut"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/ThreeNegativeCommonCut.native_three_negative_common_cut"),
                H("The complete c<a joint constructor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural a,c with 2<=c<a, set k=2a+c and v=1+2^a+2^(2a). There exist a permutation sigma of every physical Fin(k) label and a natural cut j<=k such that sigma is an OriginalOrder for (k,v) and earWord(k,sigma,j) is an OriginalOrder for (k+1,2v). OriginalOrder includes exact integer total zero and the half-modulus strip bounds for every natural prefix, including takes beyond the word length. The new word retains the old physical labels through castSucc and inserts exactly the distinct label k. Both words start at the same zero cut.")),
                    Paragraph(Text("Write t=2^a, u=2^c, A=t^2+t+1, B=(t+1)u+1, H=tu+t+1 and g=t(t+1)/2. The physical labels are U_i=i, alpha=c-1, V_i=c+i, beta=a+c-1, W_i=a+c+i and gamma=k-1. U has c-1 positive labels; V and W each have a-1. Centered uniqueness derives the paired positive values (A*2^i,2A*2^i), (B*2^i,(2B-1)*2^i), and (H*2^i,(2H-t-1)*2^i), as well as all three negative labels and the new ear value A. Equal numerical values never identify physical occurrences.")),
                    Paragraph(Text("When c=a-1, u=t/2. The literal OLD word is [V,beta,W,gamma,U,alpha]; the NEW word is [V,beta,W,gamma,k,U,alpha], with j=2a. The OLD post-beta, post-gamma and post-alpha heights are t/2,g,0. The NEW heights after those same negative labels are 0,0,0.")),
                    Paragraph(Text("When c<=a-2, put delta=t-u, f=floor((t+1)delta/H) and h=(t+1)delta-Hf. A single binary selection from the actual W row gives F, with E its physical complement. The same selected labels have OLD mass Hf and NEW mass (2H-t-1)f. The literal OLD word is [V,beta,E,gamma,F,U,alpha]; NEW inserts k immediately before gamma, giving [V,beta,E,k,gamma,F,U,alpha] and j=a+|E|. No second selection, source rotation or numerical-period quotient is used.")),
                    Paragraph(Text("The OLD post-beta, post-gamma and post-alpha heights are t-u,h,0. The NEW heights are t-2u,2h+1+(t+1)f,0. The term (t+1)f is the charge of the W support moved behind gamma. It is retained on the live proof path. With m=t/u=2^(a-c), the source powers force m=4 or m>=8. Euclidean division gives 0<=f<=m-2<t/2 and 0<=h<=H-1, so the mask fits all actual a-1 W positions.")),
                    Paragraph(Text("For m=4 the floor is exactly f=2, h=4u^2-5u-2 and the NEW gamma height is 8u^2-2u-1<g. For m>=8, the same height is at most 2tu+(t+1)m-1<=g-1, using t>=8u and u>=4. Hence both gamma seams lie within their exact caps. The beta seams satisfy their native caps directly, and alpha ends at zero. Positive-block strip concatenation then checks every intermediate height. The physical partition proves the complete permutation, and the three block nets prove both integer totals zero.")),
                    Paragraph(Text("This is an unconditional construction for the stated equal-gap family. The regions c>=a use other geometric or periodic arguments and are outside this theorem. No claim of a complete proof of Circle C3.1 or of literature novelty is made."))),
                DescribeRole.Theorem)), []));
}
