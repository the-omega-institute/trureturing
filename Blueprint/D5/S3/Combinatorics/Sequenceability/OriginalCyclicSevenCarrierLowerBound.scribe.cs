using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class OriginalCyclicSevenCarrierLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original six-pair support pattern with distinguished order seven has cyclic carrier minimum 154.",
        H("The cyclic order-seven minimum"), Blocks(
            Describe.Lean(
                DescribeId.Create("original-cyclic-seven-carrier-lower-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/OriginalCyclicSevenCarrierLowerBound.cyclic_seven_carrier_card_lower_bound"),
                H("Every cyclic order-seven carrier has at least 154 elements"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let G be a finite cyclic abelian group and f a labeling of the entire original Coordinate 7. Assume the q label has additive order exactly seven. For every finite coordinate subset C, assume that nonemptiness together with a zero label sum is equivalent to C being precisely the original triple {q,a_i,b_i} for one of the six pair indices. Then card(G) is at least 154. Label injectivity and selected-support assumptions are not added.")),
                    Paragraph(Text("Put H=<f(q)> and K=G/H. The translated quotient bound gives card(G) at least 140. Since H has exactly seven elements and card(G)=seven*card(K), card(K) is at least twenty. It is enough to exclude the remaining quotient orders twenty and twenty-one.")),
                    Paragraph(Text("The existing complete-support bridge gives six nonzero quotient labels A_i in distinct negation orbits and forbids every signed zero triple at three distinct indices. The shared cyclic normalization transports these classes through K isomorphic to ZMod(card(K)), choosing a positive representative r_i at most half the modulus in each orbit. The r_i remain distinct, and neither r_i+r_j=r_k nor r_i+r_j+r_k=card(K) can hold at three distinct indices.")),
                    Paragraph(Text("For either remaining modulus, all six representatives lie in {1,...,10}. There are exactly 210 six-element subsets. The finite certificate states that each subset contains x<y<z with x+y=z or x+y+z equal to the modulus. These are respectively the signed relations x+y-z=zero and x+y+z=zero, contradicting the original triple exclusion. This exhausts subsets without enumerating the order of the six labels. Therefore card(K) is at least twenty-two and card(G) is at least seven*twenty-two=154.")),
                    Paragraph(Text("The existing signed construction at s=three and k=zero attains this bound on ZMod 7 times ZMod 22. It has 154 elements, its q label has additive order exactly seven, and it satisfies the same complete original zero-support classification. The factors are coprime, so the Chinese remainder equivalence makes the carrier cyclic. Hence 154 is the exact minimum for this order-seven cyclic problem. No optimality claim at other parameters or literature-priority claim is made.")))))));
}
