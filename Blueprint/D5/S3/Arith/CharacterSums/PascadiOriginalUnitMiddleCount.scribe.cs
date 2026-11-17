using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalUnitMiddleCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six actual subsets of the original integer rows give the complete unit-middle count, without supplied shortness, shortest-vector, right-side or endpoint restrictions.",
        H("The complete original unit-middle contribution"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-complete-unit-middle-original-tuples"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalUnitMiddleCount.actual_unit_middle_tuple_count"),
                H("Assemble all original unit-middle charts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every epsilon>0 there is K>0 uniform in prime p, M, real widths 1<=X<=Y with 3Y<p^2, positive H with H^2=A=XY and p^3<=A<=p^4, the two alternating units modulo p^3, and the finite original integer row set T. Require the separate literal X,Y bounds, the unchanged original six-return word in order (a,t,b,d,w,v) to equal minus the identity, and both original middle entries w,t to be units. Write L=1+log(2p)/log 2. Then card(T)<=K p^epsilon (A(1+L)+A^2/p^4)+sqrt(K p^epsilon A^6 L/p^15), subject to the three explicit numerical long-chart separations (32A/p^3)^5<=M^5 p^3, (10368*3^9)^5 M^35<p^4 and (24*(8*18)^4)^5 M^40<p.")),
                    Paragraph(Text("The actual finite parameter set is T.image(originalMiddle). The unit original middle entry proves existence of its reduced congruence-lattice basis, so one basis is chosen internally at each occupied parameter. Its shortest vector is reused in every branch. No basis or value at an unoccupied parameter is an assumption, and different rows with the same middle pair cannot introduce different retained charts.")),
                    Paragraph(Text("Filter T into six actual subsets: nonunit shortest first coordinate; unit shortest first coordinate in the short range H^2 Q<=p^6; the complementary long range with nonunit original hyperbola right side; either physical endpoint zero; unit right side with a nonzero nonunit endpoint; and the retained long range with unit shortest first coordinate, unit right side and unit first entries of both endpoints. The proof establishes that these subsets cover T. They may overlap; finite union cardinality bounds the total by the sum of their actual cardinalities.")),
                    Paragraph(Text("The nonunit-shortest branch contributes at most 66048 A^2/p^4 and the short unit-vector branch at most 148992 A L. The original long nonunit-right-side theorem contributes C_epsilon p^epsilon A^2/p^4. The zero-endpoint branch contributes at most 18A. The actual nonzero nonunit-endpoint incidence theorem contributes C_epsilon p^epsilon (A/p+A^2/p^4). Finally the retained original-row theorem contributes C_epsilon p^epsilon (A+(A/p)L+A^2/p^4)+sqrt(C_epsilon p^epsilon A^6 L/p^15). The original small-width inequalities needed by these theorems follow from 1<=X<=Y and 3Y<p^2; p<=H follows from p^3<=A. Since p^epsilon>=1 and p>=1, the six bounds are absorbed into the displayed common K bound, including monotonicity of its square root.")),
                    Paragraph(Text("Every count is in the original integer ReturnRows and keeps the original even-row order y2,y0,y1. This module removes all geometric and endpoint branch restrictions from the unit-middle contribution. The three explicit numerical separations, the complementary area and bounded-prime ranges, nonunit-middle recovery and all-scalar-center assembly belong to the subsequent full original estimate."))),
                DescribeRole.Theorem)))));
}
