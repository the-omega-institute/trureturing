using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalDerivativePartnersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual derivative-zero partner is counted, with one physical fiber weight and no nonalignment or assumed counting supplier.",
        H("The complete actual derivative-zero layer"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-original-derivative-zero-partners-subpower"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalDerivativePartners.actual_derivative_zero_partners_subpower"),
                H("Uniform weighted count of all actual bad partners"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every epsilon>0 choose one positive C before all original primes, units, parameters, actual bases, retained baseline and finite partner sets S. Let B be the actual index-p-cubed middle basis and B2 a reduced index-p-squared basis for the same t,w. Put H^2=XY and sigma=sqrt((Y/X)B2.R1^2+(X/Y)B2.R2^2), with X,Y,H positive. Assume the anchor identity physical(B,q)=(-w,-t), original WordSolution for the baseline and every partner, all retained basis/anchor/baseline/shifted-expression units, coordinate bounds J1,J2, and the literal physical rectangle with 2X,2Y<p^3. If every actual pencil derivative vanishes at the genuine reduced beta=V1/R1, then card(S)<=C*p^epsilon*(1+6H/(p*sigma)), provided 1<=J2<=J1, (J1*J2)^5<=M^5*p^3, (10368*3^9)^5*M^35<p^4 and (24*(8*18)^4)^5*M^40<p.")),
                    Paragraph(Text("Partition the actual finite set S by whether its integer pencil reduces coefficientwise to zero modulo p. The zero-reduction half consumes the complete exceptional-partner theorem, which includes aligned baselines. The nonzero half consumes the genuine singular-partner theorem and its constructed algebraic values. Their disjoint cardinalities add to card(S). The weight 1+6H/(p*sigma) is at least one, so it absorbs the zero-reduction half without another multiplicity factor. The final constant is the sum of the two uniform constants. No count, relevant-factor supplier, or coordinate-to-value injection is assumed."))),
                DescribeRole.Theorem),
            Paragraph(Text("This theorem closes the actual derivative-zero partner layer of Pascadi's original word on the retained chart. The full conjecture still requires parameter averaging, good-record summation, excluded-chart control and restoration of all original tuples. The source problem and pencil are attributed to Pascadi; no global priority or official acceptance is asserted.")))));
}
