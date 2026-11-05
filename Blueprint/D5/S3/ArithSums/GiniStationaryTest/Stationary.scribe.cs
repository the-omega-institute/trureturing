using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums.GiniStationaryTest;

internal sealed class StationaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stationary criterion holds for the arithmetic mean and a cubic Gini mean.",
        H("Positive normalized stationary tuples"), Blocks(
            Describe.Lean(DescribeId.Create("gini-stationary-characteristic-derivatives"),
                DeclarationHandle.Create("D5/S3/ArithSums/GiniStationaryTest/Stationary.chiDeriv_parameters"),
                H("The two characteristic derivatives"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Certificates/grunwaldpales2024gini")),
                Blocks(Paragraph(Text("At a positive real z, the characteristic derivative for (1,0) is one and the characteristic derivative for (2,-1) is (2z+1/z squared)/3. These formulas reduce the common multiplier equations to equality of one scalar function at every coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gini-stationary-one-zero-two-negative-one"),
                DeclarationHandle.Create("D5/S3/ArithSums/GiniStationaryTest/Stationary.stationaryTest_one_zero_two_negOne"),
                H("Stationary tuples pass the comparison test"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Certificates/grunwaldpales2024gini")),
                Blocks(Paragraph(Text("For every positive tuple of any nonzero length, normalization by the Gini parameters (1,0) means that the sum of coordinates equals the length. The two characteristic derivatives are 1 and (2z+1/z squared)/3. The stationary equations therefore place all coordinates on one common level of 2z+1/z squared.")),
                    Paragraph(Text("Distinct positive points a and b on such a level satisfy a+b=2(ab) squared. For a third level point z, reciprocal substitution turns the level equation into (z inverse) cubed equal to an affine function of z inverse. The strictly convex cubic on the positive half-line cannot meet that affine function at three distinct points, so the level has at most two values. A nonconstant normalized tuple consequently has precisely two values a<1<b. If S=a+b and P=ab, each coordinate obeys z squared=S*z-P and 1/z=(S-z)/P. Summing and dividing by the tuple length gives second moment S-P and reciprocal moment (S-1)/P. Positivity of (1-a)(b-1)=(P-1)(2P+1) gives P>1. The difference of moments is (P-1)(1-a)(b-1)/P, which is positive. On the constant tuple both moments are one. Thus the Gini mean with parameters (2,-1) is at least one at every normalized stationary tuple, and it is strictly greater than one whenever the tuple is not constant."))),
                DescribeRole.Theorem))));
}
