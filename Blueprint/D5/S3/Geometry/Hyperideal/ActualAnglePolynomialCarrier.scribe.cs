using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class ActualAnglePolynomialCarrierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/ActualAnglePolynomialCarrier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact polynomial stationary certificate on the physical edge quotient of a hyperideal face pairing.",
        H("Clipped original angles without winding aliases"),
        Blocks(
            Paragraph(Text("Each marked tetrahedron edge consumes the original six-cosh numerator and two positive face radicands. The first-quadrant unit half phase has squared-coordinate difference equal to the clipped cosine. Positive square roots and both saturated endpoints are expressed by polynomial conditions.")),
            Paragraph(Text("At a multiplication node, require nonnegative imaginary part and forbid both children to be minus one. The sum at each valid subtree then lies between zero and two pi in original-angle units. This is complete for an arbitrary binary bracketing; the endpoint alone is not complete.")),
            Describe.Lean(DescribeId.Create("half-phase-stationary-iff"), DeclarationHandle.Create(Prefix+"stationary_iff"),
                H("Exact winding certificate"), StatementSource.FromAuthor(PhaseStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A valid tree ending at minus one has exactly the target angle, even if leaves are zero or pi. Conversely every such total admits all binary bracketings."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-pairing-algebraic-stationary"), DeclarationHandle.Create(Prefix+"actual_pairing_algebraic_stationary"),
                H("Actual carrier stationarity"), StatementSource.FromAuthor(CarrierStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The program checks every physical edge of the face-pairing quotient and every one of its actual incidences. Repeated occurrences at the same physical edge are counted separately. Positive cosh inputs are required. This is a stationarity equivalence, not an assertion of geometric realization for every carrier."))), DescribeRole.Theorem),
            Paragraph(Text("Feng and Lin, Non-geometric ideal triangulations with all edge valences at least six, arXiv:2610.25217v2, sections 5.1, 6.4.3 and 6.4.4, use full phases and a winding certificate for their particular fans. The present half-phase tree test is exact per candidate at every finite valence. Quantifier elimination and the separate finite four-tetrahedron census are not asserted as Lean theorems here.")))));

    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula PhaseStatement()
    {
        var t = F.Id("t");
        return Disp(All("t",Call("PhaseCircuit"),Iff(
            And(Call("Valid",t),Equal(Call("Phase",t),Call("MinusOne"))),
            And(Call("LeavesInClosedInterval",t),Equal(Call("Angle",t),Call("TwoPi"))))));
    }
    private static Formula CarrierStatement()
    {
        var q = F.Id("q"); var x = F.Id("x");
        return Disp(All("q",Call("ActualFacePairings"),All("x",Call("PositiveCoshData",q),Iff(
            Call("ExistsExactPolynomialFans",q,x),Call("AllOriginalEdgeSumsAreTwoPi",q,x)))));
    }
}
