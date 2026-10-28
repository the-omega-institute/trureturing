using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class SelectedRootCommonZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected-root equations for the literal source minors",
        H("SelectedRootCommonZero"),
        Blocks(
        Paragraph(Text("The algebraic parameter is criticalRoot, the unique root of the literal degree-67 FC polynomial in the interval (12758053/100000000,12758054/100000000). Its candidate coefficient lift is r=-C(b)/A(b), using determinantalLiftNumerator and determinantalLiftDenominator. The denominator is nonzero at this selected root. The corresponding source point has coordinates t=r/b and b.")),
        Paragraph(Text("The two degree-15 polynomials sourceE0 and sourceE1 retain their 134 integer monomials and their original ordered clock-five/six and clock-five/seven pairs. Homogenizing their evaluations at r=-C/A gives degree-1802 integer polynomials divisible by FC. Each exact quotient has degree 1735. A coefficient-mass bound below 2^9000 makes evaluation at the integer base 2^9000 conclusive: if an integer polynomial of smaller coefficient mass vanishes there, every coefficient is zero. This yields polynomial identities before specializing to the selected algebraic root.")),
        Paragraph(Text("The exact source normalization then gives both original formal Jacobian numerators zero. The nonzero regular source denominator allows the fixed-minor relation for all twenty-eight shifted rows in columns r^28 through 1 to be applied at these coordinates. The clock-seven source read remains distinct from the absolute-clock-eight M read.")),
        Paragraph(Text("These equations do not identify the candidate A,C arrays with the actual primitive normalized fixed minors, prove that the chosen literal minor is nonzero, establish the common factor h at the selected root, or identify the full original W3 coefficient world and its response center. Those additional identities are separate conditions for the full W3 identification.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-selected-root-common-zero"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SelectedRootCommonZero.selected_root_common_zero"),
            H("literal selected-root equations and fixed-minor relation"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("At b=criticalRoot and t=liftedR(b)/b, the actual source denominator is nonzero, both literal sourceE polynomials vanish at liftedR(b), and both formal source Jacobian numerators for the ordered pairs (N0,N1) and (N0,N2) vanish. Consequently liftedR(b) times the determinant of fixedMinorR(literalMatrix(b)) plus the determinant of fixedMinorC(literalMatrix(b)) is zero. The common-zero equations and denominator conditions are conclusions, not added hypotheses."))),
            DescribeRole.Theorem))));
}
