using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class SourceFixedMinorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal fixed-minor source polynomials",
        H("SourceFixedMinor"),
        Blocks(
        Paragraph(Text("sourceJ, sourceN, sourceD and sourceC are the integer circuit of VI (2.3) over a commutative coefficient ring. sourceNumerator contains the three clock-five, clock-six and clock-seven numerators in this order. The third entry uses the row (-20,70,-84,35); it is distinct from the clock-eight numerator in the actual read pair.")),
        Paragraph(Text("sourceBt and sourceBb use formal polynomial differentiation in the independent t and b coordinates. sourceE0 and sourceE1 are polynomials in r, with the exact integer coefficient expansions of VI (3.2) for the ordered pairs (N0,N1) and (N0,N2). Their normalization is checked before specialization: 45 D(t,b) Ei(tb,b) equals b^7 times the corresponding formal Jacobian numerator. No leading coefficient is divided out.")),
        Paragraph(Text("literalRow and literalMatrix retain all twenty-eight shifts and all twenty-nine descending columns. The source normalization connects the formal source criticality equations to the fixed-minor linear relation. It does not prove that the chosen fixed 28-row minor is nonzero, nor that the stored candidate lift equals the normalized-minor lift.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-literal-fixed-minor-relation"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceFixedMinor.literal_fixed_minor_relation"),
            H("literal fixed-column common-root relation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For real b,z, if sourceE0(b) and sourceE1(b) both vanish at z, then z times the determinant of fixedMinorR(literalMatrix(b)) plus the determinant of fixedMinorC(literalMatrix(b)) equals zero. literalMatrix has all twenty-eight rows r^13 E0 through E0 followed by r^13 E1 through E1, in columns r^28 through 1."))), DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-source-fixed-minor-relation"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceFixedMinor.source_fixed_minor_relation"),
            H("literal circuit to fixed-minor relation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For real t,b, with nonzero sourceD(t,b) and both formal source Jacobian numerators for (N0,N1) and (N0,N2) equal to zero, the same fixed determinants satisfy (tb) det(fixedMinorR)+det(fixedMinorC)=0. The normalization identities supply the two common-root equations. No leading coefficient is divided out, and no selected-root common-zero hypothesis is discharged by this statement."))), DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-source-e0-normalization"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceFixedMinor.source_e0_normalization"),
            H("first exact normalized minor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real t,b, 45 sourceD(t,b) times sourceE0(b) evaluated at tb equals b^7 times (sourceBt(0) sourceBb(1) minus sourceBb(0) sourceBt(1)), with both partials evaluated at (t,b)."))), DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-source-e1-normalization"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceFixedMinor.source_e1_normalization"),
            H("second exact normalized minor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real t,b, 45 sourceD(t,b) times sourceE1(b) evaluated at tb equals b^7 times (sourceBt(0) sourceBb(2) minus sourceBb(0) sourceBt(2)), with both partials evaluated at (t,b)."))), DescribeRole.Theorem))));
}
