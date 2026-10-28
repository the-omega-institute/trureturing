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
        Paragraph(Text("The fixed r^15 coefficients are -102720(b^2+8b+4) and -657408(b^2+8b+4). Both are nonzero at the selected positive FC root. This verifies the degree guard required to retain the literal degree-fifteen rows. It does not prove that the chosen fixed 28-row minor is nonzero, nor that the stored candidate lift equals the normalized-minor lift.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-source-circuit-correspondence"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceFixedMinor.source_circuit_correspondence"),
            H("literal existing circuit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real t,b, sourceD equals circuitD(t,b), sourceC equals all four circuitC samples, and sourceNumerator entry zero equals the actual clock-five numerator circuitP(t,b)."))), DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-source-e0-normalization"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceFixedMinor.source_e0_normalization"),
            H("first exact normalized minor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real t,b, 45 sourceD(t,b) times sourceE0(b) evaluated at tb equals b^7 times (sourceBt(0) sourceBb(1) minus sourceBb(0) sourceBt(1)), with both partials evaluated at (t,b)."))), DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-source-e1-normalization"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceFixedMinor.source_e1_normalization"),
            H("second exact normalized minor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real t,b, 45 sourceD(t,b) times sourceE1(b) evaluated at tb equals b^7 times (sourceBt(0) sourceBb(2) minus sourceBb(0) sourceBt(2)), with both partials evaluated at (t,b)."))), DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-source-leading-coefficients"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceFixedMinor.source_leading_coefficients"),
            H("fixed degree-fifteen coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real b, coefficient fifteen of sourceE0(b) equals -102720(b^2+8b+4), and coefficient fifteen of sourceE1(b) equals -657408(b^2+8b+4)."))), DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-selected-root-leading-guard"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceFixedMinor.selected_root_leading_guard"),
            H("selected-root fixed-degree guard"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("With no hypotheses, coefficient fifteen of each of sourceE0(criticalRoot) and sourceE1(criticalRoot) is nonzero. criticalRoot is the selected root of the literal FC in (12758053/100000000,12758054/100000000)."))), DescribeRole.Theorem))));
}
