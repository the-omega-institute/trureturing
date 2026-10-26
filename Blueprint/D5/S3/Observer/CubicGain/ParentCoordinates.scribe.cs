using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class ParentCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A world keeps the single matrix P(r,b), one fixed drift d and one whole nonzero real polynomial of degree at most three",
        H("ParentCoordinates"),
        Blocks(
        Paragraph(Text("A world keeps the single matrix P(r,b), one fixed drift d and one whole nonzero real polynomial of degree at most three. The chronological action list is [J,M,J,M,M,M], acting by left multiplication. The initial read counts and the first five literal readings are [0,24,147/5,24,18]. No reset, shifted clock or alternative jointly acquired reading is introduced.")),
        Paragraph(Text("Gain coordinates are the original values at clocks 0,1,2,3. The fixed-node Lagrange polynomial evaluates to these samples. Mathlib’s polynomial uniqueness theorem is applied directly to show that every polynomial of degree at most three has this representation; lower degrees, vanishing samples and repeated roots require no separate branch.")),
        Paragraph(Text("For ε=d-24, the parent equation is εΛ+(24/5)(b-1/8)(6/(1+b)-2/(1+2b))=0. Its gain samples are [-24-ε,-ε/j,(27/5-ε)/(1+b),-ε/n]. The literal fourth-row residual equals U times the parent equation. The equivalence reconstructs all five rows and the entire world, and its reverse direction uses only positive j,n,T,U as denominators.")),
        Paragraph(Text("The actual fifth and sixth M readings are P₅=24+(U+n)(96-108/T)+εA₅ and P₆=24+(2U+n)(240-243/T)+εA₆, where A₆=1+(2U+n)(10-36/j+45/T-20/n). These formulas come from the literal matrix products and the same gain. Unequal readings at clocks zero and one rule out only the identically zero gain.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-gainpoly-eval"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ParentCoordinates.gainPoly_eval"),
            H("gainPoly eval"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every four-sample vector a and real clock s, evaluating gainPoly a at s gives exactly gain a s."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-gain-samples"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ParentCoordinates.gain_samples"),
            H("gain samples"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every a : Fin 4 → ℝ and i : Fin 4, the gain evaluated at the original clock i equals aᵢ."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-gainpoly-degree"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ParentCoordinates.gainPoly_degree"),
            H("gainPoly degree"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every four-sample vector a, gainPoly a has degree at most three; lower degrees and the zero polynomial satisfy the same estimate."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-polynomial-representation"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ParentCoordinates.polynomial_representation"),
            H("polynomial representation"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every real polynomial g of degree at most three equals gainPoly formed from g(0),g(1),g(2),g(3). Mathlib’s interpolation uniqueness identifies the reconstructed whole polynomial with g."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-literal-traces"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ParentCoordinates.literal_traces"),
            H("literal traces"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For all real r,b, the chronological traces at clocks zero through six are [1,j,1+b,n,1+2b,1+2b+n,2(1+2b)+n]."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-source-positivity"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ParentCoordinates.source_positivity"),
            H("source positivity"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For 0≤r≤1 and b>0, the quantities j,n,T=1+b and U=1+2b are all positive."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-actual-m-responses"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ParentCoordinates.actual_m_responses"),
            H("actual m responses"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every coordinate triple C, the literal readings of parentWorld C at clocks five and six equal fifthResponse C and sixthResponse C, using the same whole gain and fixed drift."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-parent-gain-nonzero"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ParentCoordinates.parent_gain_nonzero"),
            H("parent gain nonzero"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every world satisfying the five literal parent rows has a nonzero whole gain polynomial. A zero polynomial would force the distinct readings at clocks zero and one to equal the same drift."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-fourth-residual"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ParentCoordinates.fourth_residual"),
            H("fourth residual"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For real r,b,d with j,n,T,U nonzero, the clock-four residual d+g(4)U-18 for the gain parentGain(r,b,d-24) equals U times parentEq(r,b,d-24)."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-parent-world-iff"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ParentCoordinates.parent_world_iff"),
            H("parent world iff"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every world W=(r,b,d,a) in sample coordinates, the conjunction of 0<r<1, b>0 and all five literal parent rows holds exactly when worldCoordinates W is a strict parent and parentWorld (worldCoordinates W) = W."))),
            DescribeRole.Theorem))));
}
