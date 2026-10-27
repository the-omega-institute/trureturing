using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class ExactW3CenterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact algebraic third critical center",
        H("ExactW3Center"),
        Blocks(
        Paragraph(Text("criticalPolynomial is the degree-67 real polynomial whose descending integer coefficient list is the pinned FC list. The rational interval (12758053/100000000,12758054/100000000) has opposite exact endpoint signs, so it contains an exact real root.")),
        Paragraph(Text("critical_root_exists records the degree and constructs a root b3 in that interval by the intermediate value theorem. The root is retained as an algebraic real selected by its defining polynomial and interval, rather than by a decimal approximation.")),
        Paragraph(Text("determinantalLiftDenominator and determinantalLiftNumerator are the reduced linear-subresultant coefficient polynomials from the pinned regular critical elimination. liftedR(b) is the exact quotient -c(b)/a(b), and liftedCoordinates(b) is (liftedR(b)/b,b). exactW3 is the ordinary coefficient-coordinate chartWorld at the selected root.")),
        Paragraph(Text("exactW3_parent_of_source_certificate proves that this exact lift is an OriginalParent and that chartRead is analytic whenever the source-specific rational enclosures and nonzero denominator certificate hold. The chart is the original coefficient topology and keeps the source certificate explicit.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-critical-root-exists"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ExactW3Center.critical_root_exists"),
            H("exact degree-67 critical root"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The pinned criticalPolynomial has degree 67 and has a real root strictly between 12758053/100000000 and 12758054/100000000."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-exact-w3-parent"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ExactW3Center.exactW3_parent_of_source_certificate"),
            H("exact W3 parent bridge"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("If the selected root's determinantal lift satisfies the displayed original source strip, nonzero denominator and strict-coordinate conditions, then exactW3 is an OriginalParent and chartRead is analytic at its exact lifted coordinates."))),
            DescribeRole.Theorem))));
}
