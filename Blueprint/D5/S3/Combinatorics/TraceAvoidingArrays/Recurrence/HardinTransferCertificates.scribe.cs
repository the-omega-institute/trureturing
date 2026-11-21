using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinTransferCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source vector identities with exact integer lags.",
        H("Continuation polynomials"),
        Blocks(
            Node("row1", "rowOne", "Full-state relation at height 1", DescribeRole.Theorem,
                "On all 3 unrestricted columns at height 1, the power at exponent 3 on ones equals the source lag-weighted sum of the power vectors at exponents 2 down to 1. The coefficient sum is one. The coefficients are (3, −2)."),
            Node("row2-lags", "rowTwoCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 3 are (3, 0, −2)."),
            Node("row2", "rowTwo", "Full-state relation at height 2", DescribeRole.Theorem,
                "On all 9 unrestricted columns at height 2, the power at exponent 4 on ones equals the source lag-weighted sum of the power vectors at exponents 3 down to 1. The coefficient sum is one."),
            Node("row3-lags", "rowThreeCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 4 are (4, 1, −6, 2)."),
            Node("row3", "rowThree", "Full-state relation at height 3", DescribeRole.Theorem,
                "On all 27 unrestricted columns at height 3, the power at exponent 5 on ones equals the source lag-weighted sum of the power vectors at exponents 4 down to 1. The coefficient sum is one."),
            Node("column2", "wordTwo", "Full-state relation at width 2", DescribeRole.Theorem,
                "On all 6 proper words at width 2, the power at exponent 2 on ones equals the source lag-weighted sum of the power vectors at exponents 1 down to 0. The coefficient sum is one. The coefficients are (4, −3). The diagonal and vertical-bond square matrices each satisfy this identity."),
            Node("column3-lags", "wordThreeCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 3 are (6, −7, 2)."),
            Node("column3", "wordThree", "Full-state relation at width 3", DescribeRole.Theorem,
                "On all 12 proper words at width 3, the power at exponent 3 on ones equals the source lag-weighted sum of the power vectors at exponents 2 down to 0. The coefficient sum is one. The diagonal and vertical-bond square matrices each satisfy this identity."),
            Node("column4-lags", "wordFourCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 3 are (8, −11, 4)."),
            Node("column4", "wordFour", "Full-state relation at width 4", DescribeRole.Theorem,
                "On all 24 proper words at width 4, the power at exponent 3 on ones equals the source lag-weighted sum of the power vectors at exponents 2 down to 0. The coefficient sum is one."),
            Node("row-two-radical", "rowTwoRadical", "The two-row quadratic relation", DescribeRole.Theorem,
                "For all nine columns, applying C²−2C−2I to ones gives the zero vector. The identity uses exponent zero on every column and supplies the source radical formula."),
            Paragraph(Text("For each source state, the allowed labels at each successor position exclude the labels on all incident cross-bonds. For a proper-word transfer also require adjacent successor labels to differ. Horner evaluation of the integer relation verifies the zero residual at every actual state."))
        )));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
}
