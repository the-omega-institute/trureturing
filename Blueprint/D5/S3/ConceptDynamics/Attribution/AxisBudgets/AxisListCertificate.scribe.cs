using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution.AxisBudgets;

internal sealed class AxisListCertificateDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bounded lists specify the incidence of the factor certified by their degrees and charge.",
        H("List certificates for one-coordinate inclusion factors"),
        Blocks(
            Entry("factor-rows", "MaskedFactorWithRows", "An inclusion factor with specified incidence",
                "The Boolean factor satisfies the marked loop, degree, inclusion and budget conditions. "
                + "Its true entries are exactly the pairs in the supplied relation.",
                DescribeRole.Definition),
            Entry("mask-equivalence", "maskEquiv", "Masks identify the subsets excluding coordinate zero",
                "For n free coordinates, map each mask below two to the n to the set of its occupied "
                + "coordinates with indices shifted by one. This is a bijection onto the subsets that omit zero.",
                DescribeRole.Definition),
            Entry("mask-rank", "mask_rank", "Mask weight is the rank of its subset",
                "For any mask in range, the number of occupied bits equals the cardinality "
                + "of its corresponding subset.", DescribeRole.Theorem),
            Entry("mask-top", "mask_top", "The all-ones mask is the full subset",
                "The mask with value two to the n minus one represents the full subset of free coordinates.",
                DescribeRole.Theorem),
            Entry("list-certificate", "list_axis_factor", "Bounded lists certify an exact factor table",
                "At multiplier three in selected mode, use row and column lists of masks with no duplicates. "
                + "Their entries are in range and the two lists agree on every ordered pair. Their lengths "
                + "have the required marked and ordinary degrees. The all-ones loop is absent, ordinary "
                + "row entries obey bitwise inclusion, and the listed odd-to-odd charge is within budget. "
                + "There is a corresponding Boolean factor. An entry is true exactly when the target "
                + "mask occurs in the source row list.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Entry(string id, string declaration, string title, string statement,
        DescribeRole role)
    {
        string scope = declaration switch
        {
            "maskEquiv" or "mask_rank" or "mask_top" => "AxisMaskTransport.",
            "list_axis_factor" => "ListBridge.",
            _ => "",
        };
        return Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + scope + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
    }
}
