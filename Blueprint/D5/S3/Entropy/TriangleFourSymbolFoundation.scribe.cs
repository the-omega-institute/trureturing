using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class TriangleFourSymbolFoundationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Entropy/TriangleFourSymbolFoundation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite entropy, crossing supports and original common-record laws supply the binary triangle structure.",
        H("Foundations of the Original Stochastic Triangle Law"),
        Blocks(
            Paragraph(Text(
                "The source and output alphabets are arbitrary finite types. The source law is nonnegative "
                + "and normalized, and each incident kernel is a nonnegative normalized row. Agreement "
                + "annuls every off-diagonal response cell. The joint record retains all original source "
                + "symbols, structural zeros and unused output symbols. Only positive incident-pair rows "
                + "are forced to be point masses; zero-marginal rows remain unrestricted.")),
            Node("original_law_recoverability", "Agreement forces the active original rows",
                "Assume agreement. At each positive source cell, the product response law and agreement force "
                + "all three response vectors to be point masses at one common symbol. "
                + "Every positive incident-pair marginal has a positive extension. Thus its "
                + "fixed kernel row is a point mass. The incident readouts agree on every "
                + "positive source cell, and the record-cell identity also covers zero source cells."),
            Node("original_law_common_record", "The common record belongs to the same law",
                "Assume agreement. Summing the six-variable law over the other two outputs gives recordLaw. "
                + "The output weights are a probability vector. Replacing the first response "
                + "by either other incident response gives the same record/source joint law."),
            Node("dual_nonneg", "Dual total correlation is nonnegative",
                "For a normalized nonnegative finite three-variable law, strong subadditivity and entropy subadditivity make its dual total correlation nonnegative."),
            Node("dual_zero_product", "Zero dual total correlation gives a threefold product",
                "For a normalized nonnegative finite three-variable law, zero dual total correlation forces the full table to equal the product of its three marginals, including zero cells."),
            Node("totalCorrelation_dual_balance", "Total correlation balances pair and dual information",
                "For every nonnegative finite three-variable table, twice its KL total correlation equals the three pair mutual informations plus dual total correlation."),
            Node("cardinal_lower_bound", "Crossing support families need four coordinates",
                "If three finite support families cover the coordinates and every cross-family pair has exactly one common coordinate, at least two coordinates imply at least four."),
            Node("three_codes", "Four crossing coordinates carry parity labels",
                "When the crossing support families cover between two and four coordinates, each family admits a surjective Boolean label and the coordinates admit a bijection from Boolean pairs. Membership in the three families selects the first bit, second bit and their exclusive-or."),
            Node("mass_pos", "Both labelled blocks have positive mass",
                "A surjective Boolean label on the positive-mass subtype gives each extended block a strictly positive mass in the original nonnegative law."),
            Node("mass_sum", "The two block masses sum to one",
                "Partitioning a normalized finite law by any Boolean label preserves total mass."),
            Node("cell_from_support", "Support codes identify every pair cell",
                "A nonnegative product cell selected from zero or the product of the original marginals is exactly the product of the two coded marginal blocks. Positive factors imply active marginals; the identity also treats zero marginals."),
            Node("fair_weights", "Parity forces fair block weights",
                "Three normalized Boolean weight vectors with positive first and second weights, whose pair products agree along parity, all have weight one half in each block."),
            Node("posterior_from_pair", "Pair tables determine the original posterior",
                "If an output has mass one quarter and its pair table is a product with second block mass one half, summing the normalized second posterior identifies the first posterior as twice the first block mass."),
            Node("positive_entry", "Positive total mass has a positive entry",
                "A finite real table with positive sum contains a positive entry."),
            Node("record_nonneg", "Original record cells are nonnegative",
                "The original record cell is the product of a nonnegative source cell and a nonnegative incident response probability."),
            Node("output_is_probability", "The original output law is normalized",
                "Summing the original record law gives a nonnegative output law of total mass one."),
            Node("record_eq_other_responses", "Agreement identifies the three record tables",
                "Under agreement, either other incident response gives the same record/source cell as the first response. Zero source cells are included."))));

    private static DocumentBlock Node(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("triangle-foundation-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Module + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
