using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class Scale38RawEndpointSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete raw endpoint spectrum and exact paid sets of nested compensation scans.",
        H("Scale38 Raw Endpoint Spectrum"),
        Blocks(
            Paragraph(Text(
                "The family contains the baseline P_0, enlarged-slot members X_j with indices starting at one, "
                + "and contracted-position members Y_i with indices starting at zero. "
                + "A raw endpoint has a safe sequence of its own leaf queries: each branch group "
                + "and each absent group has at most one surviving member, and only the target survives.")),
            Def("endpointTargets", "Endpoint targets", "The baseline, X_1, and contracted positions satisfying i + 2 at least k."),
            Def("scanLength", "Literal scan lengths", "The baseline and X_1 scans have k + 1 queries. The last Y position has k + 1 queries; the preceding Y position has k + 2."),
            Def("scanAddress", "Literal scan addresses", "The baseline scans q_1 through q_(k+1). X_1 scans q_2 through q_(k+1), then d = RR. Y_(k-2) scans q_1 through q_(k-1), then b_1, b_2, b_3. Y_(k-1) scans q_1 through q_k, then b_2. Here b_h = RLR^(h-1)LLR and q_t = LR^(t-1)LLR."),
            Def("exitAddress", "Exact competitor exit addresses", "For a target in endpointTargets and a distinct competitor, this is the competitor's first nonleaf address in the target scan. The target has no extra paid address."),
            Describe.Lean(DescribeId.Create("scale38-raw-endpoint-spectrum"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Complete spectrum, safe scans and exact paid sets"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For k = 1, every family member is a raw endpoint. For k = 2, the endpoints are "
                        + "P_0, X_1, Y_0 and Y_1. For k at least three, they are exactly "
                        + "P_0, X_1, Y_(k-2) and Y_(k-1). The finite-index condition i + 2 at least k "
                        + "selects precisely the last two Y positions, or the sole Y position when k = 1.")),
                    Paragraph(Text(
                        "Each displayed scan is safe. Its actual controller follows the target reply "
                        + "until a singleton branch or absent group exits, then runs that member's complete verifier. "
                        + "Following the entire target scan starts the target verifier. Other replies enter the fallback. "
                        + "The controller terminates correctly on the full source domain. Its cost on each family member "
                        + "is 3k + 14, except that the target costs 3k + 13.")),
                    Paragraph(Text(
                        "Every paid set is the member's complete leaf set together with its extra set Delta. "
                        + "Delta is empty for the target. With target P_0, X_j exits at q_j and Y_i at q_(i+2). "
                        + "With target X_1, P_0 exits at d, X_j for j at least two exits at q_j, "
                        + "and every Y_i exits at q_(i+2).")),
                    Paragraph(Text(
                        "With target Y_(k-2), X_j for j less than k exits at q_j, and Y_i for i at most k-3 "
                        + "exits at q_(i+2). The remaining competitors X_k, P_0 and Y_(k-1) exit respectively "
                        + "at b_1, b_2 and b_3. With target Y_(k-1), every X_j exits at q_j, "
                        + "each earlier Y_i exits at q_(i+2), and P_0 exits at b_2. "
                        + "Each competitor's extra set is the singleton containing its displayed exit address.")),
                    Paragraph(Text(
                        "For X_j with j at least two, Y_(j-2) and Y_(j-1) agree on every target leaf. "
                        + "For Y_i with i + 3 at most k, X_(i+2) and X_(i+3) agree on every target leaf. "
                        + "At a matching reply both competitors survive; at a branch or absent reply both would "
                        + "occupy one group, violating safety. The complete labelled frontier covers every leaf, "
                        + "so these obstructions exclude every other target without restricting the query menu."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("scale38-raw-endpoint-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
