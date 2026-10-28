using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sewing;

internal sealed class CanonicalTwoCutOccupationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal two-cut occupation control for canonical lattice coefficients.",
        H("Canonical two-cut occupation sewing"),
        Blocks(
            Paragraph(Text("The overlap envelope retains both unrestricted occupations and the literal factorialEnvelope. MixedControl records the all-mode coefficient estimate with the explicit energy polynomial and the finite positive overlap family. The analytic comparison theorem then consumes a summable majorant to obtain the exact signed-mode pair sum, including zero radial parameters.")),
            Node("MixedControl", "Uniform mixed descendant control", "For arbitrary signed modes and both occupations, the literal wordCoeff is bounded by the recursively defined word constant, the total-energy polynomial and the finite overlap envelope built from binomial(e,u), T^(degree(e-u)) and factorialEnvelope A(d-u). The predicate keeps the charge coefficient buffers A and T explicit. The recurrence proof and the summability of this majorant remain separate obligations of the sewing owner.", DescribeRole.Definition),
            Node("mixed_pair_summable_of_control", "Two-index absolute summability comparison", "Assuming the exact mixed coefficient control and a summable literal overlap majorant, comparison yields the original pair-index kernel with rowWeight on the first occupation, columnWeight on the second occupation, arbitrary signed offset s+level(e)-level(d), and both open-disk parameters. No inverse Gram, positivity or nonzero-q premise is introduced by the comparison.", DescribeRole.Theorem),
            Paragraph(Text("The source definitions are the original private canonical maps, wordCoeff, rowWeight, columnWeight and factorialEnvelope accessed through Batteries.Tactic.OpenPrivate. The finite overlap expression is a proof-local majorant, not a replacement field. The unproved coefficient induction and majorant summability are intentionally not claimed as completed by this unit."))
        )));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("canonical-two-cut-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
