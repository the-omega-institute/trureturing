using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class Scale38RawEndpointSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw endpoint addresses and leaf-response obstructions for the nested compensation family.",
        H("Scale38 Raw Endpoint Spectrum"),
        Blocks(
            Paragraph(Text(
                "The nested compensation family is indexed by one baseline member and two finite-index rows. "
                + "The existing Scale38 query addresses provide the left comb scan.")),
            Def("rawEndpoint", "Peeling endpoint predicate", "A native family member is a raw endpoint when its transported finite family admits a Peels list from the full survivor set."),
            Describe.Lean(DescribeId.Create("scale38-no-peel-of-leaf-agreement"),
                DeclarationHandle.Create(Prefix + "no_peel_of_leaf_agreement"),
                H("Equal leaf replies obstruct peeling"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If two distinct competitors differ from the target and agree at every target leaf, "
                    + "then no safe raw peeling list can delete both competitors. A nonleaf response group "
                    + "would contain both members, while a matching response keeps both in the survivor set."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("scale38-leaf-agreement-of-rows"),
                DeclarationHandle.Create(Prefix + "leaf_agreement_of_rows"),
                H("Row certificates determine all target leaves"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When every labelled row belonging to a target gives the same reply for two competitors, "
                    + "the complete frontier and response table imply equality of their replies at every leaf "
                    + "of that target."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("scale38-raw-endpoint-spectrum-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
