using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteSectorChannelModelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact objects and quantified claims for finite sector channel optimality.",
        H("Finite Sector Channel Model"),
        Blocks(
            Paragraph(Text(
                "These definitions support the physical construction, upper and lower estimates, "
                + "and flat feasibility proofs. They carry no standalone optimality assertion.")),
            Def("finite-sector-model", "Model", "Finite sector spectral data",
                "Model fixes a finite sector type, positive target rank in every sector, "
                + "and a common finite list of nonnegative, decreasing spectral values "
                + "whose sum is one in each sector."),
            Def("finite-sector-kernel", "kernel", "Residual Gram kernel",
                "The kernel pairs two sectors by summing products of square roots of "
                + "their residual spectral values at the same coordinate."),
            Def("finite-sector-spectral-minimum", "spectralMinimum", "Spectral minimum",
                "The real infimum is over every probability weight on the finite "
                + "sector type of its quadratic form in the residual Gram kernel."),
            Def("finite-sector-encoding-channels", "EncodingChannels", "Actual encoding channels",
                "The source and target are quantum channels whose complete matrix actions "
                + "are prescribed by the respective isometric encoding matrices."),
            Def("finite-sector-tensor-raw-action", "tensorRawAction", "Tensor matrix action",
                "The action expands arbitrary local channels against every physical input "
                + "matrix unit, retaining both input and output indices."),
            Def("finite-sector-tensor-realization", "TensorRealization", "Product realization",
                "A joint channel realizes the product of two local channels when its "
                + "matrix action equals tensorRawAction for every physical input matrix."),
            Def("finite-sector-mixture-realization", "MixtureRealization", "Mixture realization",
                "A joint channel realizes a finite shared-classical mixture when its "
                + "action on every input matrix equals the weighted sum of product actions."),
            Def("finite-sector-product-errors", "productErrors", "Product error set",
                "Every member is the unhalved diamond distance of an actual joint "
                + "product channel after the source encoding from the target encoding."),
            Def("finite-sector-mixture-errors", "mixtureErrors", "Mixture error set",
                "Every member is the corresponding distance of a finite probability "
                + "mixture of actual product channels."),
            Def("finite-sector-full-claim", "FullOptimalityClaim", "Full optimality claim",
                "The claim includes actual encodings, every product and mixture "
                + "realization, both unrestricted infima and product attainment."),
            Def("finite-sector-constructive-claim", "ConstructiveOptimalityClaim",
                "Constructive optimality claim",
                "The same splitter has exact all-matrix partial-trace and Schur actions, "
                + "exact basis outputs, diamond equality, and both attained infima."),
            Def("finite-sector-flat-claim", "FlatFeasibilityClaim", "Flat feasibility claim",
                "For arbitrary positive source and target ranks, exact basis output by "
                + "local channels is equivalent to every source rank being a positive "
                + "integer multiple of its target rank."))));

    private static DocumentBlock Def(string id, string name, string title, string explanation) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Owner + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Definition);
}
