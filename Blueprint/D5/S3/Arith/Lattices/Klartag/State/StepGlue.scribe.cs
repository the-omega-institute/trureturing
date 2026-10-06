using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class StepGlueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/StepGlue.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("Step Glue"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate step glue to the stochastic ellipsoid construction.")),
            Node("claim-1", "stdGaussian_coord_law", "std Gaussian coord law",
                "Each coordinate of a standard Gaussian on EuclideanSpace ℝ ι is N(0,1).", DescribeRole.Theorem),
            Node("claim-2", "coord_law", "coord law",
                "A random variable with the standard Gaussian law has N(0,1) coordinates.", DescribeRole.Theorem),
            Node("claim-3", "coord_indep", "coord indep",
                "…and independent coordinates.", DescribeRole.Theorem),
            Node("claim-4", "coord_law_smul", "coord law smul",
                "The chain's increment is r • ξ with ξ standard, so its coordinates are N(0, r²).", DescribeRole.Theorem),
            Node("claim-5", "coord_indep_smul", "coord indep smul",
                "…and they stay independent.", DescribeRole.Theorem),
            Node("claim-7", "measureReal_compl_chainGood_le", "measure Real compl chain Good le",
                "The failure probability of the full good event, the two costs added.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
