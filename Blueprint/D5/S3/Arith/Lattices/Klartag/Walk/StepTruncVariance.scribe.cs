using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class StepTruncVarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Step Trunc Variance"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate step trunc variance to the stochastic ellipsoid construction.")),
            Node("claim-1", "sqTrunc", "sq Trunc",
                "The truncated squared step norm.", DescribeRole.Definition),
            Node("claim-4", "memLp_sqTrunc", "mem Lp sq Trunc",
                "MemLp _ 2, from the cap.", DescribeRole.Theorem),
            Node("claim-5", "pairwise_indepFun_sqTrunc", "pairwise indep Fun sq Trunc",
                "Independence across steps, carried through the truncation by IndepFun.comp.", DescribeRole.Theorem),
            Node("claim-6", "variance_sum_sqTrunc_le", "variance sum sq Trunc le",
                "The variance of the truncated drift proxy, K·cap²/4. At the adopted parameters cap = η² and this is N·η⁴/4 = T·h·dim²·n², about 4·log n·n⁻⁵.", DescribeRole.Theorem),
            Node("claim-8", "integrable_sum_sqTrunc", "integrable sum sq Trunc",
                "The truncated drift proxy is bounded, hence integrable.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
