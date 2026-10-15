using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMSourceActionClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual source-copy actions transport ordered marginals and preserve the EJM score.",
        H("All 192 original source actions"),
        Blocks(
            Paragraph(Text("The finite maps act on the original twenty coordinates and retain every ordered coordinate in each of the sixteen triangle and sixteen singleton marginals. Lean checks the exact maps, inverse witnesses and local transports. The averaged original-support cut consumes these transports; no symmetry is imposed on an event or on a hidden-variable distribution.")),
            Describe.Lean(DescribeId.Create("triangle-map-closure"),
                DeclarationHandle.Create(Prefix + "triangle_map_closure"),
                H("Transporting the entire ordered triangle marginal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each source action, the transformed ten-node marginal is its recorded original marginal index composed with one of the twelve actual local coordinate permutations. The averaged cut uses this equality on the full 132-row triangle support."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-map-closure"),
                DeclarationHandle.Create(Prefix + "singleton_map_closure"),
                H("Transporting the entire ordered singleton marginal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each transformed nine-node marginal factors through the recorded original singleton index and local permutation. This transports the full 168-row support in the actual-event conflict proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-score"),
                DeclarationHandle.Create(Prefix + "score_sourceSymmetry"),
                H("The complete centered score under source actions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The local coefficient invariances and the bijections of all sixteen marginal indices preserve the sum of centered blocks. Every source action is checked, with no replacement of the original score by a residual score."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("outcome-score"),
                DeclarationHandle.Create(Prefix + "score_relabel"),
                H("A common bijection of the four outcomes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reindexing the exact head contractions proves score invariance when both coefficient functions are invariant under the common outcome bijection."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-source-score"),
                DeclarationHandle.Create(Prefix + "actual_score_sourceSymmetry"),
                H("The original coefficient functions and all source actions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual F1 and F2 coordinate invariances instantiate the source-score theorem. This supplies score preservation, while a positive global margin still requires a complete checked certificate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-outcome-score"),
                DeclarationHandle.Create(Prefix + "actual_score_relabel"),
                H("The original coefficient functions and common outcome relabeling"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equality-pattern lookup for the original coefficient functions preserves their values under every common outcome bijection. The theorem proves exact score equality and carries no positivity claim."))), DescribeRole.Theorem))));
}
