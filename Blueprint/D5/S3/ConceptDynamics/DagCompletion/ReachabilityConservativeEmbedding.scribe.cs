using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class ReachabilityConservativeEmbeddingDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/ReachabilityConservativeEmbedding.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reachability-conservative embeddings preserve and reflect prerequisite and consequence "
            + "closures.",
        H("Reachability-Conservative Embedding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("embedded-prerequisite-membership-is-equivalent"),
                DeclarationHandle.Create(Prefix + "mem_prerequisiteClosure_image_iff"),
                H("Prerequisite closure is preserved and reflected on the image"),
                StatementSource.FromAuthor(ImageFormula("prerequisiteClosure", "targets")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Quantify a reachability-preserving and reachability-reflecting embedding. "
                            + "An embedded node belongs to the target image's prerequisite closure "
                            + "exactly when the original node belongs to the original closure.")),
                    Paragraph(Text(
                        "The equivalence is restricted to nodes in the source carrier and target "
                            + "sets transported by the embedding image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("embedded-consequence-membership-is-equivalent"),
                DeclarationHandle.Create(Prefix + "mem_consequenceClosure_image_iff"),
                H("Consequence closure is preserved and reflected on the image"),
                StatementSource.FromAuthor(ImageFormula("consequenceClosure", "sources")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The same structure identifies consequence-closure membership after "
                            + "mapping the source set into the target carrier.")),
                    Paragraph(Text(
                        "No statement is made about target-carrier nodes outside the embedding's "
                            + "image."))),
                DescribeRole.Theorem))));

    private static Formula ImageFormula(string closure, string setName)
    {
        Formula edgeV = F.Id("edgeV");
        Formula edgeW = F.Id("edgeW");
        Formula embedding = F.Id("embedding");
        Formula set = F.Id(setName);
        Formula node = F.Id("node");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, edgeV, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            edgeW, Colon, Sp,
            F.Id("W"), Sp, To, Sp, F.Id("W"), Sp, To, Sp, F.Id("Prop"),
            Comma, RowBreak, Grp(),
            Forall, Sp, embedding, Colon, Sp,
            Call("ReachabilityEmbedding", edgeV, edgeW), Comma, Sp,
            set, Colon, Sp, Call("Set", F.Id("V")), Comma, Sp,
            node, Colon, Sp, F.Id("V"), Comma, RowBreak, Grp(),
            Call("toFun", embedding, node), Sp, InMacro, Sp,
            Call(closure, edgeW, Call("image", Call("toFun", embedding), set)),
            Sp, Iff, RowBreak, Grp(),
            node, Sp, InMacro, Sp, Call(closure, edgeV, set), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
