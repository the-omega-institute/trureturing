using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class ConservativeDagEmbeddingDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/ConservativeDagEmbedding.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conservative DAG embeddings compose and preserve dependency reachability.",
        H("Conservative DAG Embedding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conservative-embeddings-preserve-reachability"),
                DeclarationHandle.Create(Prefix + "map_reachable"),
                H("Conservative embeddings preserve reachability"),
                StatementSource.FromAuthor(MapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let an embedding preserve and reflect direct dependency edges. Every "
                            + "reflexive-transitive path in the source maps to a path between the "
                            + "corresponding embedded endpoints.")),
                    Paragraph(Text(
                        "The conclusion concerns preservation only. Reflection is carried by the "
                            + "structure binder but is not promoted to a stronger path equivalence "
                            + "in this theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("composed-reachability-maps-successively"),
                DeclarationHandle.Create(Prefix + "map_reachable_comp"),
                H("Composition maps paths by successive mapping"),
                StatementSource.FromAuthor(CompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Quantify two composable conservative embeddings and a source path. "
                            + "Mapping through their composite yields the same proof-irrelevant "
                            + "reachability witness as mapping through them successively.")),
                    Paragraph(Text(
                        "The equality is between path witnesses for the displayed path; it does "
                            + "not identify the two embedding structures themselves."))),
                DescribeRole.Theorem))));

    private static Formula Relation(Formula carrier) =>
        Seq(carrier, Sp, To, Sp, carrier, Sp, To, Sp, F.Id("Prop"));

    private static Formula MapFormula()
    {
        Formula edgeV = F.Id("edgeV");
        Formula edgeW = F.Id("edgeW");
        Formula embedding = F.Id("embedding");
        Formula first = F.Id("first");
        Formula last = F.Id("last");
        Formula path = Call("ReflTransGen", edgeV, first, last);

        return Disp(Seq(
            Forall, Sp, edgeV, Colon, Sp, Relation(F.Id("V")), Comma, Sp,
            edgeW, Colon, Sp, Relation(F.Id("W")), Comma, RowBreak, Grp(),
            embedding, Colon, Sp, Call("ConservativeEmbedding", edgeV, edgeW), Comma, Sp,
            first, Comma, Sp, last, Colon, Sp, F.Id("V"), Comma, RowBreak, Grp(),
            path, Sp, Rightarrow, RowBreak, Grp(),
            Call("ReflTransGen", edgeW, Call("toFun", embedding, first),
                Call("toFun", embedding, last)), Dot));
    }

    private static Formula CompositionFormula()
    {
        Formula edgeV = F.Id("edgeV");
        Formula edgeW = F.Id("edgeW");
        Formula edgeZ = F.Id("edgeZ");
        Formula first = F.Id("firstEmbedding");
        Formula second = F.Id("secondEmbedding");
        Formula source = F.Id("source");
        Formula target = F.Id("target");
        Formula path = F.Id("path");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, edgeV, Colon, Sp, Relation(F.Id("V")), Comma, Sp,
            edgeW, Colon, Sp, Relation(F.Id("W")), Comma, RowBreak, Grp(),
            edgeZ, Colon, Sp, Relation(F.Id("Z")), Comma, Sp,
            Forall, Sp, first, Colon, Sp,
            Call("ConservativeEmbedding", edgeV, edgeW), Comma,
            RowBreak, Grp(), second, Colon, Sp,
            Call("ConservativeEmbedding", edgeW, edgeZ), Comma, Sp,
            source, Comma, Sp, target, Colon, Sp, F.Id("V"), Comma, RowBreak, Grp(),
            path, Colon, Sp,
            Call("ReflTransGen", edgeV, source, target),
            Comma, RowBreak, Grp(),
            Open, Call("mapReachable", Call("comp", second, first), path), Sp, Eq, Sp,
            Call("mapReachable", second, Call("mapReachable", first, path)), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
