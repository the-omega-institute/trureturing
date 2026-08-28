using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class TypedProducerResolutionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Governance/TypedProducerResolution."
            + "typed_producer_resolution_fail_closed";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Producer actors enter artifact dependency edges only through typed resolution; "
            + "unresolved actors fail closed.",
        H("Typed Producer Resolution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typed-producer-resolution-fail-closed"),
                DeclarationHandle.Create(Declaration),
                H("Unresolved producer actors create no artifact edge and no admissible graph"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Artifact and ProducerActor are independent types. The producer map "
                            + "returns an actor, while only the resolver can return an artifact "
                            + "endpoint for the artifact-to-artifact edge relation.")),
                    Paragraph(Text(
                        "If producer(x) returns q but resolve(q) is none, every putative edge "
                            + "witness would require the contradictory equality "
                            + "resolve(q)=some(a). Hence no artifact edge enters x.")),
                    Paragraph(Text(
                        "The same unresolved actor contradicts ResolutionComplete. Because an "
                            + "AdmissibleProducerGraph contains resolution completeness together "
                            + "with exact agreement with ProducerEdge, no such graph exists.")),
                    Paragraph(Text(
                        "This is a fail-closed result: the actor is not silently accepted as an "
                            + "empty producer family merely because it contributes no edge."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula artifact = F.Id("Artifact");
        Formula actor = F.Id("ProducerActor");
        Formula type = F.Id("Type");
        Formula proposition = F.Id("Prop");
        Formula producer = F.Id("producer");
        Formula resolve = F.Id("resolve");
        Formula x = F.Id("x");
        Formula q = F.Id("q");
        Formula a = F.Id("a");
        Formula edges = F.Id("E");
        Formula optionActor = Call("Option", actor);
        Formula optionArtifact = Call("Option", artifact);
        Formula edgeType = Arrow(artifact, Arrow(artifact, proposition));

        Formula premises = Seq(
            Apply(producer, x), Sp, Eq, Sp, Call("some", q), Sp, Land, Sp,
            Apply(resolve, q), Sp, Eq, Sp, F.Id("none"));
        Formula noEdges = Seq(
            Forall, Sp, Typed(a, artifact), Comma, Sp, Neg, Sp,
            Call("ProducerEdge", producer, resolve, a, x));
        Formula noAdmissibleGraph = Seq(
            Neg, Sp, Exists, Sp, Typed(edges, edgeType), Comma, Sp,
            Call("AdmissibleProducerGraph", producer, resolve, edges));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, artifact, Comma, Sp, actor, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            Typed(producer, Arrow(artifact, optionActor)), Comma, Sp,
            Typed(resolve, Arrow(actor, optionArtifact)), Comma, Sp,
            Typed(x, artifact), Comma, Sp, Typed(q, actor), Comma,
            RowBreak, Grp(),
            premises, Sp, Longrightarrow,
            RowBreak, Grp(),
            noEdges, Sp, Land, Sp,
            Neg, Sp, Call("ResolutionComplete", producer, resolve), Sp, Land,
            RowBreak, Grp(),
            noAdmissibleGraph, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
