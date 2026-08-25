using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class FaithfulObservationTopologyDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/ObservationTopology/FaithfulObservationTopology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injective observations induce discrete topology and preserve catalog escapes.",
        H("Faithful Observation Topology"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discrete-partition-topology-is-injectivity"),
                DeclarationHandle.Create(
                    Prefix + "partitionTopology_eq_discrete_iff_injective"),
                H("A readout induces the discrete topology exactly when it is injective"),
                StatementSource.FromAuthor(DiscreteFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The partition topology identifies precisely those source points "
                            + "with equal observed values.")),
                    Paragraph(Text(
                        "If the topology is discrete, inseparable source points are equal, "
                            + "so equal observations force equal inputs. Conversely, an "
                            + "injective readout has the same fibers as the identity.")),
                    Paragraph(Text(
                        "The biconditional concerns equality with the bottom, hence "
                            + "discrete, topology on the source and adds no inhabitedness "
                            + "assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discreteness-is-unit-catalog-escape-preservation"),
                DeclarationHandle.Create(
                    Prefix + "discrete_partition_iff_preserves_unit_catalog_escape"),
                H("Discreteness is preservation of every one-row catalog escape"),
                StatementSource.FromAuthor(EscapeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the catalog input type is inhabited. The theorem compares "
                            + "discreteness of the observation partition with a universal "
                            + "one-row escape-preservation law.")),
                    Paragraph(Text(
                        "For every Unit-indexed catalog and candidate, a genuine escape "
                            + "before observation must remain an escape after both are "
                            + "postcomposed with the observation.")),
                    Paragraph(Text(
                        "The statement is an exact biconditional. It does not assert the "
                            + "preservation law without the displayed Nonempty instance."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula DiscreteFormula()
    {
        Formula state = F.Id("X");
        Formula observation = F.Id("Observation");
        Formula observe = F.Id("observe");

        return Disp(Seq(
            Forall, Sp, observe, Colon, Sp, Call("Concept", state, observation),
            Comma, Sp,
            Call("partitionTopology", observe), Sp, Eq, Sp,
            Call("bottomTopology", state), Sp, Iff, Sp,
            Call("Injective", observe), Dot));
    }

    private static Formula EscapeFormula()
    {
        Formula input = F.Id("Input");
        Formula output = F.Id("Output");
        Formula observation = F.Id("Observation");
        Formula observe = F.Id("observe");
        Formula catalog = F.Id("catalog");
        Formula candidate = F.Id("candidate");
        Formula instance = Seq(
            OpenBracket, Call("Nonempty", input), CloseBracket);
        Formula preservation = Seq(
            Forall, Sp, catalog, Colon, Sp,
            Arrow(F.Id("Unit"), Arrow(input, output)), Comma, Sp,
            candidate, Colon, Sp, Arrow(input, output), Comma, RowBreak, Grp(),
            Call("CatalogEscape", catalog, candidate), Sp, Rightarrow,
            RowBreak, Grp(),
            Call(
                "CatalogEscape",
                Call("observedCatalog", observe, catalog),
                Call("observedCandidate", observe, candidate)));
        Formula conclusion = Seq(
            Call("partitionTopology", observe), Sp, Eq, Sp,
            Call("bottomTopology", output), Sp, Iff, Sp,
            Open, preservation, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, observe, Colon, Sp, Arrow(output, observation),
            Comma, RowBreak, Grp(),
            Open, instance, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
