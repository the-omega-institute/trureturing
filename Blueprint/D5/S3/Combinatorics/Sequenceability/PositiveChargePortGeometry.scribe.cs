using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;
internal sealed class PositiveChargePortGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Sequenceability/PositiveChargePortGeometry.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original port incidence and directed geometry",
        H("Original port incidence and directed geometry"), Blocks(
        Paragraph(Text("The coordinate type is arbitrary. originalSpan H is the integer span of the original coefficient-one Boolean rows; minimalFamily is the full inclusion-minimal Complete family. Geometry retains the original opposite rows, exact two-supplier port neighbourhoods and pair coverage. No coordinate is identified or discarded.")),
        Describe.Lean(DescribeId.Create("semicomplete"),
            DeclarationHandle.Create(Prefix + "semicomplete"),
            H("Actual port colours give a semicomplete terminal relation"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For arbitrary bzero and z, let rank be injective on the terminal family and let the exterior blue coordinates K be disjoint from every opposite row. Ports at z are red on bzero; on every other opposite row the least terminal neighbour has red ports. Pair coverage then gives an arc in at least one direction between every two distinct terminals, witnessed by an actual original blue port. The semicompleteness conclusion requires no endpoint extremality assumption."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("strong-connectivity"),
            DeclarationHandle.Create(Prefix + "stronglyConnected"),
            H("A nonuniversal opposite row supplies terminal paths"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Assume bzero is an opposite row, a and z are its distinct terminal neighbours, a is least and z greatest in the injective terminal rank, and a terminal u is not adjacent to bzero. The exterior blue coordinates K are disjoint from every opposite row. Explicit paths through a,u,z establish strong connectivity of the same actual-port relation. The mixed_B and red_frame results retain concrete red and blue coordinates used by the cycle-word construction."))), DescribeRole.Theorem),
        Paragraph(Text("Independent selected minimal supports have unique suppliers at a coordinate and at q. The forbidden_port lemma excludes an original port from the entire selected disjoint union. PositiveChargePorts consumes this geometry to construct a reverse Hamilton port cycle and avoiding words; that construction remains conditional on the stated geometry and all-Complete decomposition inputs. All declarations retain their PositiveChargePorts namespace.")) )));
}
