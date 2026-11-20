using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records;

internal sealed class PrimitiveRecordConditionalMemoryGapDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordConditionalMemoryGap";
    private const string Title = "Conditional entropy gain from retaining the visible pair";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title, H(Title),
        Blocks(
            Claim("primitiverecordmemorygap-cmi", "Conditional mutual information of the literal record",
                "collision_cmi_eq_memory_gap",
                "For the fair classical label X, visible pair O, and complementary record E, the conditional entropy reduction from adding O to E equals the quantum conditional mutual information I(X:O|E) of the relabeled finite c-q state."),
            Claim("primitiverecordmemorygap-asymptotic", "Exact leading gain",
                "collision_memory_gap_asymptotic",
                "The literal conditional entropy with full ring memory has coefficient one half at the alpha-to-twice-the-ring-length scale. The complementary-only coefficient is larger. Their difference has positive coefficient (302433 - 46875 sqrt(41)) / 16384 and is strictly positive at all sufficiently large ring lengths. In the cited independent-copy erasure model with degenerate Hamiltonians, a bath at fixed temperature, and a work battery, this entropy gain multiplies k_B T to give the work-rate gain. Each erasure-rate limit holds at fixed ring length before the ring-length limit."))));

    private static DocumentBlock.Describe Claim(string id, string title, string name, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps"),
                LibraryNoteRef.Create("D5/L/Quantum/goold2016thermodynamics")),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);
}
