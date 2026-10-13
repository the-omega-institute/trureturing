using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class CanonicalRelativeModularModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual supported modular coordinates are shared by the original DPI and fixed Petz equality.",
        H("Actual relative modular model"), Blocks(
            Describe.Lean(
                DescribeId.Create("supported-relative-modular-model"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.supported_relative_modular_model"),
                H("Actual supported relative modular model"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same actual Phi, rho and sigma with input support containment, this constructor "
                        + "returns their relative modular coordinates, output support, exact same fixed Kraus family, "
                        + "both Schwarz inequalities, trace pairing, norm saturation and exact canonical entropy "
                        + "readouts. These facts are proved by the original DPI construction. The original DPI "
                        + "consumes this model and retains its original statement; CanonicalPetzEquality consumes it "
                        + "to derive recovery. This struct does not assume entropy equality or recovery."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-kraus-representation"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.actual_kraus_representation"),
                H("Choose Kraus coordinates once from the channel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This actual finite Kraus representation is chosen as a function only of Phi, before any "
                        + "density states. It carries both the Gram normalization and the full-matrix action. The "
                        + "construction was extracted once from the original DPI proof and is consumed by that DPI "
                        + "and the fixed-reference Petz theorem."))),
                DescribeRole.Definition))));
}
