using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class GoldenFactorParikhMagnusBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/GoldenFactorParikhMagnusBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed three-by-three Parikh observer and its second-order Magnus coordinates reconstruct every legal golden factor.",
        H("Faithful Nilpotent Observation on Golden Factors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-factor-parikh-faithfulness"),
                DeclarationHandle.Create(Prefix + "golden_factor_eq_iff_parikh_matrix_eq"),
                H("One matrix determines the legal factor"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The matrix entries recover both letter counts, hence the length, and the scattered pair count. The existing golden binomial rigidity theorem then recovers the full word. Equal absolute occurrence positions are not claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-factor-magnus-recovery"),
                DeclarationHandle.Create(Prefix + "golden_factor_eq_of_first_degree_and_magnus"),
                H("Counts and one Magnus center suffice"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The center is 2c-rf. With the first-degree counts it recovers c over the integers. This is a concrete sufficient observer on the constrained language, without any nonzero-commutator hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-factor-step-two-exact-fibers"),
                DeclarationHandle.Create(Prefix + "golden_factor_eq_iff_step_two_signature_eq"),
                H("Step-two fibers coincide with word fibers"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The statement uses the existing chronologicalSignature with explicit nilpotent matrix generators. It does not posit an arbitrary observer to be faithful."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-factor-first-second-strictness"),
                DeclarationHandle.Create(Prefix + "legal_golden_first_to_second_order_strictness"),
                H("A legal first-order collision is separated"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The consecutive golden factors LS and SL share first degree while their doubled Magnus centers are respectively 1 and -1. This is an unconditional finite witness."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Scope: consecutive factors of the fixed golden word. No recovery of prime labels, physical time, or absolute occurrence indices is asserted. Arbitrary binary words still have Parikh collisions. The classical Sturmian recovery phenomenon is attributed by GoldenFactorSecondOrderBinomialRigidity; this node supplies the exact matrix and Magnus integration.")))));
}
