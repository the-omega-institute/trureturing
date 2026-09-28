using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class ClassicalProductRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit ClassicalProductRecovery constructions. The linked declarations do not certify unproved analytic or quantum extensions.",
        H("ClassicalProductRecovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("product-recovery-chain"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ClassicalProductRecovery.product_recovery_chain"),
                H("product recovery chain"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applies the pinned Mathlib measure-level KL chain rule to a constant hidden thermal kernel. Infinite values are retained rather than silently mapped to a finite divergence."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("recovery-terms-finite"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ClassicalProductRecovery.recovery_terms_finite"),
                H("recovery terms finite"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves finiteness of both summands from finite total KL before any real-valued subtraction is performed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("recovery-defect-real"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ClassicalProductRecovery.recovery_defect_real"),
                H("recovery defect real"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Converts the ENNReal chain identity to a real deficit only after proving both summands finite."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thermallift-minimizes"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ClassicalProductRecovery.thermalLift_minimizes"),
                H("thermalLift minimizes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructed product lift attains the marginal KL and no Markov-disintegrated joint law with that marginal has smaller KL."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thermallift-unique-minimum"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ClassicalProductRecovery.thermalLift_unique_minimum"),
                H("thermalLift unique minimum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Cancels only a finite marginal KL. Equality of objective values forces equality of the actual joint measures, using the genuine converse Gibbs inequality."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("predictive-defect-invariant"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ClassicalProductRecovery.predictive_defect_invariant"),
                H("predictive defect invariant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual commuting observation/evolution square, with preserved reference measures, preserves both full and observed KL. It does not construct the Hamiltonian flow or a Gaussian density. A later theorem in this module constructs the abstract standard Borel disintegration."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("arbitrary-joint-recovery-chain"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ClassicalProductRecovery.arbitrary_joint_recovery_chain"),
                H("Construct the conditional kernel from any joint law"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the standard Borel hidden-space hypotheses, Mathlib constructs the conditional kernel from the arbitrary joint measure itself. No disintegration witness is assumed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("arbitrary-joint-recovery-defect"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ClassicalProductRecovery.arbitrary_joint_recovery_defect"),
                H("Finite real defect for an arbitrary joint law"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The conditional kernel construction connects the original measure directly to the product recovery. Taking real parts is guarded by finite total KL."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-joint-laws-unique-minimum"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ClassicalProductRecovery.all_joint_laws_unique_minimum"),
                H("Unique minimum over all joint laws with a fixed marginal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every probability law with the prescribed marginal satisfies the lower bound. At a finite marginal KL value, equality holds exactly for the constructed thermal product law."))), DescribeRole.Theorem))));
}
