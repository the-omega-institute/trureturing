using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class ComplementChargeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Context-preserving event complement has an affine signed readout and negates it exactly under balance.",
        H("Complement and Background Charge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complement-affine-readout"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/ComplementCharge.complement_readout"),
                H("The exact signed complement formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each archived event contributes positive or negative one. Readout sums only selected "
                    + "events; background charge sums the current region. The formula applies Mathlib's "
                    + "finite-sum subtraction theorem with the actual selection containment proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balance-necessary-and-sufficient"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Spacetime/ComplementCharge.balanced_iff_complement_negates"),
                H("Balance is exactly the negation guard"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Zero background charge suffices by the affine formula; the empty selection proves "
                    + "necessity. Balance concerns the current region, not every archived event. "
                    + "Complement retains the complete context and is involutive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-count-readout"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/ComplementCharge.charge_eq_signed_card"),
                H("The readout counts signed events"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sum is the integer difference of positive and negative event counts. "
                    + "Numerical opposite fibers reuse the existing complement-fiber API and remain sets "
                    + "of selections. Arithmetic inverses and quotient operations are later constructions."))),
                DescribeRole.Theorem))));
}
