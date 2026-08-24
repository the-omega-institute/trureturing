using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class FiniteQuotientJointKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All finite quotients jointly detect exactly the complement of the finite residual.",
        H("The Joint Kernel of All Finite Quotients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-quotient-joint-kernel"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientJointKernel."
                        + "finite_quotient_joint_kernel"),
                H("The joint finite-quotient kernel is the finite residual"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each finite-index normal subgroup H, the canonical observation "
                            + "sends a group element to its class in G/H. The joint observer "
                            + "records these classes for every such H.")),
                    Paragraph(Text(
                        "An element is in the kernel of the joint observer exactly when it "
                            + "belongs to every finite-index normal subgroup. This intersection "
                            + "is the finite residual.")),
                    Paragraph(Text(
                        "Mathlib's residual-finiteness criterion identifies this intersection "
                            + "with the trivial subgroup, while the standard homomorphism-kernel "
                            + "criterion identifies trivial kernel with injectivity."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula observer = Call("finiteQuotientObserver", group);
        Formula residual = Call("finiteResidual", group);
        Formula trivial = Call("trivialSubgroup", group);

        Formula kernelIdentity = Equal(Call("ker", observer), residual);
        Formula residualCriterion = new Formula.Logic(
            Call("ResiduallyFinite", group),
            FormulaLogicOperator.Iff,
            Equal(residual, trivial));
        Formula faithfulnessCriterion = new Formula.Logic(
            Equal(residual, trivial),
            FormulaLogicOperator.Iff,
            Call("Injective", observer));

        return F.Disp(new Formula.Logic(
            kernelIdentity,
            FormulaLogicOperator.And,
            new Formula.Logic(
                residualCriterion,
                FormulaLogicOperator.And,
                faithfulnessCriterion)));
    }
}
