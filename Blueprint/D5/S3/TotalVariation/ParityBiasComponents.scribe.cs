using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParityBiasComponentsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/TotalVariation/ParityBiasComponents";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At fixed columns and raw offset, the connected components of the bias fiber are contractible.",
        H("Connected components of a fixed-law bias fiber"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sign-sector-contractible"),
                DeclarationHandle.Create(Module + ".signSector_contractible"),
                H("A fixed sign region is contractible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix an input column at each label in a finite binary vector space, a raw affine " +
                    "offset, and a reference bias family. Consider all signed biases of absolute value " +
                    "at most one producing the reference law at those columns and offset. At any point " +
                    "of this fiber, prescribe its sign on every label whose column projects nontrivially " +
                    "modulo the fair subgroup. The resulting subtype is contractible. The contraction " +
                    "scales the fair-subgroup coordinates to zero and interpolates logarithmic absolute " +
                    "biases on the other coordinates while keeping their signs fixed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("connected-component-eq-sign-sector"),
                DeclarationHandle.Create(Module + ".connectedComponent_eq_signSector"),
                H("The nonzero quotient columns distinguish the connected components"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In the subspace topology on the fiber, a bias vector belongs to the connected " +
                    "component of a given realization exactly when the two vectors have the same " +
                    "signs on all labels outside the fair subgroup. The biases at those labels " +
                    "cannot vanish in the fiber. The sign regions are open, closed, and connected."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("card-bias-fiber-components"),
                DeclarationHandle.Create(Module + ".card_biasFiber_components"),
                H("The binary sign equation counts the components"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the reference biases have absolute value at most one, let J be the labels " +
                    "with nonzero quotient columns and let r be the dimension of their span. " +
                    "The number of distinct connected components is two to the power of the size " +
                    "of J minus r. The feasible sign vectors are a fiber of the binary linear map " +
                    "sending a coefficient vector to its sum of projected columns. Changing the " +
                    "signs of the reference magnitudes realizes every coefficient vector in this fiber."))),
                DescribeRole.Theorem))));
}
