using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GroupInvariantPsi;

internal sealed class SandwichDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exponential overlap rates of uniform finite mixtures.",
        H("Mixture bounds"), Blocks(
            Describe.Lean(DescribeId.Create("group-invariant-psi-sandwich"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.sandwich"),
                H("Largest component overlap controls a uniform mixture"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a finite group of size k permute a finite alphabet, and let p and q be nonnegative functions on that alphabet. For s strictly between zero and one, let M be the largest relative permutation overlap. The overlap of the uniform mixtures of the n-fold product functions lies between M to the power n divided by k and k times M to the power n. Relative permutation reindexing reduces every component pair to a single-site overlap raised to the power n. The lower bound retains a maximizing pair, and the upper bound uses subadditivity of fractional powers."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("group-invariant-psi-component-coeff"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.componentCoeff"),
                H("Relative permutation overlap"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a group action on basis labels, sum p(i) to the power s times q(g i) to the power one minus s over all labels."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("group-invariant-psi-max-coeff"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.maxCoeff"),
                H("Largest relative overlap"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take the maximum of the relative permutation overlaps over the finite group."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("group-invariant-psi-limit"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.psi_eq_max"),
                H("The asymptotic logarithmic overlap"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For strictly positive p and q on a nonempty finite alphabet, the normalized logarithm of the tensor overlap converges, at each parameter strictly between zero and one, to log M. This is also the value of the selected limit psi. The sandwich bounds leave a correction of absolute size at most log k divided by n. Diagonal spectral calculus and the permutation twirl identity identify this scalar overlap with the original matrix trace expression. Probability normalization is not required for this convergence calculation."))), DescribeRole.Theorem))));
}
