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
                Blocks(Paragraph(Text("Let two nonnegative finite families have the same nonzero number k of components, and let s lie strictly between zero and one. If R is the greatest overlap between a component of one family and a component of the other, the overlap of their uniform mixtures lies between R/k and kR. The lower bound retains a maximizing component pair. The upper bound expands the two fractional powers by subadditivity and sums all k squared component pairs."))),
                DescribeRole.Theorem))));
}
