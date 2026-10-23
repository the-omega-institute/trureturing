using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GroupInvariantPsi;

internal sealed class MixtureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal tensor states under permutation representations.",
        H("Classical finite mixtures"), Blocks(
            Entry("permutationRepresentation", "Permutation representation", DescribeRole.Definition,
                "A group action on basis labels gives a unitary representation by the inverse permutation matrices. This convention sends a diagonal entry at a label to the entry at its inverse image."),
            Entry("mixtureWeight", "Word probabilities", DescribeRole.Definition,
                "For each word, average over the group the product of its one-site probabilities evaluated at inverse images of its labels."),
            Entry("mixtureTrace", "Classical overlap", DescribeRole.Definition,
                "Sum over all words the product of the first mixture probability to power s and the second mixture probability to power one minus s."),
            Entry("twirlPower_diag", "Diagonal tensor average", DescribeRole.Theorem,
                "For any finite group acting on the basis labels, the uniform tensor twirl of a real diagonal matrix equals the diagonal matrix of the classical word mixture. Tensor permutation matrices reindex both matrix coordinates. Their diagonal tensor entries are products of one-site entries, so averaging gives the stated word probabilities, including tensor length zero."),
            Entry("trace_pow_diag", "Spectral trace overlap", DescribeRole.Theorem,
                "The real part of the trace of the product of the CFC powers of two real diagonal matrices is the sum of the corresponding products of scalar real powers. The existing diagonal functional-calculus theorem supplies both powers."))));

    private static DocumentBlock Entry(string declaration, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("group-invariant-psi-mixture-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/Mixture." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
