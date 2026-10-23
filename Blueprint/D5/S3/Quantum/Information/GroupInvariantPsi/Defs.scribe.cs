using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GroupInvariantPsi;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-group discrimination of faithful density matrices.",
        H("Tensor averages and asymptotic overlaps"), Blocks(
            Entry("tensorPower", "Tensor coordinates",
                "Words of length n index the tensor basis. The entry at two words is the product of the corresponding one-site matrix entries; the empty tensor has its single entry equal to one."),
            Entry("twirlPower", "Uniform conjugation average",
                "For a unitary representation of a finite group, average the conjugates of the tensor density matrix by the tensor representation with weight one divided by the group cardinality."),
            Entry("psiN", "Finite tensor overlap",
                "Take the real part of the trace of the product of the real spectral powers with exponents s and one minus s, and then its real logarithm. Spectral powers use the continuous functional calculus."),
            Entry("psi", "Asymptotic overlap",
                "The selected limit of the finite tensor overlap divided by the tensor length is used together with an explicit convergence hypothesis."),
            Entry("claim", "Differentiability assertion",
                "For every dimension, finite group and unitary representation, and every pair of positive definite complex matrices of trace one, convergence at every parameter strictly between zero and one is asserted to imply differentiability throughout that interval. Finite groups carry the discrete compact topology, and their normalized Haar measure is uniform. A failure in this domain therefore also gives a failure for compact groups."))));

    private static DocumentBlock Entry(string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create("group-invariant-psi-defs-" + declaration),
            DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/Defs." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
