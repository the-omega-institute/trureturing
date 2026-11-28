using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.GibbsOverlap;

internal sealed class PetzFlagPhysicalOverlapDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-flag Gibbs root fidelity is a normalized sum of block trace norms.",
        H("Conditional Gibbs and Petz overlap under the right partial trace"),
        Blocks(
            Paragraph(Text(
                "For a qutrit matrix Q and two effects Dᵢ summing to I, the joint input ρ has "
                + "blocks Q/2 and the joint reference σ has blocks Dᵢ/3. Write ρ_A and σ_A "
                + "for their right partial traces. For faithful joint states and marginals, "
                + "the conditional Gibbs operator is G = exp(log σ + lift(log ρ_A − log σ_A)), "
                + "where lift tensors with the flag identity. The normalized Gibbs state is "
                + "G/(Re Tr G).")),
            Entry("input-marginal", "input_marginal", "The input marginal is Q",
                "The right partial trace sums the two copies of Q/2."),
            Entry("reference-marginal", "reference_marginal", "The reference marginal is I/3",
                "The right partial trace sums Dᵢ/3 and the effects sum to I."),
            Entry("faithful-input", "input_faithful_density", "Faithfulness of the joint input",
                "When Q is positive definite with trace one, the joint input has both properties."),
            Entry("faithful-reference", "reference_faithful_density", "Faithfulness of the joint reference",
                "Positive definite effects summing to I give a positive definite, trace-one joint reference."),
            Entry("partition-trace", "gibbsOperator_trace", "The Gibbs trace is the sum of the block traces",
                "For positive definite effects summing to I and any qutrit matrix Q, "
                + "Re Tr G = Z, where Z = Σᵢ Re Tr Ωᵢ and Ωᵢ = exp(log Dᵢ + log Q). "
                + "On the faithful input domain, the scalar logarithm shifts from σ and σ_A cancel."),
            Entry("faithful-gibbs", "normalizedGibbs_faithful_density", "The normalized Gibbs state is faithful",
                "For positive definite effects summing to I and any qutrit matrix Q, "
                + "the normalized Gibbs operator is positive definite and has trace one. "
                + "Each block is the exponential of a self-adjoint matrix, and Z is positive."),
            Entry("faithful-recovery", "recovered_faithful_density", "The ordinary Petz output is faithful",
                "For positive definite effects summing to I and positive definite Q of trace one, "
                + "ordinary Petz recovery of ρ_A against σ has blocks √Dᵢ Q √Dᵢ. The output "
                + "is positive definite, and cycling the trace in each block gives total trace one."),
            Entry("strict-fidelity-equivalence", "rootFidelity_lt_sqrt_partition_iff",
                "The block deficit is equivalent to failure of the root-fidelity bound",
                "For positive definite effects summing to I and positive definite Q, root fidelity "
                + "between G/Z and the ordinary Petz output on ρ_A equals Σᵢ ‖Kᵢ‖₁/√Z, "
                + "where Kᵢ = √Ωᵢ √Dᵢ √Q. Thus it is strictly smaller than √Z exactly when "
                + "Σᵢ (‖Kᵢ‖₁ − Re Tr Ωᵢ) < 0.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string prose,
        DescribeRole role = DescribeRole.Lemma) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
