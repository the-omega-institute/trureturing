using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.GibbsOverlap;

internal sealed class PetzQutritPhysicalRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A faithful two-flag qutrit refutes the conditional Gibbs root-fidelity bound.",
        H("A faithful counterexample to the conditional Gibbs root-fidelity inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("faithful-counterexample"),
                DeclarationHandle.Create(Module + "exists_faithful_qutrit_two_flag_petz_fidelity_failure"),
                H("The faithful partial-trace counterexample"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a qutrit with a two-valued classical flag, take ρ with blocks Q/2 and σ "
                    + "with blocks D₁/3 and D₂/3 from the strict two-flag deficit. Both joint "
                    + "states are positive definite with trace one. Their right partial traces "
                    + "are Q and I/3, respectively, and both are positive definite. Let G be the "
                    + "unnormalized conditional Gibbs operator and let P be ordinary Petz recovery "
                    + "against σ of the actual input marginal Q. Both G/(Re Tr G) and P "
                    + "are positive definite with trace one. The block deficit proves that "
                    + "their root fidelity is strictly less than √(Re Tr G)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conditional-gibbs-bound-refuted"),
                DeclarationHandle.Create(Module + "result"),
                H("The universal lower bound is false"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The claim asserts root fidelity at least √(Re Tr G) for all faithful "
                    + "trace-one joint inputs and references with faithful marginals on this "
                    + "qutrit–flag system. The faithful example gives its negation. "
                    + "The sharp constant for the trace-distance recovery inequality remains open."))),
                DescribeRole.Theorem))));
}
