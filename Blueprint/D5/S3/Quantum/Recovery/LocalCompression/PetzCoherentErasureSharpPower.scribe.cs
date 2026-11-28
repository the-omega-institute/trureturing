using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class PetzCoherentErasureSharpPowerDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three physical flags give the exact Bures square of the ordinary Petz outputs.",
        H("Sharp half power for coherent erasure"),
        Blocks(
            Paragraph(Text(
                "Dephase the environment of the coherent reference. Compute the ordinary Petz "
                + "output from the dephased reference and also transport the original output "
                + "by the same three-flag channel.")),
            Entry("physical-dephasing", "dephase_is_channel", "Physical dephasing channel",
                "The three orthogonal flag projectors are Kraus operators of the dephasing channel."),
            Entry("coherent-reference-root", "sqrt_sigma", "Positive root of the coherent reference",
                "The coherent rank-one part and the third-flag part have orthogonal supports."),
            Entry("dephased-reference-root", "sqrt_dephase_sigma", "Positive root of the dephased reference",
                "The matrix square root is the block diagonal of the three positive qubit roots."),
            Entry("transported-benchmark", "Y0_eq", "Three blocks of the transported ordinary Petz output",
                "With p = ε/(1 + ε) and 0 < ε < 1, the first two conditional projectors have weight p/2 each. "
                + "The third block is M/4."),
            Entry("recomputed-benchmark", "Y1_eq", "Three blocks of the recomputed ordinary Petz output",
                "The first block is zero, the second conditional projector has weight p, "
                + "and the third block is M/4."),
            Entry("benchmark-densities", "Y0_Y1_density", "Both benchmarks are density matrices",
                "The blocks are positive semidefinite and their weights sum to one for each output."),
            Entry("paired-defect", "Gamma_eq", "Exact paired defect",
                "Pairing the matrix difference with the lifted retained likelihood gives Γ = 2p²."),
            Entry("quantum-root-fidelity", "rootFidelity_Y0_Y1", "Exact quantum root fidelity",
                "The two positive matrix roots in the fidelity formula give contributions "
                + "0, p/√2, and 1 − p from the three flags."),
            Entry("bures-square", "bures_sq_Y0_Y1", "Exact squared Bures distance",
                "The trace-one Bures convention gives d_B² = 2p(1 − 1/√2)."),
            Entry("sharp-half-power", "bures_sq_eq_sqrt_Gamma", "Equality at the half power",
                "The identity d_B² = (√2 − 1)√Γ holds throughout the family. "
                + "As ε tends to zero, Γ tends to zero and the positive ratio stays fixed."),
            Entry("optimal-one-copy-test", "one_copy_label_test_optimal", "Optimal one-copy label test",
                "Guess the transported benchmark exactly on the first flag. "
                + "The equal-prior error is (1 − p/2)/2 and is minimal over binary effects."))));

    private static DocumentBlock Entry(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
