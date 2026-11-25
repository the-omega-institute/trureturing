using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class EqualChoiGramRecoverySeparationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two explicit four-dimensional channels share an exact Choi Gram and have unequal optimal recovery fidelity.",
        H("Equal branch Choi Gram and unequal recovery fidelity"),
        Blocks(
            Entry("example-a", "exampleA_exact", "Optimal score 3/4 for the conjugate pair",
                "In dimension four, the equally weighted branches are the identity and W_A with diagonal (exp(iπ/3), exp(iπ/3), exp(−iπ/3), exp(−iπ/3)). "
                + "Every actual CPTP decoder scores at most 3/4. The diagonal decoder whose entries align 1+conj(z) at the corresponding diagonal entries z attains 3/4. "
                + "The dual bound groups the two repeated conjugate phases and applies Cauchy–Schwarz."),
            Entry("example-b", "exampleB_exact", "Optimal score 3/8 + √2/4 for the second pair",
                "The second equally weighted channel has branches the identity and W_B = diag(1,1,i,−i). Every actual CPTP decoder scores at most 3/8 + √2/4. "
                + "The same phase rule on these entries attains this value. In the dual bound, the two entries equal to one contribute at most 2 and the two imaginary entries contribute at most √2 before squaring and dividing by 16."),
            Entry("exact-gram", "equal_branch_choi_gram", "Equality of the exact normalized branch Choi Grams",
                "The branch vector for a unitary U is (U ⊗ I) times the normalized canonical maximally entangled vector. "
                + "Both relative unitaries have trace two, so the two exact unweighted two-by-two Grams have ones on the diagonal and 1/2 off the diagonal, in identity-then-unitary order."),
            Entry("strict-separation", "equal_gram_strict_recovery_separation", "One exact Gram has two different optimal scores",
                "The two normalized branch Choi Grams are equal. Every CPTP decoder for channel B scores strictly below the explicit unitary decoder for channel A, since 3/8 + √2/4 < 3/4. "
                + "The score is single-use canonical entanglement fidelity at I/4 with the reference untouched."))));

    private static DocumentBlock Entry(string id, string name, string title, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);
}
