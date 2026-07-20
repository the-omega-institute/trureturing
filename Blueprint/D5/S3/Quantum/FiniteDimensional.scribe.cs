using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class FiniteDimensionalDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Schwinger =
        LibraryNoteRef.Create("D5/L/schwinger1960unitary");
    private static readonly LibraryNoteRef Murphy =
        LibraryNoteRef.Create("D5/L/murphy1990calgebras");
    private static readonly LibraryNoteRef Gleason =
        LibraryNoteRef.Create("D5/L/gleason1957measures");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Quantum/FiniteDimensional",
            "Finite-dimensional Pauli, no-character, and trace-probability skeletons."),
        H("Finite-Dimensional Quantum Skeletons"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("the-standard-qubit-weyl-pair-has-the-pauli-star-skeleton"),
                DescribeKind.Theorem,
                H("The standard qubit Weyl pair has the Pauli star skeleton"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/FiniteDimensional.qubit_weyl_star")),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "The standard two-dimensional Pauli X and Z matrices anticommute, are self-adjoint, and square to the identity. This is only the d = 2 Weyl specialization: it does not identify an arbitrary observer window with a full matrix algebra, prove prime-power tensor factorization or a general qudit relation, or derive the structure from a classical ontology. Original numerical-certificate claim not formalized: the source atom's matrix-unit relations with exact zero certificate error."))),
                LatexStatement.Create(@"$ZX=-(XZ) \land X^{*}=X \land Z^{*}=Z \land X^{2}=I \land Z^{2}=I$")),
            new DocumentBlock.Describe(
                DescribeId.Create("the-qubit-matrix-algebra-has-no-complex-algebra-character"),
                DescribeKind.Theorem,
                H("The qubit matrix algebra has no complex-algebra character"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/FiniteDimensional.qubit_matrix_algebra_has_no_character")),
                DescribeProvenance.LiteratureAttested(Murphy),
                Blocks(Paragraph(
                    Text("No unital complex-algebra homomorphism from the two-by-two full matrix algebra to the complex numbers exists. The proof uses the stronger global additive and multiplicative laws of an algebra character. "),
                    Ref("D5/L/kochen1968problem"),
                    Text(" is contextual background only: this declaration is not the Kochen-Specker valuation theorem, does not exclude qubit noncontextual projection valuations, and proves neither the arbitrary M_n result for n greater than one nor any CHSH, hidden-address, or probability-is-not-ignorance claim."))),
                LatexStatement.Create(@"$\operatorname{IsEmpty}(\operatorname{QubitMatrix}\to_{\mathbb{C}\text{-alg}}\mathbb{C})$")),
            new DocumentBlock.Describe(
                DescribeId.Create("positive-trace-one-matrices-give-nonnegative-projection-weights"),
                DescribeKind.Theorem,
                H("Positive trace-one matrices give nonnegative projection weights"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/FiniteDimensional.born_probability_skeleton")),
                DescribeProvenance.LiteratureAttested(Gleason),
                Blocks(Paragraph(
                    Text("For a positive semidefinite finite complex matrix rho with trace one, P maps to trace(rho P), is normalized at the identity, is additive, and is nonnegative for every self-adjoint idempotent P. Positivity follows from the compression P rho P* and does not assume that rho commutes with P. "),
                    Ref("D5/L/born1926zur"),
                    Text(" records the historical Born context only. The declaration proves no Gleason representation or uniqueness theorem, no rank-one pure-state modulus-square reduction, no ledger-derived noncontextuality, no harmonic or quartic numerical certificate, and no forced classical-to-quantum origin. Original numerical-certificate claim not formalized: the source atom's separate Born control group balance to 10^-16."))),
                LatexStatement.Create(@"$$\forall n\ [\operatorname{Fintype}(n)]\ [\operatorname{DecidableEq}(n)],\ \forall \rho \in M_{n}(\mathbb{C}),\ \operatorname{PosSemidef}(\rho) \land \operatorname{tr}(\rho)=1 \Rightarrow \operatorname{bornProbability}(\rho,I)=1 \land (\forall P,Q,\ \operatorname{bornProbability}(\rho,P+Q)=\operatorname{bornProbability}(\rho,P)+\operatorname{bornProbability}(\rho,Q)) \land (\forall P,\ P^{*}=P \Rightarrow P^{2}=P \Rightarrow 0\leq\operatorname{bornProbability}(\rho,P))$$")))));
}
