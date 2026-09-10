using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class GibbsVariationalIdentityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Divergence/GibbsVariationalIdentity.";

    public DocumentDefinition Create()
    {
        Formula n = F.Id("n"), h = F.Id("H"), rho = Rho;
        Formula z = Call("partitionFunction", h), g = Call("gibbsState", h);
        Formula General(Formula body) => All(
            [Bound("n", F.Id("FiniteNonemptyType")),
                Bound("H", Call("HermitianMatrix", n)),
                Bound("rho", Call("DensityState", n))], body);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The normalized matrix exponential gives an exact entropy decomposition.",
            H("Gibbs Variational Identity"),
            Blocks(
                Paragraph(Text(
                    "Matrices are complex and indexed by an arbitrary finite nonempty type n. "
                    + "H is Hermitian. DensityState means a positive semidefinite matrix with "
                    + "complex trace one. ReTr is the real part of the matrix trace. "
                    + "partitionFunction(H) is ReTr(exp(H)) and is strictly positive; "
                    + "gibbsState(H) is its inverse scalar times exp(H), a positive definite "
                    + "density matrix. Every logarithm is natural and the matrix logarithm "
                    + "is Mathlib's spectral continuous functional calculus.")),
                Describe.Lean(
                    DescribeId.Create("spectral-logarithm-of-gibbs-state"),
                    DeclarationHandle.Create(Owner + "log_gibbs_state"),
                    H("Logarithm of the Gibbs state"),
                    StatementSource.FromAuthor(Disp(All(
                        [Bound("n", F.Id("FiniteNonemptyType")),
                            Bound("H", Call("HermitianMatrix", n))],
                        Eqn(Call("log", g), Sub(h, Mul(Call("log", z), F.Id("I"))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The logarithm of a positive scalar multiple separates into a scalar "
                        + "logarithm and the matrix logarithm. The logarithm of the exponential "
                        + "of a Hermitian matrix is the original matrix."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("gibbs-variational-identity"),
                    DeclarationHandle.Create(Owner + "gibbs_variational_identity"),
                    H("Gibbs entropy decomposition"),
                    StatementSource.FromAuthor(Disp(General(Eqn(Call("log", z),
                        Add(Add(Call("ReTr", Mul(h, rho)), Call("vonNeumannEntropy", rho)),
                            Call("quantumRelativeEntropy", rho, g)))))),
                    AssessedProvenance.FromLiterature(
                        LibraryNoteRef.Create("D5/L/Quantum/goold2016thermodynamics")),
                    Blocks(Paragraph(Text(
                        "Expanding relative entropy cancels the self-logarithm term against "
                        + "von Neumann entropy. Substitution of the Gibbs logarithm, trace "
                        + "normalization, and cyclicity of the trace give the equality. "
                        + "The density matrix may fail to commute with H."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("entropy-relative-to-uniform-state"),
                    DeclarationHandle.Create(Owner + "entropy_uniform_identity"),
                    H("The maximally mixed reference state"),
                    StatementSource.FromAuthor(Disp(All(
                        [Bound("n", F.Id("FiniteNonemptyType")),
                            Bound("rho", Call("DensityState", n))],
                        Eqn(Add(Call("vonNeumannEntropy", rho),
                            Call("quantumRelativeEntropy", rho, Call("gibbsState", Num(0)))),
                            Call("log", Call("card", n)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At H = 0 the partition function is card(n), and gibbs_state_zero "
                        + "identifies the Gibbs matrix with I/card(n). Substitution into the "
                        + "general identity gives entropy plus relative entropy to the "
                        + "maximally mixed state equal to log(card(n))."))),
                    DescribeRole.Theorem))));
    }
}
