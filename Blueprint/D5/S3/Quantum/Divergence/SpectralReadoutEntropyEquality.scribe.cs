using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class SpectralReadoutEntropyEqualityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Divergence/SpectralReadoutEntropyEquality.";

    public DocumentDefinition Create()
    {
        Formula n = F.Id("n"), u = F.Id("U"), x = F.Id("x");
        Formula conj = Call("conjugate", u, Call("diagonal", x));
        Formula readout = Call("diagonalPart", conj);

        return DocumentDefinition.Create(ScribeNode.Create(
            "A unitary readout keeps the Shannon entropy of a spectrum only in the diagonal case.",
            H("Spectral Readout Entropy Equality"),
            Blocks(
                Paragraph(Text(
                    "Matrices are complex and indexed by an arbitrary finite nonempty type n. "
                    + "U is unitary and x is a nonnegative real vector, read as a spectrum. "
                    + "diagonal(x) is the matrix carrying x on its diagonal, and conjugate(U, D) "
                    + "is U times D times the conjugate transpose of U. diagonalPart takes the "
                    + "real parts of the diagonal entries, which is the vector an observer reads "
                    + "off in the basis fixed by U. shannonEntropy is the natural-logarithm "
                    + "entropy of a nonnegative vector, with no normalization assumed.")),
                Describe.Lean(
                    DescribeId.Create("spectral-readout-entropy-equality"),
                    DeclarationHandle.Create(Owner + "spectral_readout_entropy_eq_iff_isDiag"),
                    H("Readout entropy equals spectral entropy exactly in the diagonal case"),
                    StatementSource.FromAuthor(Disp(All(
                        [Bound("n", F.Id("FiniteNonemptyType")),
                            Bound("U", Call("UnitaryGroup", n)),
                            Bound("x", Call("NonnegativeVector", n))],
                        Iff(
                            Eqn(Call("shannonEntropy", readout), Call("shannonEntropy", x)),
                            Call("IsDiag", conj))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The readout vector is the doubly stochastic image of the spectrum under "
                        + "the matrix of squared moduli of U, so its entropy is at least the "
                        + "spectral entropy. Equality forces every convex combination to be "
                        + "trivial, which pins each row of that matrix to a single unit entry, "
                        + "and the conjugated matrix is then diagonal. The converse direction is "
                        + "immediate because a diagonal conjugate reproduces the spectrum up to "
                        + "a permutation, and entropy does not see the order of its argument. "
                        + "No normalization, positive definiteness, or distinctness of the "
                        + "spectrum is assumed."))),
                    DescribeRole.Theorem))));
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
}
