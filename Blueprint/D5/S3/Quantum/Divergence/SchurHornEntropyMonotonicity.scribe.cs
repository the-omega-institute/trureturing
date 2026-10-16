using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class SchurHornEntropyMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/SchurHornEntropyMonotonicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unitary spectral readout cannot decrease finite Shannon entropy.",
        H("Schur--Horn Shannon Entropy Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spectral-readout-shannon-entropy-monotone"),
                DeclarationHandle.Create(Prefix + "spectral_readout_entropy_le"),
                H("Unitary spectral readout cannot decrease Shannon entropy"),
                StatementSource.FromAuthor(Disp(ReadoutFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite index type n, a unitary matrix U, and a nonnegative real "
                            + "spectrum x, form U diagonal(x) U* and read the real parts of its "
                            + "diagonal entries. The readout vector is the squared-entry-norm "
                            + "matrix of U applied to x.")),
                    Paragraph(Text(
                        "The squared-entry-norm matrix is doubly stochastic. Row-wise Jensen for "
                            + "the convex function t log t, followed by the column-sum identity, "
                            + "shows that the readout's x log x sum is no larger than the spectral "
                            + "sum. Negating gives the Shannon entropy inequality.")),
                    Paragraph(Text(
                        "This is the finite Schur--Horn bridge used by the later pinching and "
                            + "Klein targets. No normalization, strict positivity, or distinct "
                            + "eigenvalue assumption is required."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ReadoutFormula()
    {
        Formula n = F.Id("n");
        Formula unitary = F.Id("U");
        Formula spectrum = F.Id("x");
        Formula conjugate = Call("conjugate", unitary, Call("diagonal", spectrum));
        Formula readout = Call("diagonalPart", conjugate);
        Formula assumptions = Seq(
            Call("FiniteType", n), Sp, Land, Sp,
            Call("Unitary", unitary), Sp, Land, Sp,
            Call("Nonnegative", spectrum));

        return Seq(
            Forall, Sp, n, Comma, Sp, unitary, Comma, Sp, spectrum, Comma, Sp,
            assumptions, Sp, Rightarrow, Sp,
            Call("shannonEntropy", spectrum), Sp, Le, Sp,
            Call("shannonEntropy", readout), Dot);
    }
}
