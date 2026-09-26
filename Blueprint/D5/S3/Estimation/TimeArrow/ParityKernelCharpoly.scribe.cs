using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class ParityKernelCharpolyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A parity kernel on the sign hypercube whose profile a satisfies E a = 0 and E[chi a] = 0 has "
            + "characteristic polynomial (X - 1) X^(2^d - 1).",
        H("Characteristic Polynomial of Balanced Parity Kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parity-kernel-charpoly"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/TimeArrow/ParityKernelCharpoly.charpoly_parityKernel"),
                H("Characteristic polynomial of a balanced parity kernel"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sum, Underscore, Grp(F.Id("y")), Sp, Call("a", F.Id("y")), Eq, D(0), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("y")), Sp, Call("chi", F.Id("y")), Sp, Call("a", F.Id("y")),
                    Eq, D(0), Sp, Rightarrow, Sp,
                    Call("charpoly", Sub(F.Id("P"), F.Id("a"))), Eq, Sp,
                    Open, F.Id("X"), Minus, D(1), Close, Sp,
                    F.Id("X"), Caret, Grp(D(2), Caret, Grp(F.Id("d")), Minus, D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let d >= 1 and let a be a real profile on the sign hypercube {-1, 1}^d with "
                            + "sum a = 0 and sum chi a = 0. The kernel matrix P_a(x, y) = (1 + a(x) chi(y)) / 2^d "
                            + "has characteristic polynomial (X - 1) X^(2^d - 1): the eigenvalue 1 is simple and "
                            + "all other eigenvalues vanish with full algebraic multiplicity.")),
                    Paragraph(Text(
                        "The kernel is the rank-two product U V with U = [1, a] / 2^d, a 2^d by 2 matrix, and "
                            + "V = [1, chi] transposed. The reversed product V U is the 2 by 2 matrix with entries "
                            + "E 1 = 1, E a = 0, E chi = 0 and E[chi a] = 0, that is diag(1, 0). The parity sum "
                            + "E chi = 0 is the instance a = 1, b = 0 of two-step uniform mixing. The "
                            + "Weinstein-Aronszajn identity for characteristic polynomials of rectangular "
                            + "products then gives X^(2^d - 2) (X^2 - X)."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) result.AddRange([Comma, Sp]);
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }

    private static Formula Sub(Formula name, Formula index) => Seq(name, Underscore, Grp(index));
}
