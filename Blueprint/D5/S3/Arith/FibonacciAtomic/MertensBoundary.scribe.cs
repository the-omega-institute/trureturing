using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class MertensBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/MertensBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Power bounds for the seven-ten boundary and coprime Mertens sums.",
        H("The Seven-Ten Boundary and Mertens Power Bounds"),
        Blocks(
            Node("coprime-mertens", "Coprime Mertens sums", "coprimeMertens",
                CoprimeFormula(),
                "For every natural modulus R and real cutoff X, C(R,X) sums the integer "
                    + "Moebius function over positive natural numbers at most the natural floor "
                    + "of X and coprime to R. The natural floor is zero for negative inputs. "
                    + "Thus C(70,X) is the coprime Mertens sum, and C(1,X) is the ordinary "
                    + "Mertens sum M(X).", DescribeRole.Definition),
            Node("boundary", "The signed boundary interval", "boundary", BoundaryFormula(),
                "B(X) sums the same Moebius coefficients coprime to seventy over the real "
                    + "interval X/10 < n <= X/7. Its natural-index form uses the open-closed "
                    + "interval between the two natural floors. In particular, endpoints "
                    + "are retained with their stated strict and weak inequalities.",
                DescribeRole.Definition),
            Node("power-bounds", "Equivalent positive power bounds", "power_bounds_iff",
                ResultFormula(),
                "For every positive real exponent a, both equivalences hold as X tends to "
                    + "positive infinity through all real cutoffs. P(f,a) denotes "
                    + "Asymptotics.IsBigO atTop f (fun X => Real.rpow X a). The boundary is "
                    + "C(70,X/7)-C(70,X/10). Iterating the contraction q=7/10 until q^j X<1 "
                    + "gives a finite telescoping sum, bounded by a geometric series with "
                    + "ratio q^a<1. For a prime p coprime to R, splitting the Moebius sum "
                    + "according to divisibility by p gives C(R,X)=C(pR,X)-C(pR,X/p). "
                    + "The same contraction estimate, applied successively at p=2,5,7, "
                    + "relates the restricted and ordinary sums. These equivalences impose "
                    + "no Riemann hypothesis assumption and assert no Riemann hypothesis criterion.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula C(Formula r, Formula x) => Call("C", r, x);
    private static Formula CoprimeFormula()
    {
        var n = F.Id("n"); var x = F.Id("X"); var r = F.Id("R");
        return Disp(Equal(C(r, x), Seq(new Formula.Subscript(Sum,
            Seq(D(0), Lt, n, Le, new Formula.Floor(x), Comma,
                Call("gcd", n, r), Eq, D(1))), Call("mu", n))));
    }
    private static Formula BoundaryFormula()
    {
        var n = F.Id("n"); var x = F.Id("X");
        return Disp(Equal(Call("B", x), Seq(new Formula.Subscript(Sum,
            Seq(new Formula.Floor(new Formula.Fraction(x, D(1, 0))), Lt, n, Le,
                new Formula.Floor(new Formula.Fraction(x, D(7))), Comma,
                Call("gcd", n, D(7, 0)), Eq, D(1))), Call("mu", n))));
    }
    private static Formula ResultFormula()
    {
        var a = F.Id("a");
        Formula bound(Formula f) => Call("P", f, a);
        Formula restricted = Call("C", D(7, 0));
        Formula ordinary = Call("C", D(1));
        return Disp(Seq(Forall, a, InMacro, Seq(Mathbb, Grp(F.Id("R"))), Comma,
            D(0), Lt, a, Rightarrow,
            Open, bound(F.Id("B")), Leftrightarrow, bound(restricted), Close, Land,
            Open, bound(restricted), Leftrightarrow, bound(ordinary), Close));
    }
}
