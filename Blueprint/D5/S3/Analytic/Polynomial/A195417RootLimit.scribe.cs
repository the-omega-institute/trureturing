using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class A195417RootLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/A195417RootLimit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/hanna2011a195417");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete absolute coefficient sum of (1+X-X cubed) to power n has root limit sqrt((97+26 sqrt(13))/27).",
        H("The absolute coefficient root limit in OEIS A195417"),
        Blocks(
            Paragraph(Text("The polynomial p has integer coefficients. For each natural n, including zero, a(n) sums the natural absolute values "
                + "of every coefficient of p to power n at indices zero through 3n. Coefficients outside that interval vanish. "
                + "The cast to the reals occurs after this complete sum. Powers with exponent 1/(n:R) use real rpow; the limit is along all natural numbers.")),
            Entry("p", "The original integer polynomial", Equal(Cast(V("p"), Call("Polynomial", Integers())),
                Sub(Add(D(1), V("X")), Pow(V("X"), D(3)))),
                "No coefficient normalization or substitution changes the sequence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("a", "The original complete coefficient sum", SequenceFormula(),
                "The range 3n+1 includes both endpoints zero and 3n. natAbs is the absolute value of an integer as a natural number. "
                + "At n=0 the polynomial is one and the sum is one. Mapping the integer polynomial to the complex numbers preserves "
                + "each coefficient and converts its natural absolute value, after a real cast, to its complex norm. "
                + "The degree bound 3n identifies the padded sum with the entire support sum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("result", "The complete real root limit", LimitFormula(),
                "Put s=sqrt(13), C=(97+26s)/27 and M=sqrt(C). For a unit complex number z, let u=Re(z). "
                + "Then the squared modulus of p(z) is f(u)=5+8u-4u squared-8u cubed. The identity "
                + "C-f(u)=(6u+1-s) squared times (6u+1+2s)/27 proves f(u) is at most C: u is at least -1 and s is at least 5/2, "
                + "so both factors on the right are nonnegative. Equality holds when u=(-1+s)/6 and "
                + "z=u+i sqrt(1-u squared). This u lies between -1 and 1, so z has norm one. "
                + "The original CountableHankelNegativeWitness.eval_bound applied to the real image of p to power n at this z "
                + "gives M to power n at most a(n). The generic power_sum_sq_le in A192205RootLimit uses Parseval and "
                + "Cauchy-Schwarz to bound a(n) squared by the number of support indices times M to power 2n. "
                + "There are at most 3n+1 indices, giving a(n) at most (3n+1) M to power n. For n at least one, "
                + "taking real powers 1/n bounds the root between M and (3n+1) to power 1/n times M. "
                + "The original degree_root_limit in A192205RootLimit makes that extra factor tend to one. "
                + "The squeeze theorem proves the full natural-index limit. This result answers only the first root-limit question; "
                + "it makes no assertion about successive ratios or their attractors.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Entry(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a195417-root-limit-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Cast(Formula f, Formula t) => Par(Seq(f, Colon, Sp, t));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula Constant() => Seq(Sqrt, Grp(new Formula.Fraction(
        Add(D(9,7), Mul(D(2,6), Seq(Sqrt, Grp(D(1,3))))), D(2,7))));
    private static Formula SequenceFormula()
    {
        var n = V("n");
        var i = V("i");
        var indices = Call("range", Add(Mul(D(3), n), D(1)));
        var summand = Call("natAbs", Call("coeff", Pow(V("p"), n), i));
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(i, Sp, InMacro, Sp, indices)), Sp, summand);
        return Seq(Forall, Sp, n, Colon, Naturals(), Comma, Sp, Equal(Call("a", n), sum));
    }
    private static Formula LimitFormula()
    {
        var n = V("n");
        var root = Pow(Cast(Call("a", n), Reals()), new Formula.Fraction(D(1), Cast(n, Reals())));
        var function = Par(Seq(V("fun"), Sp, Par(Seq(n, Colon, Naturals())), Sp, Mapsto, Sp, root));
        return Call("Tendsto", function, Call("atTop"), Call("nhds", Constant()));
    }
}
