using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class A192205RootLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/A192205RootLimit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/hanna2011a192205");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete absolute coefficient sum of (1-X-X squared+X cubed) to power n has root limit 16 sqrt(3)/9.",
        H("The absolute coefficient root limit in OEIS A192205"),
        Blocks(
            Paragraph(Text("The polynomial p has integer coefficients. For each natural n, including zero, a(n) sums the natural absolute values "
                + "of every coefficient of p to power n at indices zero through 3n. Coefficients outside that interval vanish. "
                + "The cast to the reals occurs after this complete sum. Powers with exponent 1/(n:R) use real rpow; the limit is along all natural numbers.")),
            Entry("p", "The original integer polynomial", Equal(Cast(V("p"), Call("Polynomial", Integers())),
                Add(Sub(Sub(D(1), V("X")), Pow(V("X"), D(2))), Pow(V("X"), D(3)))),
                "The polynomial factors as (1-X) squared times (1+X). No coefficient normalization or substitution changes the sequence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("a", "The original complete coefficient sum", SequenceFormula(),
                "The range 3n+1 includes both endpoints zero and 3n. natAbs is the absolute value of an integer as a natural number. "
                + "At n=0 the polynomial is one and the sum is one. Mapping the integer polynomial to the complex numbers preserves "
                + "each coefficient and converts its natural absolute value, after a real cast, to its complex norm. "
                + "The degree bound 3n identifies the padded sum with the entire support sum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("result", "The complete real root limit", LimitFormula(),
                "Put M=16 sqrt(3)/9 and write u=Re(z) for a unit complex number z. The squared modulus of p(z) is "
                + "8(1-u) squared times (1+u). Its difference from 256/27 is "
                + "8(3u+1) squared times (5-3u)/27, which is nonnegative since u is at most one. "
                + "Thus the modulus is at most M. Equality holds at z=-1/3+(2 sqrt(2)/3)i, whose norm is one. "
                + "The original CountableHankelNegativeWitness.eval_bound applied to the real image of p to power n at this z "
                + "gives M to power n at most a(n). Parseval identifies the sum of squared complex coefficient norms with "
                + "the unit-circle average of the squared modulus. The bound M on p yields a square sum at most M to power 2n. "
                + "Cauchy-Schwarz and at most 3n+1 support indices give a(n) squared at most (3n+1) M to power 2n. "
                + "In particular a(n) is at most (3n+1) M to power n. For n at least one, taking real powers 1/n bounds "
                + "the root between M and (3n+1) to power 1/n times M. That extra factor tends to one. "
                + "The squeeze theorem proves the stated full limit, with no sign assumption on the coefficients. "
                + "The squared-coefficient binomial observation in the source is not assumed or asserted here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a192205-absolute-coefficient-root-limit"), ResolutionKind.Proved)))));

    private static DocumentBlock Entry(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a192205-root-limit-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
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
    private static Formula Constant() => new Formula.Fraction(Mul(D(1,6), Seq(Sqrt, Grp(D(3)))), D(9));
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
