using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Raney;

internal sealed class ExactPrimeRunsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef RaneySource =
        LibraryNoteRef.Create("D5/L/Recurrence/euhuangkao2026zerorun");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every prime p at least five, the exact maximal zero-run lengths of the literal R31 sequence are its distinct positive record lengths.",
        H("Exact R31 Runs at Every Prime at Least Five"),
        Blocks(
            Paragraph(Text(
                "This is the p≥5 branch of Theorem 2.1 of the repository theory input "
                + "RANEY_R31_EXACT_ZERO_RUN_RECORD_SPECTRA, attributed there to Haobo Ma and Wenlin Zhang. "
                + "The sequence is the existing raneyNumber(3,1,n), reduced in ZMod(p) after exact natural "
                + "division. A maximal run uses IsMaximalDeltaInterval with Delta={0}, including both "
                + "nonzero neighbors. The binary and ternary branches are separate mathematical obligations.")),
            Paragraph(Text(
                "Write A(q,j)=ceil(jq/3)=(jq+2) div 3, B(q,1)=(q−3) div 2, B(q,2)=q−1, "
                + "and ell(q,j)=B(q,j)+1−A(q,j), with natural subtraction and division. "
                + "All q in the result are p^m with m≥1; they are odd and congruent to one or five modulo six.")),
            Describe.Lean(
                DescribeId.Create("raney-prime-ge-five-exact-spectrum"),
                DeclarationHandle.Create("D5/S1/Recurrence/Raney/ExactPrimeRuns.raney_prime_ge_five_spectrum"),
                H("Complete maximal-run spectrum and first records"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(RaneySource),
                Blocks(
                    Paragraph(Text(
                        "For every prime p≥5 and every m≥1, put q=p^m. The interval with j=1 is "
                        + "[ceil(q/3),(q−3)/2], and that with j=2 is [ceil(2q/3),q−1]. The first interval "
                        + "is empty precisely at q=5 and q=7; the second is always nonempty. Every retained "
                        + "interval is an actual maximal run. Every earlier maximal run has strictly smaller "
                        + "length, so this interval is both the earliest occurrence of its length and a record, "
                        + "also under the source convention allowing tied records.")),
                    Paragraph(Text(
                        "Their lengths are ell(q,1)=(q−7)/6 for q congruent to one modulo six and "
                        + "(q−5)/6 for q congruent to five modulo six, and ell(q,2)=floor(q/3). Every actual "
                        + "maximal finite zero run has one of these retained lengths. The lengths strictly "
                        + "increase with m and, within each scale, from j=1 to j=2. Thus there are no "
                        + "duplicate retained values for a fixed prime, and the complete positive maximal-run "
                        + "and distinct positive record spectra coincide. All primes, exponents and interval "
                        + "endpoints are unbounded.")),
                    Paragraph(Text(
                        "The proof derives raneyNumber(3,1,n)·n!·(2n+1)!=(3n)! from adjacent binomial "
                        + "identities and the literal quotient. Legendre's theorem then gives its p-adic "
                        + "valuation as the finite sum of f_(p^h)(n mod p^h), where "
                        + "f_q(x)=floor(3x/q)−floor((2x+1)/q). For x<q and q≥2 each summand is zero or one. "
                        + "The residue is zero exactly when some positive scale has summand one; scales "
                        + "beyond a sufficiently large power vanish. The proof does not assume a zero mask.")),
                    Paragraph(Text(
                        "For q=p^m, solving f_q(x)=1 gives exactly the two displayed intervals. At each "
                        + "left neighbor, 3n+s=jq for s=1 or 2. At the first right neighbor, 2n+1=q; "
                        + "the second right neighbor is q. Reduction to every dividing lower scale makes "
                        + "its summand zero, and every higher summand vanishes by 3n+1<p^(m+1). "
                        + "These calculations prove both endpoint nonvanishing assertions.")),
                    Paragraph(Text(
                        "Induct on the prime-power prefix. An actual run meeting a new scale interval "
                        + "equals it, since two maximal intervals sharing an index have equal endpoints. "
                        + "A disjoint run has no top-scale contribution. It cannot cross a multiple of "
                        + "the preceding power, where all lower contributions vanish. Taking its residues "
                        + "modulo that power produces an actual smaller-prefix run of equal length. "
                        + "The induction also proves that its start is no earlier than the unshifted "
                        + "witness for that length. This proves component completeness. Exact rounding "
                        + "and p≥5 give strict length growth, which excludes an equally long earlier run."))),
                DescribeRole.Theorem))));

    private static Formula V(string n) => F.Id(n);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string f, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(f))), [.. xs]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Rightarrow, Sp, Par(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Par(a), Sp, Leftrightarrow, Sp, Par(b));
    private static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula And(params Formula[] xs)
    {
        Formula r = Par(xs[0]);
        for (var i = 1; i < xs.Length; i++) r = Seq(r, Sp, Land, Sp, Par(xs[i]));
        return r;
    }
    private static Formula All(string n, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), N(), b);
    private static Formula Ex(string n, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), N(), b);
    private static Formula Valid(Formula j) => Or(Eqn(j, D(1)), Eqn(j, D(2)));
    private static Formula A(Formula q, Formula j) => Call("A", q, j);
    private static Formula B(Formula q, Formula j) => Call("B", q, j);
    private static Formula Len(Formula q, Formula j) => Call("ell", q, j);
    private static Formula Run(Formula a, Formula b) => Call("IsMaximalDeltaInterval",
        Call("singleton", D(0)), Call("raneyResidue", D(3), D(1), V("p")), a, b);
    private static Formula Div(Formula a, byte b) => Call("NatDiv", a, D(b));

    private static Formula ResultFormula()
    {
        var p = V("p"); var m = V("m"); var h = V("h");
        var j = V("j"); var k = V("k"); var q = Pow(p, m);
        var a = V("a"); var b = V("b"); var c = V("c"); var d = V("d");
        var length = Call("ite", Eqn(j, D(1)),
            Call("ite", Eqn(Call("mod", q, D(6)), D(1)), Div(Sub(q, D(7)), 6), Div(Sub(q, D(5)), 6)),
            Div(q, 3));
        var witnesses = All("m", Imp(Le(D(1), m), All("j", Imp(Valid(j), And(
            Iff(Le(A(q, j), B(q, j)), Or(Eqn(j, D(2)), And(Ne(q, D(5)), Ne(q, D(7))))),
            Eqn(Len(q, j), length),
            Imp(Le(A(q, j), B(q, j)), And(Run(A(q, j), B(q, j)),
                All("c", All("d", Imp(And(Run(c, d), LtF(c, A(q, j))),
                    LtF(Sub(Add(d, D(1)), c), Len(q, j))))))))))));
        var complete = All("a", All("b", Imp(Run(a, b), Ex("m", Ex("j", And(
            Le(D(1), m), Valid(j), Le(A(q, j), B(q, j)),
            Eqn(Sub(Add(b, D(1)), a), Len(q, j))))))));
        var order = All("m", All("h", All("j", All("k", Imp(And(
            Le(D(1), m), Le(D(1), h), Valid(j), Valid(k),
            Or(LtF(m, h), And(Eqn(m, h), LtF(j, k)))), LtF(Len(q, j), Len(Pow(p, h), k)))))));
        return Disp(All("p", Imp(And(Call("Prime", p), Le(D(5), p)), And(witnesses, complete, order))));
    }
}
