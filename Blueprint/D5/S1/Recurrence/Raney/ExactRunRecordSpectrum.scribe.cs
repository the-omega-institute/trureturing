using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Raney;

internal sealed class ExactRunRecordSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.";
    private static readonly LibraryNoteRef RaneySource =
        LibraryNoteRef.Create("D5/L/Recurrence/euhuangkao2026zerorun");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every prime, the complete positive maximal zero-run length set and the distinct tied-record value set of the literal R31 sequence equal the displayed strictly ordered families.",
        H("Exact All-Prime R31 Run and Record Spectra"),
        Blocks(
            Paragraph(Text(
                "This is the complete Theorem 2.1 of RANEY_R31_EXACT_ZERO_RUN_RECORD_SPECTRA, attributed "
                + "there to Haobo Ma and Wenlin Zhang. The residue sequence is always the existing "
                + "raneyNumber(3,1,n) in ZMod(p): the natural quotient is taken before reduction. Write "
                + "rho(p) for this sequence and Run(rho,a,b) for IsMaximalDeltaInterval({0},rho,a,b). "
                + "This includes a<=b, zeros at every index from a through b, a nonzero right neighbor, "
                + "and either a=0 or a nonzero left neighbor. The actual value at zero is one.")),
            Paragraph(Text(
                "Every length here is the natural number b+1-a. In particular an empty displayed interval "
                + "with a=b+1 has length zero; it never receives the spurious length one from (b-a)+1. "
                + "A weak record compares with every earlier actual run and permits ties. First occurrence "
                + "compares starts of all actual runs of that same length. The theorem concerns record "
                + "values: it does not assert that every occurrence of a length is itself a record.")),
            Node("IsWeakZeroRunRecord", "Tied left-to-right record", RecordFormula(false),
                "For any residue sequence rho:N->ZMod(p), this predicate includes actual maximality "
                + "and weak domination of the length of every maximal run starting earlier.", DescribeRole.Definition),
            Node("IsFirstZeroRunLength", "First occurrence of a run length", RecordFormula(true),
                "For any rho, this predicate includes actual maximality and says no run of equal "
                + "length has a smaller starting index.", DescribeRole.Definition),
            Node("positiveZeroRunLengths", "Positive maximal-run length set", SetFormula(false),
                "Membership means positive length and an actual finite nonempty maximal zero interval "
                + "of that length; endpoints range over all natural numbers.", DescribeRole.Definition),
            Node("positiveZeroRunRecordValues", "Distinct positive weak-record values", SetFormula(true),
                "Membership means positive length and an actual weak record of that length. Set "
                + "membership lists each tied value only once.", DescribeRole.Definition),
            Node("runSpectrumRetained", "Exact retained exponent and interval domains", RetainedFormula(),
                "For p=2 use m>=2 and j=1; for p=3 use m>=1 and j=1. Otherwise require p>=5, "
                + "m>=1 and j=1 or 2, retaining j=1 exactly when p^m is neither five nor seven. "
                + "No additional coprimality condition is present.", DescribeRole.Definition),
            Node("runSpectrumStart", "Displayed interval starts", NumericFormula(0),
                "The starts are ceil(2^(m+1)/3), (3^m+1)/2, and ceil(j*p^m/3), respectively. "
                + "All divisions in the formula are natural divisions.", DescribeRole.Definition),
            Node("runSpectrumLast", "Displayed interval ends", NumericFormula(1),
                "The ends are 2^m-1, (3^(m+1)-3)/2, and, for p>=5, (p^m-3)/2 at j=1 "
                + "or p^m-1 at j=2.", DescribeRole.Definition),
            Node("runSpectrumLength", "Exact branch length formulas", NumericFormula(2),
                "The values are floor(2^m/3), 3^m-1, and, for p>=5, (q-7)/6 if j=1 and "
                + "q mod 6=1, (q-5)/6 if j=1 and q mod 6=5, or floor(q/3) if j=2. For the "
                + "prime powers in scope, these are the only two residues modulo six.", DescribeRole.Definition),
            Paragraph(Text(
                "In the final formula abbreviate the displayed functions by A(p,m,j), B(p,m,j), "
                + "L(p,m,j) and Ret(p,m,j). Define Values(p)={l in N : there exist m,j in N with "
                + "Ret(p,m,j) and l=L(p,m,j)}. These are not extra hypotheses or a supplied branch "
                + "certificate: all the following conclusions are proved for the literal sequence.")),
            Node("raney_all_prime_exact_run_record_spectrum", "Complete all-prime theorem", ResultFormula(),
                "The two complete positive sets both equal Values(p). Every retained interval is an "
                + "actual maximal run, has its stated strictly positive length, is a first occurrence "
                + "and is a weak record. Lengths strictly increase in exponent-then-interval order, "
                + "and equality of retained lengths forces equality of both indices. At p>=5, the "
                + "displayed nonemptiness equivalence proves exactly the omissions I1(5) and I1(7).",
                DescribeRole.Theorem,
                Paragraph(Text(
                    "The proof directly consumes raney_binary_exact_zero_run_spectrum, "
                    + "raney_three_exact_zero_runs and ExactPrime.raney_prime_ge_five_spectrum. "
                    + "Prime trichotomy is proved internally. The binary and larger-prime witnesses "
                    + "are strictly longer than every earlier actual run. At three, the complete "
                    + "endpoint classification, weak comparison and uniqueness of a same-length "
                    + "interval imply that same strict earlier bound. This produces First and weak "
                    + "Record without assuming any correspondence with a proxy sequence.")),
                Paragraph(Text(
                    "For set completeness, classify an arbitrary actual maximal run by a retained "
                    + "length. For the converse, take the displayed actual witness; its strict earlier "
                    + "bound makes it a record. A record is already an actual maximal run, giving the "
                    + "reverse inclusion for record values. Strict ordering excludes duplicate retained "
                    + "values. The branch proofs establish the literal support and component completeness.")),
                Paragraph(Text(
                    "Corollary 3.1 is a direct substitution consequence: exponent parity gives "
                    + "2^m mod 3 and the odd-prime powers modulo six, separating the displayed affine "
                    + "families; strict ordering gives their disjointness. The first interval rows at "
                    + "(p,m)=(5,1),(7,1) are omitted because their lengths are zero. The corollary's "
                    + "initial values and witness table are evaluations of these formulas, with no "
                    + "additional table theorem or independent mathematical assumption."))))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, params DocumentBlock[] extra) => Describe.Lean(
            DescribeId.Create("raney-all-prime-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(RaneySource), Blocks([Paragraph(Text(prose)), .. extra]), role);

    private static Formula V(string n) => F.Id(n);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string n, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. xs]);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula Iff(Formula a, Formula b) => Seq(P(a), Sp, Leftrightarrow, Sp, P(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Or, P(b));
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula And(params Formula[] xs)
    {
        Formula r = P(xs[0]);
        for (var i = 1; i < xs.Length; i++) r = new Formula.Logic(r, FormulaLogicOperator.And, P(xs[i]));
        return r;
    }
    private static Formula All(string n, Formula b) => Bind(n, N(), b);
    private static Formula Bind(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), N(), b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Div(Formula a, byte b) => Call("NatDiv", a, D(b));
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Len(Formula a, Formula b) => Sub(Add(b, D(1)), a);
    private static Formula Run(Formula r, Formula a, Formula b) => Call("IsMaximalDeltaInterval", Call("singleton", D(0)), r, a, b);
    private static Formula Ret(Formula p, Formula m, Formula j) => Call("Ret", p, m, j);
    private static Formula A(Formula p, Formula m, Formula j) => Call("A", p, m, j);
    private static Formula B(Formula p, Formula m, Formula j) => Call("B", p, m, j);
    private static Formula L(Formula p, Formula m, Formula j) => Call("L", p, m, j);
    private static Formula Valid(Formula j) => Or(Eqn(j, D(1)), Eqn(j, D(2)));
    private static Formula Omit(Formula q, Formula j) => Or(Eqn(j, D(2)), And(Ne(q, D(5)), Ne(q, D(7))));

    private static Formula RecordFormula(bool first)
    {
        var r = V("rho"); var a = V("a"); var b = V("b"); var c = V("c"); var d = V("d");
        var condition = first
            ? Imp(And(Run(r, c, d), Eqn(Len(c, d), Len(a, b))), Le(a, c))
            : Imp(And(Run(r, c, d), LtF(c, a)), Le(Len(c, d), Len(a, b)));
        return Disp(All("p", Bind("rho", new Formula.TypeArrow(N(), Call("ZMod", V("p"))),
            All("a", All("b", Iff(Call(first ? "IsFirstZeroRunLength" : "IsWeakZeroRunRecord", r, a, b),
                And(Run(r, a, b), All("c", All("d", condition)))))))));
    }

    private static Formula SetFormula(bool record)
    {
        var r = V("rho"); var l = V("l"); var a = V("a"); var b = V("b");
        return Disp(All("p", Bind("rho", new Formula.TypeArrow(N(), Call("ZMod", V("p"))), All("l",
            Iff(new Formula.Relation(l, FormulaRelationOperator.MemberOf,
                Call(record ? "positiveZeroRunRecordValues" : "positiveZeroRunLengths", r)),
                And(LtF(D(0), l), Ex("a", Ex("b", And(
                    record ? Call("IsWeakZeroRunRecord", r, a, b) : Run(r, a, b), Eqn(l, Len(a, b)))))))))));
    }

    private static Formula RetainedFormula()
    {
        var p = V("p"); var m = V("m"); var j = V("j");
        return Disp(All("p", All("m", All("j", Iff(Call("runSpectrumRetained", p, m, j),
            Ite(Eqn(p, D(2)), And(Le(D(2), m), Eqn(j, D(1))),
                Ite(Eqn(p, D(3)), And(Le(D(1), m), Eqn(j, D(1))),
                    And(Le(D(5), p), Le(D(1), m), Valid(j), Omit(Pow(p, m), j)))))))));
    }

    private static Formula NumericFormula(int which)
    {
        var p = V("p"); var m = V("m"); var j = V("j"); var q = Pow(p, m);
        var binary = which == 0 ? Div(Add(Pow(D(2), Add(m, D(1))), D(2)), 3)
            : which == 1 ? Sub(Pow(D(2), m), D(1)) : Div(Pow(D(2), m), 3);
        var ternary = which == 0 ? Div(Add(Pow(D(3), m), D(1)), 2)
            : which == 1 ? Div(Sub(Pow(D(3), Add(m, D(1))), D(3)), 2) : Sub(Pow(D(3), m), D(1));
        var large = which == 0 ? Div(Add(new Formula.Binary(j, FormulaBinaryOperator.Multiply, q), D(2)), 3)
            : which == 1 ? Ite(Eqn(j, D(1)), Div(Sub(q, D(3)), 2), Sub(q, D(1)))
            : Ite(Eqn(j, D(1)), Ite(Eqn(Call("mod", q, D(6)), D(1)), Div(Sub(q, D(7)), 6), Div(Sub(q, D(5)), 6)), Div(q, 3));
        return Disp(All("p", All("m", All("j", Eqn(Call(which == 0 ? "runSpectrumStart" : which == 1 ? "runSpectrumLast" : "runSpectrumLength", p, m, j),
            Ite(Eqn(p, D(2)), binary, Ite(Eqn(p, D(3)), ternary, large)))))));
    }

    private static Formula ResultFormula()
    {
        var p = V("p"); var m = V("m"); var h = V("h"); var j = V("j"); var k = V("k");
        var r = Call("rho", p); var a = A(p, m, j); var b = B(p, m, j); var l = L(p, m, j);
        var witnesses = All("m", All("j", Imp(Ret(p, m, j), And(Run(r, a, b), LtF(D(0), l),
            Eqn(Len(a, b), l), Call("IsFirstZeroRunLength", r, a, b), Call("IsWeakZeroRunRecord", r, a, b)))));
        var ordered = All("m", All("h", All("j", All("k", Imp(And(Ret(p, m, j), Ret(p, h, k),
            Or(LtF(m, h), And(Eqn(m, h), LtF(j, k)))), LtF(l, L(p, h, k)))))));
        var unique = All("m", All("h", All("j", All("k", Imp(And(Ret(p, m, j), Ret(p, h, k),
            Eqn(l, L(p, h, k))), And(Eqn(m, h), Eqn(j, k)))))));
        var q = Pow(p, m);
        var omissions = Imp(Le(D(5), p), All("m", All("j", Imp(And(Le(D(1), m), Valid(j)),
            Iff(Le(Div(Add(new Formula.Binary(j, FormulaBinaryOperator.Multiply, q), D(2)), 3),
                Ite(Eqn(j, D(1)), Div(Sub(q, D(3)), 2), Sub(q, D(1)))), Omit(q, j))))));
        return Disp(All("p", Imp(Call("Prime", p), And(
            Eqn(Call("positiveZeroRunLengths", r), Call("Values", p)),
            Eqn(Call("positiveZeroRunRecordValues", r), Call("Values", p)),
            witnesses, ordered, unique, omissions))));
    }
}
