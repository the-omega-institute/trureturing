using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class CarryGraphFiniteSamplerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Par(Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body));
    private static Formula Ex(Formula x, Formula type, Formula body) =>
        Par(Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body));
    private static Formula And(params Formula[] fs) => Par(Seq(fs.SelectMany((f, i) =>
        i == 0 ? new[] { f } : new[] { Sp, Land, Sp, f }).ToArray()));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula Add(Formula a, Formula b) => Par(Seq(a, Sp, Plus, Sp, b));
    private static Formula Mul(Formula a, Formula b) => Par(Seq(a, Sp, Cdot, Sp, b));
    private static Formula Ty(string name) => Seq(Mathbb, Grp(V(name)));
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Pos(Formula a) => Seq(D(0), Sp, Lt, Sp, a);
    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        var m = V("m"); var s = V("s"); var j = V("j"); var f = V("f");
        var u = V("u"); var t = V("tape"); var d = V("d"); var c = V("c"); var n = V("n");
        var active = Call("Active", m);
        var control = Call("Sum", active, Call("Fin", m));
        var policies = Call("P", m);
        Formula Parameters(Formula b) => All(m, Ty("N"), All(f, policies, b));
        Formula Run(Formula k) => Call("execute", m, f, c, t, k);
        var prev = Run(d);
        var next = Add(d, D(1));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A stationary carry table needs only a bounded slot control to preserve every fair-tape output and charge.",
            H("Finite Carry-slot Sampling"), Blocks(
                Def("Active", "Bounded active controls", All(m, Ty("N"),
                    Equal(active, Seq(OpenBrace, Pair(s, j), Sp, InMacro, Sp,
                        Call("Product", Call("S", m), Ty("N")), Mid, Sp,
                        j, Sp, Lt, Sp, Call("r", s), CloseBrace))),
                    "S(m) contains exactly the legal integer carry states. The slot j is a natural number below r, so an active control has positive width. The stored fields are r, e and j; no depth or history word is stored."),
                Def("initial", "Root control", All(m, Ty("N"), Imp(Leq(D(2), m),
                    Equal(Call("initial", m), Call("inl", Pair(Call("root", m), D(0)))))),
                    "The root has r=1 and e=m, with its unique slot numbered zero."),
                Def("step", "One-bit control transition", Parameters(All(u, V("Bool"),
                    All(c, control, Seq(Call("step", m, f, u, c), Sp, InMacro, Sp, control)))),
                    "An output control is absorbing. At an active control (s,j), apply the legal action f(s), form the increasing list L of its fixed labels, and set z=2j+toNat(u). If z is below the length of L, output L[z]. Otherwise move to the carry successor and slot z-length(L). A slot guard totalizes the definition by retaining the old active control when the guard fails; the correspondence proves this case is never taken from the root."),
                Def("execute", "Control and separate invoice", Parameters(All(c, control,
                    All(t, V("Tape"), And(Equal(Run(D(0)), Pair(c, D(0))),
                        All(d, Ty("N"), Equal(Run(next), Pair(
                            Call("step", m, f, Call("bit", t, d), Call("fst", prev)),
                            Add(Call("snd", prev), Call("indicator", V("isLeft"), Call("fst", prev)))))))))),
                    "The invoice increments once at an active control and stays fixed after output. Only the control and the current bit enter step; the invoice is an external execution observation."),
                Def("sample", "First output with its invoice", Parameters(All(c, control,
                    All(t, V("Tape"), Equal(Call("sample", m, f, c, t),
                        Call("firstOutput", Call("execute", m, f, c, t)))))),
                    "Take the first execution index whose control is an output, and return its label and invoice. The sample is absent if no finite output occurs."),
                Def("bill", "Every active step is charged", Parameters(All(c, control,
                    All(t, V("Tape"), Equal(Call("bill", m, f, c, t),
                        Seq(new Formula.Subscript(F.Sum, Seq(d, Sp, InMacro, Sp, Ty("N"))),
                            Call("indicator", V("isLeft"), Call("fst", Run(d)))))))),
                    "The sum is nonnegative extended-real. A divergent execution has infinitely many active steps and therefore an infinite bill."),
                Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                    H("Finite control attains the critical bit bill"),
                    StatementSource.FromAuthor(Disp(ResultFormula())), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For every m at least two, a critical stationary table with a positive anchor exists. Every stationary table whose positive anchor and path cost satisfy C=alpha(m) times the anchor has a finite slot machine. Its policy path gamma starts at the root, and p is the law obtained from that path's fixed label digits. At every index on every tape, a returned scan label and charge agree with the machine control and invoice; a continuing scan slot agrees with the machine's carry state and slot. Thus their first-return samples and total bills coincide even on exceptional divergent tapes. In the display, core(x) is the stored carry state and slot(x) is its natural slot; treeSample and treeBill denote the existing fixed-label tree sample and bill.")),
                        Paragraph(Text("The active-control bound is m squared times (m-1) divided by two, with m additional absorbing output labels. The output law is strictly positive and normalized, its minimum is the positive anchor, its label probabilities are the digit sums, and its stopping tail is r(d)/2 raised to d. It returns almost surely and every returned invoice equals the total bill. The expected bill equals the policy-path cost, the dyadic cost of p and alpha(m) times the anchor.")),
                        Paragraph(Text("The statement gives no rationality claim, minimum-state claim or uniform bound on the number of bits read."))),
                    DescribeRole.Theorem))));
    }

    private static Formula ResultFormula()
    {
        var m = V("m"); var f = V("f"); var g = V("gamma"); var p = V("p");
        var t = V("tape"); var d = V("d"); var i = V("i"); var n = V("n");
        var j = V("j"); var x = V("x"); var indices = Call("Fin", m);
        var natural = Ty("N"); var active = Call("Active", m);
        var start = Call("initial", m);
        Formula Run(Formula k) => Call("execute", m, f, start, t, k);
        Formula Scan(Formula k) => Call("scan", m, g, t, k);
        Formula Sample() => Call("sample", m, f, start, t);
        Formula Bill() => Call("bill", m, f, start, t);
        Formula Returned(Formula k) => Equal(Sample(), Call("some", Pair(i, k)));
        Formula Event(Formula b) => Seq(OpenBrace, t, Sp, InMacro, Sp, V("Tape"), Mid, Sp, b, CloseBrace);
        var next = Add(d, D(1)); var anchor = Call("anchorValue", g); var cost = Call("pathCost", g);
        var simulation = All(t, V("Tape"), All(d, natural, And(
            All(i, indices, All(n, natural, Imp(Equal(Scan(d), Call("inl", Pair(i, n))),
                Equal(Run(d), Pair(Call("inr", i), n))))),
            All(j, natural, Imp(Equal(Scan(d), Call("inr", j)), Ex(x, active, And(
                Equal(Run(d), Pair(Call("inl", x), d)),
                Equal(Call("core", x), Call("state", g, d)), Equal(Call("slot", x), j))))))));
        var tail = Event(Par(Seq(Equal(Sample(), V("none")), Sp, Lor, Sp,
            Ex(i, indices, Ex(n, natural, And(Returned(n), Seq(d, Sp, Lt, Sp, n)))))));
        var clauses = And(Call("IsRootPath", m, g), Call("Finite", active),
            Leq(Call("card", active), new Formula.Fraction(
                Mul(new Formula.Power(m, D(2)), Par(Seq(m, Sp, Minus, Sp, D(1)))), D(2))),
            Equal(Call("card", indices), m), simulation,
            All(t, V("Tape"), And(Equal(Sample(), Call("treeSample", m, g, t)),
                Equal(Bill(), Call("treeBill", m, g, t)))),
            All(i, indices, Pos(Call("p", i))),
            Equal(Seq(new Formula.Subscript(F.Sum, Seq(i, Sp, InMacro, Sp, indices)), Call("p", i)), D(1)),
            Pos(anchor), Equal(Call("inf", Call("range", p)), anchor),
            All(i, indices, Equal(Call("p", i),
                Seq(new Formula.Subscript(F.Sum, Seq(d, Sp, InMacro, Sp, natural)),
                    new Formula.Fraction(Call("indicator", Call("labelSet", m, g, d), i),
                        new Formula.Power(D(2), next))))),
            All(t, V("Tape"), All(i, indices, All(d, natural,
                Seq(Returned(next), Sp, Iff, Sp, Pair(Call("prefix", t, next), i),
                    Sp, InMacro, Sp, Call("stopping", m, g, d))))),
            All(t, V("Tape"), All(i, indices, All(n, natural,
                Imp(Returned(n), Equal(Bill(), n))))),
            All(i, indices, Equal(Call("fairTape", Event(Ex(n, natural, Returned(n)))),
                Call("ofReal", Call("p", i)))),
            All(d, natural, Equal(Call("fairTape", tail), Call("ofReal",
                new Formula.Fraction(Call("r", Call("state", g, d)), new Formula.Power(D(2), d))))),
            Par(Seq(new Formula.Power(Forall, Call("ae", V("fairTape"))), Sp,
                t, Colon, Sp, V("Tape"), Comma, Sp, Ex(i, indices, Ex(n, natural, Returned(n))))),
            Equal(Call("lintegral", V("fairTape"), Call("bill", m, f, start)), Call("ofReal", cost)),
            Equal(cost, Call("cost", p)), Equal(Call("cost", p), Mul(Call("alpha", m), anchor)));
        var orbit = Call("policyPath", m, f, Call("root", m));
        var existsCritical = Ex(f, Call("P", m), And(Pos(Call("anchorValue", orbit)),
            Equal(Call("pathCost", orbit), Mul(Call("alpha", m), Call("anchorValue", orbit)))));
        var everyCritical = All(f, Call("P", m), Ex(g, V("Path"),
            Ex(p, Seq(indices, Sp, To, Sp, Ty("R")), And(
                Equal(g, orbit),
                All(i, indices, Equal(Call("p", i), Call("ofDigits", Call("labelDigit", g, i)))),
                Imp(Pos(anchor), Imp(Equal(cost, Mul(Call("alpha", m), anchor)), clauses))))));
        return All(m, natural, Imp(Leq(D(2), m), And(existsCritical, everyCritical)));
    }
}
