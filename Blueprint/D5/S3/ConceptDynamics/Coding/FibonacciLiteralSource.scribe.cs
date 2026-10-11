using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FibonacciLiteralSourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciLiteralSource.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula I(string name) => F.Id(name);
    private static Formula Words => Call("List", I("Label"));
    private static Formula Returns => Call("List", I("Return"));
    private static Formula Len(Formula word) => Call("length", word);
    private static Formula Coord(Formula word, Formula position) => Call("coordinate", word, position);
    private static Formula Comp(Formula word, Formula point) => Call("compose", word, point);
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Pow(Formula a, Formula b) => Call("power", a, b);
    private static Formula Append(Formula a, Formula b) => Call("append", a, b);

    private static Formula Geometry()
    {
        var w = I("w"); var v = I("v"); var z = I("z");
        var s = I("s"); var e = I("e"); var p = I("p");
        var left = I("left"); var block = I("B"); var right = I("right");
        var x = I("x"); var y = I("y");
        return Disp(And(
            All(Imp(And(Call("LegalWord", s, e, w), Call("InSupport", e, z)),
                    Call("InSupport", s, Comp(w, z))),
                B("s", I("Guard")), B("e", I("Guard")), B("w", Words), B("z", I("Real"))),
            All(Imp(Call("le", p, Len(block)), Equal(
                    Coord(Append(Append(left, block), right), Add(Len(left), p)),
                    Add(Comp(Call("drop", block, p), I("c0")),
                        Mul(Pow(Call("negate", I("g")), Sub(Len(block), p)),
                            Sub(Coord(right, D(0)), I("c0")))))),
                B("left", Words), B("B", Words), B("right", Words), B("p", I("Nat"))),
            All(Equal(Coord(Append(w, Call("replicate", I("n"), I("L0"))), p), Coord(w, p)),
                B("w", Words), B("n", I("Nat")), B("p", I("Nat"))),
            All(Equal(Comp(w, Add(x, y)),
                    Add(Comp(w, x), Mul(Pow(Call("negate", I("g")), Len(w)), y))),
                B("w", Words), B("x", I("Real")), B("y", I("Real"))),
            All(Equal(Comp(Append(w, v), z), Comp(w, Comp(v, z))),
                B("w", Words), B("v", Words), B("z", I("Real")))));
    }

    private static Formula Reconstruction()
    {
        var j = I("j"); var model = I("model"); var xs = I("execution");
        var p = I("p"); var state = I("D");
        var prefix = Call("observedPrefix", j, model, xs);
        var full = Call("sourcePrefix", j, model, xs);
        var tail = Call("tailPrefix", j);
        var external = Call("externalWord", j, xs);
        Formula Signed(Formula value) => Add(I("c0"), Mul(Call("sign", j), value));
        var paidLength = Add(Call("observationOffset", model), Call("listWeight", xs));
        return Disp(All(And(
            Call("LegalWord", I("G0"), I("G0"), full),
            All(Equal(Call("source", j, model, xs, Add(Len(prefix), p)), Call("address", tail, p)),
                B("p", I("Nat"))),
            All(Equal(Coord(full, Add(Len(prefix), p)), Coord(tail, p)), B("p", I("Nat"))),
            Equal(Coord(Append(Append(external, Call("anchor", j, model)), tail), D(0)),
                Signed(Call("execute", j, xs, Call("initial", j, model)))),
            Equal(Len(prefix), paidLength), Equal(Len(Call("history", model, xs)), paidLength),
            All(Equal(Comp(I("C"), Signed(state)), Signed(Mul(I("chi"), state))), B("D", I("Real"))),
            All(Equal(Comp(Call("block", j), Signed(state)),
                Signed(Add(Call("aSide", j), Mul(I("rho"), state)))), B("D", I("Real"))),
            All(Equal(Comp(Call("returnWord", j, I("a")), Signed(state)),
                Signed(Call("returnMap", j, I("a"), state))), B("a", I("Return")), B("D", I("Real"))),
            All(Equal(Comp(Call("externalWord", j, I("xs")), Signed(state)),
                Signed(Call("execute", j, I("xs"), state))), B("xs", Returns), B("D", I("Real"))),
            Equal(Comp(tail, D(0)), Signed(Call("xSide", j)))),
            B("j", I("Side")), B("model", I("Model")), B("execution", Returns)));
    }

    private static Formula PathLaw()
    {
        var path = I("path"); var p = I("p"); var w = I("w");
        Formula At(Formula n) => Call("apply", path, n);
        return Disp(All(Imp(Call("LegalWord", I("s"), I("e"), w),
            new Formula.BindMany(FormulaQuantifier.Exists,
                [B("path", Call("Function", I("Nat"), I("Guard")))], And(
                    Equal(At(D(0)), I("s")),
                    All(Equal(Call("nextGuard", At(p), Call("address", w, p)),
                        Call("some", At(Add(p, D(1))))), B("p", I("Nat"))),
                    All(Call("InSupport", At(p), Coord(w, p)), B("p", I("Nat"))),
                    All(Equal(Coord(w, p), Call("branch", Call("address", w, p),
                        Coord(w, Add(p, D(1))))), B("p", I("Nat")))))),
            B("s", I("Guard")), B("e", I("Guard")), B("w", Words)));
    }

    private static Formula SlotLaw()
    {
        var o = I("o"); var b = I("b"); var j = I("j"); var state = I("D"); var z = I("z");
        Formula Supply(bool strict) => Call("BlockSupply", o, b, I(strict ? "true" : "false"),
            Call("block", j), I("colorsD"), Add(I("c0"), Mul(Call("sign", j), state)));
        var cost = Sub(I("lam"), Mul(Pow(I("g"), D(2)), state));
        var domain = And(Call("lt", D(0), state), Call("le", state, Call("eSide", j)));
        var owned = new Formula.Logic(
            And(Equal(j, I("high")), Equal(Call("apply", o, D(0)), I("true"))),
            FormulaLogicOperator.Or,
            And(Equal(j, I("low")), Equal(Call("apply", o, D(1)), I("false"))));
        var closed = new Formula.Logic(Call("lt", cost, b), FormulaLogicOperator.Or,
            And(Equal(cost, b), owned));
        return Disp(All(Imp(Call("lt", Sub(I("lam"), I("rho")), b), And(
            All(Imp(domain, new Formula.Logic(Supply(true), FormulaLogicOperator.Iff,
                Call("lt", cost, b))), B("j", I("Side")), B("D", I("Real"))),
            All(Imp(domain, new Formula.Logic(Supply(false), FormulaLogicOperator.Iff, closed)),
                B("j", I("Side")), B("D", I("Real"))),
            All(Imp(And(Call("le", D(0), z), Call("le", z, I("T2"))),
                Call("BlockSupply", o, b, I("true"), I("C"), I("colorsE"), z)),
                B("z", I("Real"))))), B("o", I("Ownership")), B("b", I("Real"))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five-label affine source uses its original legal guards, endpoint flags, literal blocks and eventually-empty tails. Each departure coordinate belongs to one complete suffix of that source.",
        H("Literal Fibonacci sources and occurrence coordinates"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-literal-source-geometry"),
                DeclarationHandle.Create(Prefix + "literal_source_geometry"), H("One coordinate per occurrence"),
                StatementSource.FromAuthor(Geometry()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction over the literal word proves support preservation and its affine suffix law. Extending the finite cutoff by empty labels leaves every coordinate unchanged. The displacement in an occurrence formula is the coordinate of the actual complete right suffix minus the fixed center."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-paired-source-reconstruction"),
                DeclarationHandle.Create(Prefix + "paired_source_reconstruction"), H("Reconstruct both prescribed sources"),
                StatementSource.FromAuthor(Reconstruction()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite block calculation uses every original cycle label. Induction reconstructs the reversed execution list without reversing block letters. Both templates have legal seams, the exact original tail at the unobserved terminal, the actual scalar return action, and observation lengths 26 plus the variable weight or 52 plus that weight."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-literal-address-path"),
                DeclarationHandle.Create(Prefix + "literal_address_path"), H("The complete literal departure path"),
                StatementSource.FromAuthor(PathLaw()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction constructs a guard itinerary from the legal prefix. At every departure position, including the eventual empty tail, the coordinate lies in that guard's support and satisfies the original label branch recurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-literal-full-slot-readout"),
                DeclarationHandle.Create(Prefix + "literal_full_slot_readout"), H("Every original block departure slot"),
                StatementSource.FromAuthor(SlotLaw()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For budgets above lambda minus rho, all six positions of U and V and all twenty positions of C are checked at one fixed block input. The active position has cost lambda minus g squared times its displacement. Strict acquisition requires a strict cost inequality; equality in the closed contract uses the original high-side first flag or low-side second flag. The input domains are exactly the original comparison domains. This block law alone does not establish whole-record supply or the cap and high-guard equivalence."))),
                DescribeRole.Theorem),
            Paragraph(Text("ActualPairSupply is independently defined through clipped readout, error bounds, the prescribed history and zero-error futures. The declarations here reconstruct the literal sources and certify individual block slots. Whole-record supply is supplied separately by StrictSupply.actual_strict_record_supply and ClosedSupply.actual_closed_record_supply. StrictSupply.uniform_guard_trace_iff_split and exact_control_iff_split give their stated cap and guard conditions. Completion.auxiliary_factor_upper_completion and actual_source_address_injection provide the actual factor completion and literal-source separation. The exact original client anonymous37 assembles the every-weight list/history/source cardinalities and their rate equalities for both models, both contracts and offsets 26 and 52; those applications do not become new declarations here. Full auxiliary62.18 nesting, intersection and asymptotics, the interior spectral root, canonical containing paths and the compliant decoder33.13 optimum remain outside these local source laws.")))));
}
