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
            Paragraph(Text("Application to every original block departure slot.")),
            Paragraph(Math(SlotLaw())),
            Paragraph(Text("This is an application of the existing affine and order results inside StrictSupply.actual_strict_cost_supply and ClosedSupply.actual_closed_record_supply. The ownership map o : Fin 5 -> Bool is arbitrary, as is the real budget b subject only to lam - rho < b. Both sides have sign high = 1 and sign low = -1. For every real displacement 0 < D <= eSide j, the strict six-slot U/V supply is equivalent to lam - g^2 D < b. The closed supply is equivalent to that strict inequality or exact equality together with high o 0 = true or low o 1 = false. These are per-occurrence error existentials, not a common error for a whole block. For every real 0 <= z <= T2, all twenty C/colorsE departures have their own error of magnitude strictly below b.")),
            Paragraph(Text("The parameters are t = (sqrt 5 - 1)/2, g = 2t - 1, phi = 1 + t, T2 = 1 - t, lam = T2/10, c0 = 2t/5, rho = g^6 and chi = g^20. The bounds g^2 + 4g = 1, 4/17 < g < 17/72, 59/250 < g and g < 1/4 follow by normalization from Real.sq_sqrt and Real.sqrt_nonneg at 5. The six-cell cuts in order are -1, -T2-lam, g-3lam, t-5lam, 2t-7lam, 2t+lam and phi. Clipping is max(-1,min(phi,x+error)); readout at each interior cut uses its own ownership bit to choose the adjacent color. On open cell interiors, ownership has no effect.")),
            Paragraph(Text("The actual literal words are U = [L5,L0,L3,L0,L3,L3], V = [L0,L3,L3,L5,L0,L3], and C = [L5,L5,L3,L2,L2,L0,L3,L3,L3,L25,L5,L0,L0,L2,L2,L25,L3,L3,L0,L5]. Their color lists are colorsD = [2,1,0,2,1,0] and colorsE = [2,3,0,3,4,2,0,1,0,5,2,1,1,3,3,5,0,0,1,2]. The suffix is dropped at the actual position p before composing; it is never a left prefix or a reversed block.")),
            Paragraph(Text("At input c0 the U suffix coordinates for p = 0,...,5 are (-257+1096g)/5, (-121+519g)/10, (-35+121g)/10, -3/5+3g, (-3+3g)/5, and (-7+g)/10. The V suffix coordinates are (-342+1451g)/5, (-83+342g)/5, (-45+161g)/10, -3/5+4g, (-1+11g)/10, and (-7+g)/10. Each table ends at coordinate c0 at p = 6. The branch recurrence at each of these finitely many positions is algebraic normalization. Nat.decreasingInduction' with List.drop_eq_getElem_cons and List.drop_eq_nil_of_le transports this table along the suffix; it adds no numerical assumption.")),
            Paragraph(Text("The affine clause of literal_source_geometry gives compose(w.drop p,z) - compose(w.drop p,c0) = (-g)^(length(w)-p)(z-c0). The bound |z-c0| <= 2/5 gives magnitude at most (1/4)^(length(w)-p) 2/5 by pow_le_pow_left₀ and mul_le_mul. For U/V, every nonactive p != 4 is strictly attainable: exists_between chooses y between max(cut i,x-b) and min(cut(i+1),x+b), and error = y-x has |error| < b and clips to the required open-cell point. At p = 4 the coordinate is cut 1 - lam + g^2 D on the high side and cut 2 + lam - g^2 D on the low side. Color 1 requires a point between these two cuts. Thus strict feasibility gives exactly the stated cost inequality. At equality in the closed contract the errors are b on high and -b on low, and the endpoint readout requires precisely o 0 = true or o 1 = false.")),
            Paragraph(Text("For C, write q_p = compose(C.drop p,c0). Every original occurrence is covered by the following color and coordinate pairs: p0: (2,(1+g)/5); p1: (3,(5+3g)/10); p2: (0,-4/5); p3: (3,(7+3g)/10); p4: (4,(9+3g)/10); p5: (2,(1+g)/10); p6: (0,(-5-g)/10); p7: (1,-2/5); p8: (0,(-9-g)/10); p9: (5,(6+2g)/5); p10: (2,(3+3g)/10); p11: (1,g/5); p12: (1,-1/5); p13: (3,(4+g)/5); p14: (3,(3+g)/5); p15: (5,(7+2g)/5); p16: (0,(-5+g)/10); p17: (0,-3/5); p18: (1,(-1+g)/10); p19: (2,(3+g)/10). The p20 suffix is empty and has coordinate c0. Every displayed q_p lies strictly inside the required color cell by the same cut and g bounds.")),
            Paragraph(Text("For each C occurrence p < 19, choose its own error q_p - compose(C.drop p,z). Its magnitude is at most (1/4)^(20-p) 2/5 <= 1/40 < b, using pow_le_pow_of_le_one and lam - rho < b; the corrected point is exactly q_p. At p = 19 choose error zero: throughout the full closed input interval [0,T2], the one-label suffix branch L5 z lies strictly between cut 2 and cut 3. These witnesses include both input endpoints and all twenty original positions. StrictSupply uses them at the actual input c0 + sign j chi^n D of each repeated C block. ClosedSupply uses the same strict witnesses and weakens only |error| < b to |error| <= b. The same-parameter bounds 0 < chi^n D < hSide j < eSide j and the actual interval domain are discharged in those proofs.")),
            Paragraph(Text("The source displacements are h_high = (39-6g)/380, h_low = (46+31g)/380, e_high = T2-c0, e_low = c0, a_j = (1-rho)h_j, x_j = a_j + rho chi^3 e_j and y_j = a_j + rho chi x_j. The initial displacement is x_j in the original model and y_j in the anchored model. The operational application retains every positive Return(m,r), with m > 0 and r > 0: returnWord is m copies of block j followed by r copies of C, returnColors has the corresponding replicated colors, and returnMap j a D = hSide j - rho^m(hSide j - chi^r D). External words group the reversed execution list while preserving each block's letters. The observed prefix is stem j ++ externalWord j execution ++ anchor j model, with stem = block j ++ C and anchor empty in the original model or stem in the anchored model. The tail is block j ++ C repeated three times ++ [L5,L0] on high or ++ [L0] on low, then the address defaults to L0 forever. The history is colorsD ++ colorsE ++ the flattened reversed returnColors, followed by no anchor colors or by colorsD ++ colorsE respectively. Both the observed and history lengths are exactly 26 or 52 plus sum(6m+20r), as supplied by paired_source_reconstruction.")),
            Paragraph(Text("ActualPairSupply uses one error function for each side of the prescribed source, with the complete-right-suffix coordinate at every history occurrence. The strict, closed and recordMargin contracts respectively require every |err p| < b, every |err p| <= b, or a single positive eps with every |err p| <= b-eps. At every p at or beyond the history length the error is zero, and all later readouts equal the actual tail readouts at zero error. The source reconstruction, literal_source_geometry and literal_address_path preserve the actual returns, legality, guards and zero-tail coordinates. The consumer proofs assemble the local errors through the actual words and history, without adding a premise or changing either model. These exact mathematical applications assert no physical decoder realization, resource optimum or literature novelty. The block feasibility formulas alone do not establish whole-record supply, cap/guard equivalences or asymptotic rates; those remain the conclusions of their actual supply, operation, storage and rate consumers.")),
            Paragraph(Text("ActualPairSupply is independently defined through clipped readout, error bounds, the prescribed history and zero-error futures. The declarations here reconstruct the literal sources; the block applications above are used inside the actual supply proofs. Whole-record supply is supplied separately by StrictSupply.actual_strict_record_supply and ClosedSupply.actual_closed_record_supply. StrictSupply.uniform_guard_trace_iff_split and exact_control_iff_split give their stated cap and guard conditions. Completion.auxiliary_factor_upper_completion and actual_source_address_injection provide the actual factor completion and literal-source separation. The exact original client anonymous37 assembles the every-weight list/history/source cardinalities and their rate equalities for both models, both contracts and offsets 26 and 52. Full auxiliary62.18 nesting, intersection and asymptotics, the interior spectral root, canonical containing paths and the compliant decoder33.13 optimum remain outside these local source laws.")))));
}
