using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AffineNetworks;

internal sealed class AffineModularBehaviorDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/AffineNetworks/AffineModularBehavior.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact congruence boundary of actual affine path and adaptive transcripts.",
        H("Affine modular behavior theorem 11.2"),
        Blocks(Describe.Lean(
            DescribeId.Create("affine-modular-behavior"),
            DeclarationHandle.Create(Gid + "theorem11_2"),
            H("All-path congruence and minimum realized boundary"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "All formulas quantify the original Network N. Its fields N.m, N.V, N.E, " +
                    "N.src, N.dst, N.d, N.a and N.c have their original meanings. Type denotes " +
                    "Lean's universe-zero Type; C and S denote the arbitrary Control and State " +
                    "types, s the legal selector, c the common initial control, r the readout, " +
                    "and u the second initial phase. Natcard, range and Surjective mean Nat.card, " +
                    "Set.range and Function.Surjective. Function arguments follow the Lean source; " +
                    "implicit network and endpoint arguments are inferred from the bound path.")),
                Paragraph(Text(
                    "Fix a positive modulus m, a nonempty finite directed multigraph with named edges, " +
                    "and positive port divisors d_v of m. At every vertex the actual source is all of " +
                    "ZMod m. Each edge e is legal at every source phase and transports that same phase " +
                    "by t ↦ a_e t+c_e modulo m. The natural multiplier may be zero. Loops, parallel " +
                    "edges, repeated edge occurrences and the empty path are retained.")),
                Paragraph(Text(
                    "For an actual path γ:v→w let A_γ be the product of its edge multipliers, with " +
                    "A_empty=1. Define D_v as the lcm of d_w/gcd(d_w,A_γ) over all such paths. This is " +
                    "the independent all-path divisor image, without a bound on path length. D_v is a " +
                    "positive divisor of m. The boundary map b_v is actual reduction from ZMod m " +
                    "to ZMod D_v; equality of its values is congruence modulo D_v.")),
                Paragraph(Text(
                    "A fixed-path transcript starts with the initial vertex and port answer. Each " +
                    "step appends the chosen named edge, the destination vertex and its actual port " +
                    "answer. For two initial phases, equality of every such finite transcript is " +
                    "equivalent to equality under b_v. No hidden phase is included in a public event.")),
                Paragraph(Text(
                    "An adaptive execution stores the physical phase separately from its public " +
                    "vertex, history, internal control and halt flag. The control type is arbitrary " +
                    "and need not be finite. Its deterministic selector uses only the vertex, full " +
                    "obtained history and internal control. It either halts or chooses an outgoing " +
                    "named edge and the next control state. The executor updates the phase by the " +
                    "original affine rule and appends the actual edge and port; a halt is absorbing. " +
                    "Every finite horizon, including horizon zero, is allowed.")),
                Paragraph(Text(
                    "For phases t,t′ at v, all adaptive histories agree for every selector, every " +
                    "common internal initial state and every finite horizon if and only if " +
                    "b_v(t)=b_v(t′). The universal quantifier is essential: a particular selector " +
                    "can halt immediately or choose an uninformative path.")),
                Paragraph(Text(
                    "Reduction b_v is surjective, so its realized image has exactly D_v states. " +
                    "For any deterministic readout r from the full source into any state type, if " +
                    "equal r-values imply agreement of every fixed-path transcript, then its " +
                    "realized image has at least D_v states. The count concerns attained values, " +
                    "not unused labels. This gives both attainment and the minimum.")),
                Paragraph(Text(
                    "Ordered-path induction proves T_γ(t′)−T_γ(t)=A_γ(t′−t). Reduction at w and " +
                    "gcd cancellation show that its terminal ports agree precisely when " +
                    "d_w/gcd(d_w,A_γ) divides t′−t. Taking the lcm gives the boundary kernel. " +
                    "Every intermediate observation is itself the endpoint of a prefix path.")),
                Paragraph(Math(EndpointFormula())),
                Paragraph(Text(
                    "For adaptive executions, a simultaneous induction maintains one actual named " +
                    "path and a shared public history and control state, while the two independently " +
                    "updated phases equal their respective actual runs along that path. Equal " +
                    "prefix ports force the same next selection. Conversely, a controller that " +
                    "replays the remaining named-edge list executes any fixed legal path. " +
                    "Finally, sufficient readouts factor onto the realized reduction image, " +
                    "whose surjectivity gives the cardinality bound.")),
                Paragraph(Text(
                    "The boundary describes the joint kernel of all possible path experiments. " +
                    "It does not assert that one physical run can acquire every boundary class. " +
                    "No phase-dependent guard, fee or extra reference is present. Randomized " +
                    "control, acquisition costs and recovery memory are outside this statement."))),
            DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        Formula n = F.Id("N");
        Formula v = F.Id("v");
        Formula t = F.Id("t");
        Formula u = F.Id("u");
        Formula w = F.Id("w");
        Formula p = F.Id("p");
        Formula controlType = F.Id("C");
        Formula select = F.Id("s");
        Formula control = F.Id("c");
        Formula horizon = F.Id("n");
        Formula state = F.Id("S");
        Formula readout = F.Id("r");
        Formula phases = Call("ZMod", Field(n, "m"));
        Formula modulus = Call("allPathModulus", n, v);
        Formula boundary = Call("boundary", n, v);
        Formula same = Equal(Call("boundary", n, v, t), Call("boundary", n, v, u));
        Formula traces = All("w", Field(n, "V"),
            All("p", Call("NPath", n, v, w),
                Equal(Call("pathTranscript", p, t), Call("pathTranscript", p, u))));
        Formula selectorDomain = Seq(
            Open, w, Colon, Sp, Field(n, "V"), Close, Sp, To, Sp,
            Call("List", Call("Event", n)), Sp, To, Sp, controlType, Sp, To, Sp,
            Call("Option", Seq(OpenBrace, F.Id("e"), Colon, Sp, Field(n, "E"), Bar,
                Apply(Field(n, "src"), F.Id("e")), Eq, w, CloseBrace,
                Sp, Times, Sp, controlType)));
        Formula historyEqual = Equal(
            Field(Call("execute", select, horizon, v, t, control), "history"),
            Field(Call("execute", select, horizon, v, u, control), "history"));
        Formula histories = All("C", Constant("Type"), All("s", selectorDomain,
            All("c", controlType, All("n", Seq(Mathbb, Grp(F.Id("N"))), historyEqual))));
        Formula sufficient = All("t", phases, All("u", phases,
            Logic(Equal(Apply(readout, t), Apply(readout, u)),
                FormulaLogicOperator.Implies, traces)));
        Formula minimality = All("S", Constant("Type"),
            All("r", new Formula.TypeArrow(phases, state),
                Logic(sufficient, FormulaLogicOperator.Implies,
                    Relation(modulus, FormulaRelationOperator.LessThanOrEqual,
                        Call("Natcard", Call("range", readout))))));
        Formula conclusion = Conjoin(
                Conjoin(Relation(D(0), FormulaRelationOperator.LessThan, modulus),
                    Relation(modulus, FormulaRelationOperator.Divides, Field(n, "m"))),
                All("t", phases, All("u", phases,
                    Logic(traces, FormulaLogicOperator.Iff, same))),
                All("t", phases, All("u", phases,
                    Logic(histories, FormulaLogicOperator.Iff, same))),
                Call("Surjective", boundary),
                Equal(Call("Natcard", Call("range", boundary)), modulus),
                minimality);
        return Disp(All("N", Constant("Network"), All("v", Field(n, "V"), conclusion)));
    }

    private static Formula EndpointFormula()
    {
        Formula n = F.Id("N");
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula p = F.Id("p");
        Formula t = F.Id("t");
        Formula u = F.Id("u");
        Formula phases = Call("ZMod", Field(n, "m"));
        Formula endpoints = Equal(Call("portRead", n, w, Call("pathRun", p, t)),
            Call("portRead", n, w, Call("pathRun", p, u)));
        Formula difference = Call("natAbs", Subtract(
            Seq(Open, Field(u, "val"), Colon, Sp, new Formula.Integers(), Close),
            Seq(Open, Field(t, "val"), Colon, Sp, new Formula.Integers(), Close)));
        Formula cancellation = Logic(endpoints, FormulaLogicOperator.Iff,
            Relation(Call("pathQuotient", p), FormulaRelationOperator.Divides, difference));
        Formula pathEndpoints = All("w", Field(n, "V"), All("p", Call("NPath", n, v, w),
            All("t", phases, All("u", phases, cancellation))));
        Formula allEndpoints = All("t", phases, All("u", phases,
            Logic(All("w", Field(n, "V"), All("p", Call("NPath", n, v, w), endpoints)),
                FormulaLogicOperator.Iff,
                Equal(Call("boundary", n, v, t), Call("boundary", n, v, u)))));
        return Disp(All("N", Constant("Network"), All("v", Field(n, "V"),
            Conjoin(pathEndpoints, allEndpoints))));
    }

    private static Formula Field(Formula value, string field) => Seq(value, Dot, F.Id(field));

    private static Formula Constant(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));

    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Relation(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);

    private static Formula Logic(Formula left, FormulaLogicOperator operation, Formula right) =>
        new Formula.Logic(left, operation, right);

    private static Formula Conjoin(params Formula[] clauses) => clauses.Length == 1
        ? clauses[0]
        : Logic(clauses[0], FormulaLogicOperator.And, Conjoin(clauses[1..]));
}
