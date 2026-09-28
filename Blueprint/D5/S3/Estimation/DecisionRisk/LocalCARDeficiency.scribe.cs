using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class LocalCARDeficiencyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A local change of a CAR profile preserves every pair readout and has two exact directed deficiencies.",
        H("Local CAR Deficiency"),
        Blocks(Describe.Lean(
            DescribeId.Create("local-car-deficiency"),
            DeclarationHandle.Create("D5/S3/Estimation/DecisionRisk/LocalCARDeficiency.result"),
            H("Exact local deficiencies in an arbitrary common background"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("A is any finite nonempty state set, and Block(A) consists of all nonempty subsets of A. "
                    + "For a profile w, experiment(w,i,B) is w(B) when i belongs to B and is zero otherwise. "
                    + "The profile is nonnegative and each experiment row sums to one. No partition-mixture representation is assumed.")),
                Paragraph(Text("Fix U contained in A with m = card(U) at least three. The local direction is one at U, "
                    + "m minus two at each singleton in U, minus one at each two-element block contained in U, and zero elsewhere. "
                    + "The new profile is v = w + a direction(U), where a is nonnegative. The capacity hypothesis applies only to "
                    + "the weight of each exact internal two-element block; it is not a bound on the sum of weights of all blocks containing that pair.")),
                new DocumentBlock.DisplayFormula(ProfileFormula()),
                Paragraph(Text("The common background is arbitrary, including blocks meeting both U and its complement. "
                    + "Every pair of distinct states in A has the same readout r before and after the change. "
                    + "The new profile is nonnegative and normalized at every state.")),
                new DocumentBlock.DisplayFormula(ReadoutFormula()),
                Paragraph(Text("finiteDeficiency takes its target experiment first and its source experiment second. "
                    + "It is the infimum, over all stochastic kernels on the full nonempty-block alphabet, of the maximum statewise half-L1 total-variation error. "
                    + "Thus finiteDeficiency(experiment(w),experiment(v)) describes simulation from v to w, and the reverse expression describes simulation from w to v. "
                    + "The lower bounds in the statement hold separately for every unrestricted kernel, including kernels that output target zero-weight blocks or blocks not containing the true state.")),
                Paragraph(Text("There is one globally defined attaining kernel in each direction, used for all states simultaneously. "
                    + "Write Q for the two-element blocks contained in U, let delta(B,C) be one when B equals C and zero otherwise, "
                    + "and write indicator(P) for the indicator of a condition. Set b(B) = w(B) - a indicator(B in Q). "
                    + "The following probability rows and nonnegative mass flows give explicit attaining kernels.")),
                new DocumentBlock.DisplayFormula(KernelFormula()),
                Paragraph(Text("P is uniform on Q, and S(j) is uniform on its blocks containing j, for j in U. "
                    + "The row sums of FP and FM are respectively v(B) and w(B). When an input weight is zero, its entire nonnegative flow row is zero; "
                    + "the displayed identity row completes the kernel on that input. Consequently both kernels are defined on every input block. "
                    + "For a = 0 both constructions are the identity kernel and both errors are zero. No division by a is required.")),
                Paragraph(Text("KP has error ep = a(m-2)/m at every state in U and zero error at every state outside U. "
                    + "KM has error em = a(m-2)/2 at every state in U and zero outside U. "
                    + "Both retain every background block outside the changed coordinates, including all crossing blocks.")),
                Paragraph(Text("For optimality, put k(B) = card(B intersect U). Two bounded losses on the full output alphabet have optimal "
                    + "unnormalized block costs max(k(B)-2,0) and, respectively, zero for k(B) at most one and k(B)/2 otherwise. "
                    + "The identity decision attains each block cost. Averaging over the uniform prior on U gives risk gaps ep in the first direction and em in the second. "
                    + "All unchanged background terms cancel separately. Bounded-loss risk transport bounds each gap by the maximum statewise simulation error of every stochastic kernel, "
                    + "giving the two lower bounds and hence equality with the explicit upper bounds."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula A = F.Id("A"), U = F.Id("U"), a = F.Id("a"), w = F.Id("w"), v = F.Id("v");
        Formula B = F.Id("B"), i = F.Id("i"), j = F.Id("j"), K = F.Id("K");
        Formula KP = F.Id("KP"), KM = F.Id("KM"), ep = F.Id("ep"), em = F.Id("em");
        Formula blocks = Call("Block", A), kernel = Call("FiniteMarkovKernel", blocks, blocks);
        Formula ew = Call("experiment", w), ev = Call("experiment", v);
        Formula hypotheses = And(
            LeF(D(3), Call("card", U)), LeF(D(0), a),
            All(B, blocks, LeF(D(0), Apply(w, B))),
            All(i, A, Eqn(Call("sum", B, blocks, Call("experiment", w, i, B)), D(1))),
            All(B, blocks, Implies(Call("subset", B, U), Eqn(Call("card", B), D(2)), LeF(a, Apply(w, B)))));
        Formula conclusions = And(
            All(B, blocks, LeF(D(0), Apply(v, B))),
            All(i, A, Eqn(Call("sum", B, blocks, Call("experiment", v, i, B)), D(1))),
            All(i, A, All(j, A, Implies(Seq(i, Sp, Neq, Sp, j),
                Eqn(Call("r", v, i, j), Call("r", w, i, j))))),
            Eqn(Call("finiteDeficiency", ew, ev), Call("ofReal", ep)),
            Eqn(Call("finiteDeficiency", ev, ew), Call("ofReal", em)),
            Seq(Exists, Sp, KP, Comma, Sp, KM, Colon, Sp, kernel, Comma, RowBreak, Grp(),
                And(
                    All(i, A, Eqn(Call("totalVariation", Apply(ew, i),
                        Call("channelOutput", Projection(KP), Apply(ev, i))),
                        Call("ite", Call("member", i, U), ep, D(0)))),
                    All(i, A, Eqn(Call("totalVariation", Apply(ev, i),
                        Call("channelOutput", Projection(KM), Apply(ew, i))),
                        Call("ite", Call("member", i, U), em, D(0)))),
                    All(K, kernel, LeF(ep, Call("uniformSimulationError", ew, ev, K))),
                    All(K, kernel, LeF(em, Call("uniformSimulationError", ev, ew, K))))));
        Formula m = Call("card", U);
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            All(A, Call("Type"), Implies(Call("Fintype", A), Call("DecidableEq", A), Call("Nonempty", A),
                All(U, Call("Finset", A), All(a, Real(), All(w, Seq(blocks, Sp, To, Sp, Real()),
                    Implies(hypotheses, LetIn([
                        Eqn(v, Call("plus", w, U, a)),
                        Eqn(ep, Div(Mul(a, Paren(Sub(m, D(2)))), m)),
                        Eqn(em, Div(Mul(a, Paren(Sub(m, D(2)))), D(2)))], conclusions))))))),
            Dot, End, Grp(F.Id("gathered"))));
    }

    private static Formula ProfileFormula()
    {
        Formula B = F.Id("B"), U = F.Id("U"), w = F.Id("w"), a = F.Id("a");
        Formula small = AndInline(Call("subset", B, U), Eqn(Call("card", B), D(1)));
        Formula pair = AndInline(Call("subset", B, U), Eqn(Call("card", B), D(2)));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Eqn(Call("direction", U, B), Call("ite", Eqn(B, U), D(1),
                Call("ite", small, Sub(Call("card", U), D(2)), Call("ite", pair, Seq(Minus, D(1)), D(0))))),
            RowBreak, Grp(), Eqn(Call("plus", w, U, a, B),
                Add(Apply(w, B), Mul(a, Call("direction", U, B)))),
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ReadoutFormula()
    {
        Formula B = F.Id("B"), A = F.Id("A"), w = F.Id("w"), i = F.Id("i"), j = F.Id("j");
        return Disp(Eqn(Call("r", w, i, j), Call("sum", B, Call("Block", A),
            Call("ite", AndInline(Call("member", i, B), Call("member", j, B)), Apply(w, B), D(0)))));
    }

    private static Formula KernelFormula()
    {
        Formula B = F.Id("B"), C = F.Id("C"), U = F.Id("U"), j = F.Id("j"), m = F.Id("m"), a = F.Id("a");
        Formula w = F.Id("w"), v = F.Id("v"), b = F.Id("b"), Q = F.Id("Q");
        Formula pairC = Call("member", C, Q), pairB = Call("member", B, Q);
        Formula indicator(Formula p) => Call("indicator", p);
        Formula delta(Formula x, Formula y) => Call("delta", x, y);
        Formula sing = Call("singleton", j);
        Formula fp = Add(Mul(Apply(b, B), delta(B, C)),
            Mul(a, indicator(Eqn(B, U)), Call("P", C)),
            Mul(a, Paren(Sub(m, D(2))), Call("sum", j, U,
                Mul(indicator(Eqn(B, sing)), Call("S", j, C)))));
        Formula fm = Add(Mul(Apply(b, B), delta(B, C)),
            Mul(a, indicator(pairB), Paren(Add(
                Div(delta(U, C), Sub(m, D(1))),
                Mul(Div(Sub(m, D(2)), Mul(D(2), Paren(Sub(m, D(1))))),
                    Call("sum", j, B, delta(sing, C)))))));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Eqn(m, Call("card", U)), Comma, Sp,
            Eqn(Apply(b, B), Sub(Apply(w, B), Mul(a, indicator(pairB)))), RowBreak, Grp(),
            Eqn(Call("P", C), Mul(indicator(pairC), Div(D(2), Mul(m, Paren(Sub(m, D(1))))))), RowBreak, Grp(),
            Eqn(Call("S", j, C), Div(indicator(AndInline(pairC, Call("member", j, C))), Sub(m, D(1)))), RowBreak, Grp(),
            Eqn(Call("FP", B, C), fp), RowBreak, Grp(),
            Eqn(Call("FM", B, C), fm), RowBreak, Grp(),
            Eqn(Call("KP", B, C), Call("ite", Eqn(Apply(v, B), D(0)), delta(B, C), Div(Call("FP", B, C), Apply(v, B)))), RowBreak, Grp(),
            Eqn(Call("KM", B, C), Call("ite", Eqn(Apply(w, B), D(0)), delta(B, C), Div(Call("FM", B, C), Apply(w, B)))),
            End, Grp(F.Id("gathered"))));
    }

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Projection(Formula value) => Seq(value, Dot, D(1));
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula LeF(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Div(Formula numerator, Formula denominator) => Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Add(params Formula[] values) => Infix(Plus, values);
    private static Formula Sub(params Formula[] values) => Infix(Minus, values);
    private static Formula Mul(params Formula[] values) => Infix(Cdot, values);
    private static Formula AndInline(params Formula[] values) => Infix(Land, values);
    private static Formula Infix(Formula op, Formula[] values)
    {
        var items = new List<Formula>();
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, op, Sp]);
            items.Add(values[i]);
        }
        return Seq([.. items]);
    }
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula> { Open };
        for (var i = 0; i < clauses.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Land, RowBreak, Grp()]);
            items.AddRange([Open, clauses[i], Close]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Implies(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var i = 0; i < clauses.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Rightarrow, RowBreak, Grp()]);
            items.AddRange([Open, clauses[i], Close]);
        }
        return Seq([.. items]);
    }
    private static Formula LetIn(Formula[] definitions, Formula body) => Seq(
        F.Text, Grp(F.Id("let"), Sp), Infix(Comma, definitions), Sp,
        F.Text, Grp(Sp, F.Id("in"), Sp), RowBreak, Grp(), body);
}
