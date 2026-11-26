using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235301TransferDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer";
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Integers = Seq(Mathbb, Grp(F.Id("Z")));
    private static readonly Formula Type = F.Id("Type");
    private static readonly Formula State = F.Id("State");
    private static readonly Formula A = Alpha;
    private static readonly Formula HistA = Call("Hist", A);
    private static readonly Formula HistState = Call("Hist", State);
    private static readonly Formula Xs = F.Id("xs");
    private static readonly Formula Ys = F.Id("ys");
    private static readonly Formula Fn = F.Id("f");
    private static readonly Formula Weight = F.Id("c");
    private static readonly Formula Key = F.Id("key");
    private static readonly Formula S = F.Id("s");
    private static readonly Formula Ht = F.Id("h");
    private static readonly Formula W = F.Id("w");
    private static readonly Formula Empty = Seq(OpenBracket, CloseBracket);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted transfer of stress-three boundary words.",
        H("Weighted row transfer"),
        Blocks(
            Data("index", "index", "Column edge index", EdgeIndex(),
                "A mask bit represents the parity and ordered pair of letters of a column edge."),
            Data("par", "par", "Parity of an index", All(F.Id("n"), Nat,
                Eqn(Call("par", F.Id("n")), Call("decide", Par(Eqn(Call("mod", F.Id("n"), D(2)), D(1)))))),
                "The Boolean is true at odd indices."),
            Lemma("par-succ", "par_succ", "Parity of the successor", All(F.Id("n"), Nat,
                Eqn(Call("par", Seq(F.Id("n"), Plus, D(1))), Call("not", Call("par", F.Id("n"))))),
                "Each step in the column continuation count flips the parity."),
            Data("state", "State", "Transfer state", Typed(State, Type),
                "The record fields are parity of type Bool, last of type Fin 6, and mask of type Nat. "
                + "The mask stores the surviving column edges, indexed by parity and the two letters."),
            Data("hist", "Hist", "Signed history", All(A, Type,
                Eqn(HistA, Call("List", Seq(A, Sp, Times, Sp, Integers)))),
                "A history is an ordered list of states with integer weights."),
            Data("eval-hist", "evalHist", "History evaluation",
                OnHistory(All(Fn, Arrow(A, Integers), Eqn(Eval(Xs, Fn),
                    Call("sum", Call("map", Par(Lam(Seq(Open, S, Comma, F.Id("x"), Close),
                        Seq(F.Id("x"), Cdot, Sp, Apply(Fn, S)))), Xs))))),
                "The sum includes the contribution of every list entry, including repeats."),
            Data("scale-hist", "scaleHist", "Scaling a signed history", OnHistory(All(Weight, Integers,
                Eqn(Call("scaleHist", Weight, Xs),
                    Call("map", Par(Lam(Seq(Open, S, Comma, F.Id("x"), Close),
                        Seq(Open, S, Comma, Sp, Weight, Cdot, Sp, F.Id("x"), Close))), Xs)))),
                "Scaling multiplies every weight by the same integer and retains the list order."),
            Data("normalize", "normalize", "Normalization",
                All(A, Type, Seq(OpenBracket, Call("DecidableEq", A), CloseBracket, Sp,
                    Typed(F.Id("normalize"), Arrow(Par(Arrow(A, Nat)), Arrow(HistA, HistA))))),
                "The implementation merges singleton runs using the supplied natural-valued key, "
                + "combines adjacent identical states, and drops zero weights."),
            Data("state-key", "stateKey", "State key", All(S, State,
                Eqn(Call("stateKey", S), Seq(D(1,2), Cdot, Sp, Field("mask", S), Plus,
                    D(6), Cdot, Sp, Call("toNat", Field("parity", S)), Plus, Call("val", Field("last", S))))),
                "The key orders by mask, then parity, then last letter."),
            Data("step-hist", "stepHist", "One transfer step",
                Typed(F.Id("stepHist"), Arrow(HistState, HistState)),
                "For each weighted state and each next letter a, the new state flips parity, takes a "
                + "as last letter, and intersects the mask with legal edges for that crossing. "
                + "It retains the weight if a parity-zero edge out of column letter zero survives. "
                + "Concatenate the surviving successors and normalize with stateKey."),
            Data("action", "action", "Action on observables",
                Typed(F.Id("action"), Arrow(Par(Arrow(State, Integers)), Arrow(State, Integers))),
                "At state s, sum f on its surviving successors over the six choices of the next letter. "
                + "The survival rule is the same one used by stepHist."),
            Data("path", "path", "Row transfer history",
                All(Ht, Nat, Eqn(Call("path", Seq(Ht, Plus, D(1))),
                    Call("stepHist", Call("path", Ht)))),
                "The function has type Nat to Hist State. At zero its list contains the six states "
                + "in letter order, each with parity false, the corresponding last letter, "
                + "all 72 mask bits set and weight one."),
            Data("coefficients", "coefficients", "Signed coefficient history",
                All(F.Id("v"), Arrow(Nat, HistState),
                    Eqn(Call("coefficients", F.Id("v")), CoefficientHistory())),
                "The terms are concatenated in descending index order."),
            Data("residual-hist", "residualHist", "Residual history",
                All(Ht, Nat, Eqn(Residual(Ht), Call("normalize", F.Id("stateKey"),
                    Call("coefficients", Lam(F.Id("i"), Call("path", Seq(Ht, Plus, F.Id("i"), Plus, D(1)))))))),
                "The initial index of the path window is h plus one."),
            Data("group-mask", "groupMask", "Grouping by mask",
                All(Xs, HistState, Eqn(Call("groupMask", Xs), Call("normalize", F.Id("id"),
                    Call("map", Par(Lam(Seq(Open, S, Comma, F.Id("x"), Close),
                        Seq(Open, Field("mask", S), Comma, Sp, F.Id("x"), Close))), Xs)))),
                "The result is a signed history over natural-number masks."),
            Data("value", "value", "Acceptance at fixed width", Value(),
                "This integer sum counts words starting at zero whose consecutive column edges are "
                + "all present in the mask. Test-bit returns a Boolean."),
            Lemma("eval-nil", "eval_nil", "Empty history",
                All(A, Type, All(Fn, Arrow(A, Integers), Eqn(Eval(Empty, Fn), D(0)))),
                "The empty history has zero evaluation."),
            Lemma("eval-append", "eval_append", "Concatenated histories",
                OnHistory(All(Ys, HistA, All(Fn, Arrow(A, Integers),
                    Eqn(Eval(Append(Xs, Ys), Fn), Seq(Eval(Xs, Fn), Plus, Eval(Ys, Fn)))))),
                "Evaluation adds across concatenation."),
            Lemma("eval-scale", "eval_scale", "Evaluation after scaling",
                OnHistory(All(Fn, Arrow(A, Integers), All(Weight, Integers,
                    Eqn(Eval(Call("scaleHist", Weight, Xs), Fn), Seq(Weight, Cdot, Sp, Eval(Xs, Fn)))))),
                "Every term acquires the same integer factor."),
            Lemma("eval-normalize", "eval_normalize", "Evaluation after normalization",
                All(A, Type, Seq(OpenBracket, Call("DecidableEq", A), CloseBracket, Sp,
                    All(Key, Arrow(A, Nat), All(Xs, HistA, All(Fn, Arrow(A, Integers),
                        Eqn(Eval(Call("normalize", Key, Xs), Fn), Eval(Xs, Fn))))))),
                "Merging the runs and combining equal states preserves evaluation for every observable."),
            Lemma("eval-group", "eval_group", "Evaluation by mask",
                All(Xs, HistState, All(Fn, Arrow(Nat, Integers), Eqn(Eval(Call("groupMask", Xs), Fn),
                    Eval(Xs, Lam(S, Apply(Fn, Field("mask", S))))))),
                "A mask observable gives the same evaluation before and after grouping."),
            Lemma("eval-residual-succ", "eval_residual_succ", "Residual propagation",
                All(Ht, Nat, All(Fn, Arrow(State, Integers),
                    Eqn(Eval(Residual(Seq(Ht, Plus, D(1))), Fn), Eval(Residual(Ht), Call("action", Fn))))),
                "Moving the residual window forward by one applies the transfer action to the observable."),
            Entry("count-transfer", "count_transfer", "Transfer equals the literal count",
                All(Ht, Nat, All(W, Nat, Seq(D(0), Lt, Ht, Sp, Implies, Sp, D(0), Lt, W, Sp, Implies, Sp,
                    Eqn(Par(Typed(Call("C", D(3), D(3), Ht, W), Integers)),
                        Eval(Call("path", Ht), Lam(S, Call("value", W, Field("mask", S)))))))),
                "By the boundary-word equivalence, each row word contributes the number of compatible "
                + "column words. At positive width, a discarded state has zero contribution.",
                DescribeRole.Theorem))));

    private static Formula EdgeIndex()
    {
        var p = F.Id("p");
        var a = F.Id("a");
        var b = F.Id("b");
        var letter = Call("Fin", D(6));
        return All(p, F.Id("Bool"), All(a, letter, All(b, letter,
            Eqn(Call("index", p, a, b), Seq(D(3, 6), Cdot, Sp, Call("toNat", p), Plus,
                D(6), Cdot, Sp, Call("val", a), Plus, Call("val", b))))));
    }

    private static Formula Value()
    {
        var m = F.Id("m");
        var c = F.Id("c");
        var j = F.Id("j");
        var bit = Seq(D(3,6), Cdot, Sp, Call("mod", Call("val", j), D(2)), Plus,
            D(6), Cdot, Sp, Call("val", Apply(c, Call("castSucc", j))), Plus,
            Call("val", Apply(c, Call("succ", j))));
        var accepts = Seq(Eqn(Apply(c, D(0)), D(0)), Sp, Land, Sp,
            All(j, Call("Fin", W), Eqn(Call("testBit", m, bit), F.Id("true"))));
        return All(W, Nat, All(m, Nat, Eqn(Call("value", W, m),
            Seq(Sum, Sub(Seq(c, InMacro, Sp, Call("Word", W))), Sp,
                Call("ite", Par(accepts), D(1), D(0))))));
    }

    private static Formula CoefficientHistory()
    {
        int[] weights = [1, -3, -17, 57, 86, -372, -76, 972, -360, -864, 576];
        return weights.Select((weight, i) =>
            Call("scaleHist", Number(weight), Apply(F.Id("v"), Number(10 - i)))).Aggregate(Append);
    }

    private static Formula Number(int value)
    {
        var digits = D((value < 0 ? -value : value).ToString(System.Globalization.CultureInfo.InvariantCulture)
            .Select(digit => (byte)(digit - '0')).ToArray());
        return value < 0 ? Seq(Minus, digits) : digits;
    }

    private static Formula OnHistory(Formula body) => All(A, Type, All(Xs, HistA, body));
    private static Formula Residual(Formula h) => Call("residualHist", h);
    private static Formula Eval(Formula history, Formula f) => Call("evalHist", history, f);
    private static Formula Field(string field, Formula s) => Call(field, s);
    private static Formula Sub(Formula body) => Seq(Underscore, Grp(body));
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Append(Formula left, Formula right) => Seq(left, Sp, Plus, Plus, Sp, right);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, F.Eq, Sp, right);
    private static Formula Typed(Formula term, Formula type) => Seq(term, Colon, Sp, type);
    private static Formula Arrow(Formula source, Formula target) => Seq(source, Sp, To, Sp, target);
    private static Formula All(Formula binder, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(binder, type), Comma, Sp, body);
    private static Formula Lam(Formula binder, Formula body) => Seq(LambdaLower, Sp, binder, Comma, Sp, body);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => Apply(Seq(Operatorname, Grp(F.Id(name))), args);

    private static DocumentBlock Data(string id, string name, string title, Formula statement, string text) =>
        Entry(id, name, title, statement, text, DescribeRole.Definition);
    private static DocumentBlock Lemma(string id, string name, string title, Formula statement, string text) =>
        Entry(id, name, title, statement, text, DescribeRole.Lemma);
    private static DocumentBlock Entry(string id, string name, string title, Formula statement, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + "." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
