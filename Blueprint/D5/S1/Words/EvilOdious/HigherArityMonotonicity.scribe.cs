using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.EvilOdious;

internal sealed class HigherArityMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/EvilOdious/HigherArityMonotonicity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/allouche2021evilodious");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered k-tuple representation counts over the evil and odious supports evolve in arity "
        + "by discrete convolution against binary-valued indicators satisfying adjacent-pair "
        + "complementation a(2q) + a(2q + 1) = 1. A general signed forward-difference identity "
        + "splits the convolution increment above any finite cutoff R into a nonnegative boundary "
        + "term, a finite prefix whose negative variation is bounded by V_R(f), and a tail bounded "
        + "below by floor((n - R + 1) / 2), forcing strict increase for all n >= R + 2 V_R(f) + 1 "
        + "and, under weak-composition binomial bounds on f, for all "
        + "n >= R + 2 choose(R + k - 1, k) + 1. Propagating from the sixfold thresholds r_6(n) < "
        + "r_6(n + 1) for n >= 37 and s_6(n) < s_6(n + 1) for n >= 5 yields explicit quantitative "
        + "strict monotonicity across every arity k >= 6, together with sharp odious strict "
        + "monotonicity s_k(n) < s_k(n + 1) for all k >= 6 and n >= k - 1 via the shifted odious "
        + "bijection s_k(n) = q_k(n - k).",
        H("Quantified finite-prefix convolution correction and higher-arity evil-odious monotonicity"),
        Blocks(
            DefNode("evil-ind", "evilInd",
                "Binary indicator of the evil support",
                EvilIndFormula(),
                "For each natural number n, evilInd n takes value 1 when thueMorse n = false "
                + "(even binary digit sum) and value 0 when thueMorse n = true."),
            DefNode("odious-ind", "odiousInd",
                "Binary indicator of the odious support",
                OdiousIndFormula(),
                "For each natural number n, odiousInd n takes value 1 when thueMorse n = true "
                + "(odd binary digit sum) and value 0 when thueMorse n = false."),
            DefNode("nat-conv", "natConv",
                "Discrete convolution of natural-valued sequences",
                NatConvFormula(),
                "Given sequences a, f : N -> N and index n : N, natConv a f n sums "
                + "a(j) f(n - j) over 0 <= j <= n using Finset.range (n + 1)."),
            DefNode("shifted-odious", "shiftedOdious",
                "Ordered tuple representation count over the shifted odious support",
                ShiftedOdiousFormula(),
                "Because 0 is evil and 1 is odious, shifting every positive odious coordinate x_i "
                + "to b_i = x_i - 1 maps ordered k-tuples of odious numbers summing to n >= k "
                + "bijectively onto ordered k-tuples b in Finset.Nat.antidiagonalTuple k (n - k) "
                + "satisfying thueMorse (b_i + 1) = true for all i, counted by shiftedOdious k."),
            DefNode("positive-evil-count", "positiveEvilCount",
                "Ordered tuple representation count over the positive shifted evil support E + 1",
                PositiveEvilCountFormula(),
                "For arity k and sum N, positiveEvilCount k N counts ordered k-tuples x summing "
                + "to N whose coordinates satisfy x_i >= 1 and thueMorse (x_i - 1) = false, "
                + "corresponding to ordered representations over E + 1 = {e + 1 : e in E}."),
            DefNode("positive-odious-count", "positiveOdiousCount",
                "Ordered tuple representation count over the positive shifted odious support O + 1",
                PositiveOdiousCountFormula(),
                "For arity k and sum N, positiveOdiousCount k N counts ordered k-tuples x summing "
                + "to N whose coordinates satisfy x_i >= 1 and thueMorse (x_i - 1) = true, "
                + "corresponding to ordered representations over O + 1 = {o + 1 : o in O}."),
            DefNode("fwd-diff", "fwdDiff",
                "Signed integer forward difference",
                FwdDiffFormula(),
                "For a natural-valued sequence f : N -> N and index m : N, fwdDiff f m casts "
                + "f(m + 1) and f(m) to Z before subtracting so negative increments on finite "
                + "prefixes are preserved without natural-number truncation."),
            DefNode("neg-part", "negPart",
                "Nonnegative integer negative part",
                NegPartFormula(),
                "For an integer u, negPart u = max(0, -u) isolates the magnitude of negative "
                + "excursions while assigning 0 to nonnegative values and satisfying "
                + "-negPart u <= u."),
            DefNode("prefix-var-int", "prefixVarInt",
                "Integer-valued cumulative negative forward-difference variation",
                PrefixVarIntFormula(),
                "On a finite prefix 0 <= m < R, prefixVarInt R f sums negPart (fwdDiff f m) in Z, "
                + "producing a nonnegative integer upper bound on the total downward variation of "
                + "f prior to the threshold R."),
            DefNode("prefix-var", "prefixVar",
                "Natural-valued cumulative negative forward-difference variation",
                PrefixVarFormula(),
                "Applying Int.toNat to the nonnegative sum prefixVarInt R f produces the natural "
                + "number prefixVar R f satisfying (prefixVar R f : Z) = prefixVarInt R f."),
            DefNode("evil-bound", "evilBound",
                "Recursive sufficient threshold sequence for higher-arity evil strict monotonicity",
                EvilBoundFormula(),
                "Seeded at evilBound 6 = 37 (with constant placeholder 37 below arity 6), "
                + "evilBound evolves for every k >= 6 by "
                + "evilBound (k + 1) = evilBound k + 2 choose(evilBound k + k - 1, k) + 1."),
            DefNode("odious-bound", "odiousBound",
                "Recursive sufficient threshold sequence for higher-arity odious strict monotonicity",
                OdiousBoundFormula(),
                "Seeded at odiousBound 6 = 5 (with constant placeholder 5 below arity 6), "
                + "odiousBound evolves for every k >= 6 by "
                + "odiousBound (k + 1) = odiousBound k + 2 choose(odiousBound k + k - 1, k) + 1."),
            AuthorThmNode("pair-convolution-and-bound", "evil_odious_pair_convolution_and_bound",
                "Adjacent-pair complementation, convolution recurrences, composition bounds, and positive shift",
                PairConvolutionAndBoundFormula(),
                "From thueMorse (2q) = thueMorse q and thueMorse (2q + 1) = !thueMorse q, both "
                + "evilInd and odiousInd take values in {0, 1}, satisfy adjacent-pair "
                + "complementation a(2q) + a(2q + 1) = 1, and agree with r_1 and s_1. Partitioning "
                + "Finset.Nat.antidiagonalTuple (k + 1) n fiberwise by the initial coordinate j "
                + "and pairing fibers with Finset.Nat.antidiagonalTuple k (n - j) via Fin.cons and "
                + "Fin.tail establishes r_{k + 1} = natConv evilInd r_k, "
                + "s_{k + 1} = natConv odiousInd s_k, and weak-composition cardinality "
                + "choose(n + k - 1, k - 1) for k >= 1, whence r_k(n) and s_k(n) are bounded above "
                + "by choose(n + k - 1, k - 1). Coordinatewise addition of 1 gives "
                + "positiveEvilCount k (n + k) = r_k(n) and positiveOdiousCount k (n + k) = s_k(n)."),
            AuthorThmNode("quantified-finite-prefix-correction",
                "quantified_finite_prefix_correction",
                "Quantified finite-prefix convolution correction and binomial variation bound",
                QuantifiedPrefixCorrectionFormula(),
                "Under adjacent-pair complementation a(2q) + a(2q + 1) = 1 in N, every value a(m) "
                + "lies in {0, 1} and every prefix of length L satisfies sum_{j < L} a(j) >= "
                + "floor(L / 2). Assuming fwdDiff f m >= 1 for all m >= R, splitting the exact "
                + "convolution difference fwdDiff (natConv a f) n at n >= R into the boundary term "
                + "a(n + 1) f(0), the reflected finite prefix 0 <= m < R, and the tail "
                + "0 <= j <= n - R yields the three-tier lower bound "
                + "a(n + 1) f(0) + floor((n - R + 1) / 2) - prefixVarInt R f <= "
                + "fwdDiff (natConv a f) n, forcing fwdDiff (natConv a f) n >= 1 for all "
                + "n >= R + 2 prefixVar R f + 1. When f(m) <= choose(m + k - 1, k - 1) with "
                + "k >= 1, bounding negPart (fwdDiff f m) <= f(m) and summing by the cumulative "
                + "hockey-stick identity sum_{m < R} choose(m + k - 1, k - 1) = "
                + "choose(R + k - 1, k) gives prefixVar R f <= choose(R + k - 1, k) and strict "
                + "positivity of fwdDiff (natConv a f) n for n >= R + 2 choose(R + k - 1, k) + 1."),
            AuthorThmNode("higher-arity-strict-monotonicity",
                "higher_arity_evil_odious_strict_monotonicity",
                "Higher-arity quantitative strict monotonicity and sharp odious threshold",
                HigherArityStrictMonotonicityFormula(),
                "Combining the sixfold strict monotonicity bounds r_6(n) < r_6(n + 1) for n >= 37 "
                + "and s_6(n) < s_6(n + 1) for n >= 5 with evil_odious_pair_convolution_and_bound "
                + "and quantified_finite_prefix_correction propagates r_k(n) < r_k(n + 1) for all "
                + "k >= 6 and n >= evilBound k, with evilBound 7 = 38 + 2 choose(42, 6). On the "
                + "odious branch, because 0 is not odious and 1 is odious, s_k(n) = 0 for n < k "
                + "while s_k(n) = shiftedOdious k (n - k) for n >= k with shiftedOdious k 0 = 1. "
                + "Since s_6 is strictly increasing from n = 5 <= 6, shiftedOdious 6 is strictly "
                + "increasing on all of N; convolving against the shifted indicator b(j) with "
                + "b(0) = 1 preserves global strict increase of shiftedOdious k for every k >= 6, "
                + "giving sharp odious strict monotonicity s_k(n) < s_k(n + 1) for all n >= k - 1 "
                + "and therefore also above odiousBound k >= k - 1 (with odiousBound 7 = 426).")),
        []));

    private static DocumentBlock DefNode(string id, string name, string title, Formula formula,
        string prose) => Describe.Lean(
            DescribeId.Create("ham-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static DocumentBlock AuthorThmNode(string id, string name, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create("ham-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Dotted(string a, string b) => Seq(Named(a), Dot, Named(b));
    private static Formula Dotted3(string a, string b, string c) =>
        Seq(Named(a), Dot, Named(b), Dot, Named(c));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula fn, params Formula[] args) =>
        new Formula.Apply(fn, [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Cast(Formula v, Formula t) => Par(Seq(v, Sp, Colon, Sp, t));
    private static Formula FuncType(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula FloorDiv(Formula a, Formula b) =>
        Par(Seq(Par(a), Sp, Slash, Sp, b));
    private static Formula NegOf(Formula x) => new Formula.Negate(x);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula OrOf(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula AndAll(params Formula[] items)
    {
        var acc = items[^1];
        for (var idx = items.Length - 2; idx >= 0; idx--)
            acc = new Formula.Logic(Par(items[idx]), FormulaLogicOperator.And, Par(acc));
        return acc;
    }
    private static Formula All(string v, Formula dom, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), dom, body);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula NatSeq() => FuncType(Nats(), Nats());
    private static Formula FinOf(Formula k) => Call("Fin", k);
    private static Formula Ite(Formula cond, Formula t, Formula e) =>
        Seq(Named("if"), Sp, cond, Sp, Named("then"), Sp, t, Sp, Named("else"), Sp, e);
    private static Formula SumRange(string idx, Formula upper, Formula summand) =>
        Seq(Sum, Underscore,
            Grp(Seq(F.Id(idx), Sp, InMacro, Sp, App(Dotted("Finset", "range"), upper))),
            Sp, summand);
    private static Formula ChooseOf(Formula n, Formula k) =>
        App(Dotted("Nat", "choose"), n, k);
    private static Formula TupleFilterCard(Formula k, Formula sum, string tupleVar, Formula pred)
    {
        Formula tupleDom = FuncType(FinOf(k), Nats());
        Formula baseSet = App(Dotted3("Finset", "Nat", "antidiagonalTuple"), k, sum);
        Formula lam = Par(Seq(Named("fun"), Sp, Cast(F.Id(tupleVar), tupleDom), Sp, Mapsto, Sp,
            All("i", FinOf(k), pred)));
        return Seq(Par(Seq(Par(baseSet), Dot, Named("filter"), Sp, lam)), Dot, Named("card"));
    }

    private static Formula EvilIndFormula()
    {
        Formula n = F.Id("n");
        return All("n", Nats(),
            Eqn(Call("evilInd", n),
                Ite(Eqn(Call("thueMorse", n), Named("false")), Num(1), Num(0))));
    }

    private static Formula OdiousIndFormula()
    {
        Formula n = F.Id("n");
        return All("n", Nats(),
            Eqn(Call("odiousInd", n),
                Ite(Eqn(Call("thueMorse", n), Named("true")), Num(1), Num(0))));
    }

    private static Formula NatConvFormula()
    {
        Formula a = F.Id("a"), f = F.Id("f"), n = F.Id("n"), j = F.Id("j");
        return All("a", NatSeq(), All("f", NatSeq(), All("n", Nats(),
            Eqn(Call("natConv", a, f, n),
                SumRange("j", Add(n, Num(1)),
                    Mul(App(a, j), App(f, Sub(n, j))))))));
    }

    private static Formula ShiftedOdiousFormula()
    {
        Formula k = F.Id("k"), m = F.Id("m"), b = F.Id("b"), i = F.Id("i");
        return All("k", Nats(), All("m", Nats(),
            Eqn(Call("shiftedOdious", k, m),
                TupleFilterCard(k, m, "b",
                    Eqn(Call("thueMorse", Add(App(b, i), Num(1))), Named("true"))))));
    }

    private static Formula PositiveEvilCountFormula()
    {
        Formula k = F.Id("k"), N = F.Id("N"), x = F.Id("x"), i = F.Id("i");
        return All("k", Nats(), All("N", Nats(),
            Eqn(Call("positiveEvilCount", k, N),
                TupleFilterCard(k, N, "x",
                    AndAll(LeOf(Num(1), App(x, i)),
                        Eqn(Call("thueMorse", Sub(App(x, i), Num(1))), Named("false")))))));
    }

    private static Formula PositiveOdiousCountFormula()
    {
        Formula k = F.Id("k"), N = F.Id("N"), x = F.Id("x"), i = F.Id("i");
        return All("k", Nats(), All("N", Nats(),
            Eqn(Call("positiveOdiousCount", k, N),
                TupleFilterCard(k, N, "x",
                    AndAll(LeOf(Num(1), App(x, i)),
                        Eqn(Call("thueMorse", Sub(App(x, i), Num(1))), Named("true")))))));
    }

    private static Formula FwdDiffFormula()
    {
        Formula f = F.Id("f"), m = F.Id("m");
        return All("f", NatSeq(), All("m", Nats(),
            Eqn(Call("fwdDiff", f, m),
                Sub(Cast(App(f, Add(m, Num(1))), Ints()), Cast(App(f, m), Ints())))));
    }

    private static Formula NegPartFormula()
    {
        Formula u = F.Id("u");
        return All("u", Ints(),
            Eqn(Call("negPart", u), Call("max", Cast(Num(0), Ints()), NegOf(u))));
    }

    private static Formula PrefixVarIntFormula()
    {
        Formula R = F.Id("R"), f = F.Id("f"), m = F.Id("m");
        return All("R", Nats(), All("f", NatSeq(),
            Eqn(Call("prefixVarInt", R, f),
                SumRange("m", R, Call("negPart", Call("fwdDiff", f, m))))));
    }

    private static Formula PrefixVarFormula()
    {
        Formula R = F.Id("R"), f = F.Id("f");
        return All("R", Nats(), All("f", NatSeq(),
            Eqn(Call("prefixVar", R, f),
                Seq(Par(Call("prefixVarInt", R, f)), Dot, Named("toNat")))));
    }

    private static Formula EvilBoundFormula()
    {
        Formula k = F.Id("k"), eb = Call("evilBound", k);
        return AndAll(
            Eqn(Call("evilBound", Num(0)), Num(37)),
            All("k", Nats(),
                Eqn(Call("evilBound", Add(k, Num(1))),
                    Ite(LtOf(k, Num(6)), Num(37),
                        Add(Add(eb, Mul(Num(2), ChooseOf(Sub(Add(eb, k), Num(1)), k))),
                            Num(1))))));
    }

    private static Formula OdiousBoundFormula()
    {
        Formula k = F.Id("k"), ob = Call("odiousBound", k);
        return AndAll(
            Eqn(Call("odiousBound", Num(0)), Num(5)),
            All("k", Nats(),
                Eqn(Call("odiousBound", Add(k, Num(1))),
                    Ite(LtOf(k, Num(6)), Num(5),
                        Add(Add(ob, Mul(Num(2), ChooseOf(Sub(Add(ob, k), Num(1)), k))),
                            Num(1))))));
    }

    private static Formula QuantifiedPrefixCorrectionFormula()
    {
        Formula a = F.Id("a"), f = F.Id("f"), R = F.Id("R"), q = F.Id("q"), m = F.Id("m"),
            n = F.Id("n"), j = F.Id("j"), k = F.Id("k");
        Formula ha = All("q", Nats(),
            Eqn(Add(App(a, Mul(Num(2), q)), App(a, Add(Mul(Num(2), q), Num(1)))), Num(1)));
        Formula hf = All("m", Nats(),
            Imp(LeOf(R, m), LeOf(Cast(Num(1), Ints()), Call("fwdDiff", f, m))));
        Formula bin = All("m", Nats(), OrOf(Eqn(App(a, m), Num(0)), Eqn(App(a, m), Num(1))));
        Formula castEq = Eqn(Cast(Call("prefixVar", R, f), Ints()), Call("prefixVarInt", R, f));
        Formula gDiff = Call("fwdDiff", Call("natConv", a, f), n);
        Formula endTerm = Mul(Cast(App(a, Add(n, Num(1))), Ints()), Cast(App(f, Num(0)), Ints()));
        Formula halfTail = Cast(FloorDiv(Add(Sub(n, R), Num(1)), Num(2)), Ints());
        Formula prefSigned = SumRange("m", R,
            Mul(Cast(App(a, Sub(n, m)), Ints()), Call("fwdDiff", f, m)));
        Formula tailSigned = SumRange("j", Add(Sub(n, R), Num(1)),
            Mul(Cast(App(a, j), Ints()), Call("fwdDiff", f, Sub(n, j))));
        Formula prefWeighted = SumRange("m", R,
            Mul(Cast(App(a, Sub(n, m)), Ints()), Call("negPart", Call("fwdDiff", f, m))));
        Formula tier2Lhs = Sub(Add(endTerm, halfTail), prefWeighted);
        Formula tier3Lhs = Sub(Add(endTerm, halfTail), Call("prefixVarInt", R, f));
        Formula tiers = All("n", Nats(), Imp(LeOf(R, n), AndAll(
            Eqn(gDiff, Add(Add(endTerm, prefSigned), tailSigned)),
            LeOf(tier2Lhs, gDiff),
            LeOf(tier3Lhs, tier2Lhs),
            LeOf(tier3Lhs, gDiff))));
        Formula genThresh = All("n", Nats(),
            Imp(LeOf(Add(Add(R, Mul(Num(2), Call("prefixVar", R, f))), Num(1)), n),
                LeOf(Cast(Num(1), Ints()), gDiff)));
        Formula hockey = All("k", Nats(), Imp(LeOf(Num(1), k),
            Eqn(SumRange("m", R, ChooseOf(Sub(Add(m, k), Num(1)), Sub(k, Num(1)))),
                ChooseOf(Sub(Add(R, k), Num(1)), k))));
        Formula binomSpec = All("k", Nats(), Imp(LeOf(Num(1), k),
            Imp(All("m", Nats(), LeOf(App(f, m), ChooseOf(Sub(Add(m, k), Num(1)), Sub(k, Num(1))))),
                AndAll(
                    LeOf(Call("prefixVar", R, f), ChooseOf(Sub(Add(R, k), Num(1)), k)),
                    All("n", Nats(),
                        Imp(LeOf(Add(Add(R, Mul(Num(2), ChooseOf(Sub(Add(R, k), Num(1)), k))),
                                Num(1)), n),
                            LeOf(Cast(Num(1), Ints()), gDiff)))))));
        return All("a", NatSeq(), All("f", NatSeq(), All("R", Nats(),
            Imp(ha, Imp(hf, AndAll(bin, castEq, tiers, genThresh, hockey, binomSpec))))));
    }

    private static Formula PairConvolutionAndBoundFormula()
    {
        Formula q = F.Id("q"), n = F.Id("n"), k = F.Id("k"), rFn = F.Id("r"), sFn = F.Id("s");
        Formula pairEvil = All("q", Nats(),
            Eqn(Add(Call("evilInd", Mul(Num(2), q)),
                    Call("evilInd", Add(Mul(Num(2), q), Num(1)))),
                Num(1)));
        Formula pairOdious = All("q", Nats(),
            Eqn(Add(Call("odiousInd", Mul(Num(2), q)),
                    Call("odiousInd", Add(Mul(Num(2), q), Num(1)))),
                Num(1)));
        Formula arityOne = All("n", Nats(), AndAll(
            OrOf(Eqn(Call("evilInd", n), Num(0)), Eqn(Call("evilInd", n), Num(1))),
            OrOf(Eqn(Call("odiousInd", n), Num(0)), Eqn(Call("odiousInd", n), Num(1))),
            Eqn(App(rFn, Num(1), n), Call("evilInd", n)),
            Eqn(App(sFn, Num(1), n), Call("odiousInd", n))));
        Formula convStep = All("k", Nats(), All("n", Nats(), AndAll(
            Eqn(App(rFn, Add(k, Num(1)), n),
                Call("natConv", Named("evilInd"), Par(App(rFn, k)), n)),
            Eqn(App(sFn, Add(k, Num(1)), n),
                Call("natConv", Named("odiousInd"), Par(App(sFn, k)), n)))));
        Formula binomBound = All("k", Nats(), All("n", Nats(),
            Imp(LeOf(Num(1), k), AndAll(
                LeOf(App(rFn, k, n), ChooseOf(Sub(Add(n, k), Num(1)), Sub(k, Num(1)))),
                LeOf(App(sFn, k, n), ChooseOf(Sub(Add(n, k), Num(1)), Sub(k, Num(1))))))));
        Formula posShift = All("k", Nats(), All("n", Nats(), AndAll(
            Eqn(Call("positiveEvilCount", k, Add(n, k)), App(rFn, k, n)),
            Eqn(Call("positiveOdiousCount", k, Add(n, k)), App(sFn, k, n)))));
        return AndAll(pairEvil, pairOdious, arityOne, convStep, binomBound, posShift);
    }

    private static Formula HigherArityStrictMonotonicityFormula()
    {
        Formula k = F.Id("k"), m = F.Id("m"), n = F.Id("n"), rFn = F.Id("r"), sFn = F.Id("s");
        Formula eb = Call("evilBound", k), ob = Call("odiousBound", k);
        Formula baseE = Eqn(Call("evilBound", Num(6)), Num(37));
        Formula baseO = Eqn(Call("odiousBound", Num(6)), Num(5));
        Formula rec = All("k", Nats(), Imp(LeOf(Num(6), k), AndAll(
            Eqn(Call("evilBound", Add(k, Num(1))),
                Add(Add(eb, Mul(Num(2), ChooseOf(Sub(Add(eb, k), Num(1)), k))), Num(1))),
            Eqn(Call("odiousBound", Add(k, Num(1))),
                Add(Add(ob, Mul(Num(2), ChooseOf(Sub(Add(ob, k), Num(1)), k))), Num(1))))));
        Formula arity7E = Eqn(Call("evilBound", Num(7)),
            Add(Num(38), Mul(Num(2), ChooseOf(Num(42), Num(6)))));
        Formula arity7O = Eqn(Call("odiousBound", Num(7)), Num(426));
        Formula shiftBij = All("k", Nats(), Imp(LeOf(Num(1), k), AndAll(
            Eqn(Call("shiftedOdious", k, Num(0)), Num(1)),
            All("n", Nats(), Imp(LtOf(n, k), Eqn(App(sFn, k, n), Num(0)))),
            All("n", Nats(),
                Imp(LeOf(k, n),
                    Eqn(App(sFn, k, n), Call("shiftedOdious", k, Sub(n, k))))))));
        Formula qStrict = All("k", Nats(), Imp(LeOf(Num(6), k),
            All("m", Nats(),
                LtOf(Call("shiftedOdious", k, m), Call("shiftedOdious", k, Add(m, Num(1)))))));
        Formula sSharp = All("k", Nats(), Imp(LeOf(Num(6), k),
            All("n", Nats(),
                Imp(LeOf(Sub(k, Num(1)), n),
                    LtOf(App(sFn, k, n), App(sFn, k, Add(n, Num(1))))))));
        Formula rMono = All("k", Nats(), Imp(LeOf(Num(6), k),
            All("n", Nats(),
                Imp(LeOf(eb, n),
                    LtOf(App(rFn, k, n), App(rFn, k, Add(n, Num(1))))))));
        Formula sMono = All("k", Nats(), Imp(LeOf(Num(6), k),
            All("n", Nats(),
                Imp(LeOf(ob, n),
                    LtOf(App(sFn, k, n), App(sFn, k, Add(n, Num(1))))))));
        return AndAll(baseE, baseO, rec, arity7E, arity7O, shiftBij, qStrict, sSharp, rMono, sMono);
    }
}
