using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class LaplacianTwoLevelTreeSharpTransferDecayDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/coutinho2025peak");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Across all two-level rooted trees T(k, l) with k >= 2 and l >= 1 and all real times t, "
        + "the scaled root-to-leaf Laplacian transfer probability n^(3/2) P_{k, l}(t) has global "
        + "supremum C_* = 2 + 6 sqrt(5) / 5, realized already by the time supremum on the single "
        + "five-vertex tree T(2, 1) along an explicit Pell phase-alignment sequence "
        + "t_j -> +infinity yet strictly unattained at every finite time because of an integer "
        + "parity obstruction. Restricting to trees of order n >= N drives both the scaled "
        + "spectral-bound tail supremum and the scaled transfer-probability tail supremum to 1 as "
        + "N -> +infinity, yielding uniform (1 + epsilon) n^(-3/2) decay while ruling out "
        + "O(n^(-beta)) decay for every exponent beta > 3/2 via an infinite even-parameter family "
        + "attaining peak root-to-leaf transfer at time pi.",
        H("Non-attained Pell phase supremum and unit asymptotic tail decay for two-level trees"),
        Blocks(
            Node("scaled-transfer-set", "scaledTransferSet",
                "Global set of scaled root-to-leaf transfer probabilities",
                ScaledTransferSetFormula(),
                "The set scaledTransferSet collects all real values n^(3/2) P_{k, l}(t) as (k, l) "
                + "ranges over integers k >= 2 and l >= 1, (i, j) ranges over leaves of T(k, l), "
                + "and t ranges over all real times, where n = treeOrder k l = 1 + k(l + 1).",
                DescribeRole.Definition),
            Node("scaled-transfer-set-21", "scaledTransferSet21",
                "Scaled root-to-leaf transfer set on T(2, 1)",
                ScaledTransferSet21Formula(),
                "For a fixed leaf (i, j) of T(2, 1), whose order is n = 5, scaledTransferSet21 "
                + "i j collects all values 5^(3/2) P_{2, 1}(t) as t ranges over the real line.",
                DescribeRole.Definition),
            Node("pell-pair", "pellPair", "Pell-type integer recurrence approximating sqrt(5)",
                PellPairFormula(),
                "Starting from (p_0, m_0) = (2, 1), where 2 - sqrt(5) < 0 has unit norm in "
                + "Z[sqrt(5)], multiplying repeatedly by the totally positive fundamental square "
                + "unit 9 + 4 sqrt(5) = (2 + sqrt(5))^2 defines (p_{j + 1}, m_{j + 1}) = "
                + "(9 p_j + 20 m_j, 4 p_j + 9 m_j).",
                DescribeRole.Definition),
            Node("pell-p", "pellP", "Numerator sequence of the Pell phase approximation",
                PellPFormula(),
                "The first coordinate p_j = (pellPair j).1 is even for every j and satisfies "
                + "p_j - sqrt(5) m_j = (2 - sqrt(5))(9 - 4 sqrt(5))^j -> 0 as j -> +infinity.",
                DescribeRole.Definition),
            Node("pell-m", "pellM", "Denominator sequence of the Pell phase approximation",
                PellMFormula(),
                "The second coordinate m_j = (pellPair j).2 is odd, strictly increasing, and "
                + "bounded below by 9^j, ensuring that 3 m_j - p_j is an odd integer for every j.",
                DescribeRole.Definition),
            Node("b-star", "bStar",
                "Upper positive root-supported Laplacian eigenvalue on T(2, 1)",
                BStarFormula(),
                "On T(2, 1) the trace parameter is S = 5 and the discriminant is d = sqrt(5), so "
                + "the upper positive root-supported eigenvalue is b_* = (5 + sqrt(5)) / 2, while "
                + "the lower eigenvalue a_* = (5 - sqrt(5)) / 2 satisfies a_* / b_* = "
                + "(3 - sqrt(5)) / 2.",
                DescribeRole.Definition),
            Node("approx-time", "approxTime", "Pell phase-alignment times on T(2, 1)",
                ApproxTimeFormula(),
                "Setting t_j = 2 pi m_j / b_* aligns the upper frequency exactly at "
                + "exp(i b_* t_j) = exp(2 pi i m_j) = 1 while driving the lower frequency "
                + "a_* t_j = pi(3 m_j - p_j) + pi(p_j - sqrt(5) m_j) modulo 2 pi toward pi.",
                DescribeRole.Definition),
            Node("tail-bounding-set", "tailBoundingSet",
                "Tail set of scaled squared spectral bounds above threshold N",
                TailBoundingSetFormula(),
                "For a real order threshold N, tailBoundingSet N collects all scaled squared "
                + "bounding entries n^(3/2) B_{k, l}^2 over parameters k >= 2, l >= 1 with "
                + "n = treeOrder k l >= N and leaves (i, j).",
                DescribeRole.Definition),
            Node("tail-transfer-set", "tailTransferSet",
                "Tail set of scaled root-to-leaf transfer probabilities above threshold N",
                TailTransferSetFormula(),
                "For a real order threshold N, tailTransferSet N collects all scaled transfer "
                + "probabilities n^(3/2) P_{k, l}(t) over parameters k >= 2, l >= 1 with "
                + "n = treeOrder k l >= N, leaves (i, j), and real times t.",
                DescribeRole.Definition),
            Node("tail-bounding-sup", "tailBoundingSup",
                "Tail supremum of scaled squared spectral bounds",
                TailBoundingSupFormula(),
                "The function tailBoundingSup N = sSup(tailBoundingSet N) records the supremum "
                + "M_B(N) of n^(3/2) B_{k, l}^2 over all two-level trees of order at least N.",
                DescribeRole.Definition),
            Node("tail-transfer-sup", "tailTransferSup",
                "Tail supremum of scaled root-to-leaf transfer probabilities",
                TailTransferSupFormula(),
                "The function tailTransferSup N = sSup(tailTransferSet N) records the supremum "
                + "M_P(N) of n^(3/2) P_{k, l}(t) over all two-level trees of order at least N "
                + "and all real times t.",
                DescribeRole.Definition),
            Node("tail-threshold-d", "tailThresholdD",
                "Discriminant lower-bound threshold as a function of tree order",
                TailThresholdDFormula(),
                "For N >= 4, every two-level tree with k >= 2, l >= 1, and 1 + k(l + 1) >= N "
                + "satisfies k + l + 1 >= 2 sqrt(N - 1) and (k - l)^2 + 4 l >= 2(k + l + 1) - 3, "
                + "so its discriminant specD k l is bounded below by "
                + "D_N = max(sqrt(5), sqrt(4 sqrt(N - 1) - 3)).",
                DescribeRole.Definition),
            Node("supremum-and-pell", "sharp_transfer_supremum_and_pell_approx",
                "Global supremum C_*, strict finite-time non-attainment, and Pell convergence",
                SupremumAndPellFormula(),
                "The approximation times t_m = 2 pi m_m / b_* are strictly increasing and diverge "
                + "to +infinity. For every k >= 2, l >= 1, leaf (i, j), and real time t, one has "
                + "the strict inequality n^(3/2) P_{k, l}(t) < C_*: when (k, l) != (2, 1), the "
                + "uniqueness clause of sharp_global_spectral_transfer_bound gives "
                + "n^(3/2) B_{k, l}^2 < C_*; when (k, l) = (2, 1), expanding "
                + "B_{2, 1}^2 - P_{2, 1}(t) as the sum of three nonnegative cosine-gap terms "
                + "2 c A_0(1 + cos(a_* t)) + 2 c B_0(1 - cos(b_* t)) + "
                + "2 A_0 B_0(1 + cos((a_* - b_*) t)) shows that equality would force "
                + "a_* t = (2 u + 1) pi and b_* t = 2 v pi for integers u, v, leading to the "
                + "impossible integer parity equation (4 v - 6 u - 3)^2 = 5(2 u + 1)^2 whose "
                + "difference is 4(2(2 v^2 - 6 u v - 3 v + 2 u^2 + 2 u) + 1) != 0. Conversely, "
                + "at t_j on T(2, 1), the odd parity of 3 m_j - p_j yields "
                + "5^(3/2) P_{2, 1}(t_j) = (C_* / 2)(1 + cos(pi delta_j)) with "
                + "delta_j = (2 - sqrt(5))(9 - 4 sqrt(5))^j -> 0, which converges to C_* and "
                + "establishes nonemptiness, boundedness above, and least-upper-bound equality "
                + "sSup(scaledTransferSet) = sSup(scaledTransferSet21 i_0 j_0) = C_*.",
                DescribeRole.Theorem),
            Node("tail-decay", "sharp_asymptotic_tail_decay",
                "Unit asymptotic tail constant, uniform (1 + epsilon) n^(-3/2) bound, and sharpness",
                TailDecayFormula(),
                "For every positive even integer s = 2(m + 1), choosing l_s = s(s + 1) and "
                + "k_s = l_s + 1 produces odd lower eigenvalue a_s = s^2 + 1, even upper "
                + "eigenvalue b_s = (s + 1)^2 + 1, and discriminant d_s = 2 s + 1; at t = pi "
                + "the phases exp(i pi a_s) = -1 and exp(i pi b_s) = 1 align constructively so "
                + "that P_{k_s, l_s}(pi) = B_{k_s, l_s}^2 and n_s^(3/2) P_{k_s, l_s}(pi) = "
                + "H(2 s + 1) > 1. Because n_s >= m can be chosen above any threshold M, both "
                + "tail sets are nonempty and bounded above by C_*, and "
                + "1 <= M_P(N) <= M_B(N) holds for all N >= 4. Conversely, specD k l >= D_N and "
                + "antitonicity of G and H give M_B(N) <= max(G(D_N), H(D_N)); for d >= 128 one "
                + "has G(d) <= 1 < H(d) <= 1 + 175 / d, while D_N -> +infinity as N -> +infinity, "
                + "forcing both M_B(N) -> 1 and M_P(N) -> 1. This yields for every epsilon > 0 "
                + "a threshold N_0 above which P_{k, l}(t) <= B_{k, l}^2 <= (1 + epsilon) n^(-3/2), "
                + "whereas for any exponent beta > 3/2 the even-s family satisfies "
                + "n_s^beta P_{k_s, l_s}(pi) = n_s^(beta - 3/2) H(2 s + 1) > n_s^(beta - 3/2) -> "
                + "+infinity, refuting every global O(n^(-beta)) upper bound.",
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("ltlstd-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Dotted(string a, string b) => Seq(Named(a), Dot, Named(b));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula fn, params Formula[] args) =>
        new Formula.Apply(fn, [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Cast(Formula v, Formula t) => Par(Seq(v, Sp, Colon, Sp, t));
    private static Formula PairOf(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula SetOf(string v, Formula dom, Formula pred) =>
        Seq(OpenBrace, F.Id(v), Sp, Colon, Sp, dom, Sp, Mid, Sp, pred, CloseBrace);
    private static Formula LambdaOf(string v, Formula dom, Formula body) =>
        Seq(LambdaLower, Sp, Cast(F.Id(v), dom), Sp, Mapsto, Sp, Par(body));
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula FracOf(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula NegOf(Formula x) => new Formula.Negate(x);
    private static Formula NotOf(Formula x) => new Formula.Not(Par(x));
    private static Formula SqrtOf(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Pow(Formula b, Formula e) =>
        b is Formula.LatexWord ? new Formula.Power(b, e) : new Formula.Power(Par(b), e);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula AndAll(params Formula[] items)
    {
        var acc = items[^1];
        for (var idx = items.Length - 2; idx >= 0; idx--)
            acc = new Formula.Logic(Par(items[idx]), FormulaLogicOperator.And, Par(acc));
        return acc;
    }
    private static Formula All(string v, Formula dom, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), dom, body);
    private static Formula Some(string v, Formula dom, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), dom, body);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula ThreeHalves() => FracOf(Num(3), Num(2));
    private static Formula NegThreeHalves() => NegOf(ThreeHalves());

    private static Formula ScaledTransferSetFormula()
    {
        Formula y = F.Id("y"), k = F.Id("k"), l = F.Id("l"), i = F.Id("i"), j = F.Id("j"),
            t = F.Id("t");
        Formula nR = Cast(Call("treeOrder", k, l), Reals());
        Formula pred = Some("k", Nats(), Some("l", Nats(),
            AndAll(LeOf(Num(2), k), LeOf(Num(1), l),
                Some("i", FinOf(k), Some("j", FinOf(l), Some("t", Reals(),
                    Eqn(y, Mul(Pow(nR, ThreeHalves()),
                        Call("leafTransferProb", k, l, i, j, t)))))))));
        return Eqn(Named("scaledTransferSet"), SetOf("y", Reals(), pred));
    }

    private static Formula ScaledTransferSet21Formula()
    {
        Formula y = F.Id("y"), i = F.Id("i"), j = F.Id("j"), t = F.Id("t");
        Formula pred = Some("t", Reals(),
            Eqn(y, Mul(Pow(Num(5), ThreeHalves()),
                Call("leafTransferProb", Num(2), Num(1), i, j, t))));
        return All("i", FinOf(Num(2)), All("j", FinOf(Num(1)),
            Eqn(Call("scaledTransferSet21", i, j), SetOf("y", Reals(), pred))));
    }

    private static Formula PellPairFormula()
    {
        Formula j = F.Id("j");
        Formula p = App(Dotted("Prod", "fst"), Call("pellPair", j));
        Formula m = App(Dotted("Prod", "snd"), Call("pellPair", j));
        return AndAll(
            Eqn(Call("pellPair", Num(0)), PairOf(Num(2), Num(1))),
            All("j", Nats(),
                Eqn(Call("pellPair", Add(j, Num(1))),
                    PairOf(Add(Mul(Num(9), p), Mul(Num(20), m)),
                        Add(Mul(Num(4), p), Mul(Num(9), m))))));
    }

    private static Formula PellPFormula() =>
        All("j", Nats(),
            Eqn(Call("pellP", F.Id("j")),
                App(Dotted("Prod", "fst"), Call("pellPair", F.Id("j")))));

    private static Formula PellMFormula() =>
        All("j", Nats(),
            Eqn(Call("pellM", F.Id("j")),
                App(Dotted("Prod", "snd"), Call("pellPair", F.Id("j")))));

    private static Formula BStarFormula() =>
        Eqn(Named("bStar"), FracOf(Add(Num(5), SqrtOf(Num(5))), Num(2)));

    private static Formula ApproxTimeFormula() =>
        All("j", Nats(),
            Eqn(Call("approxTime", F.Id("j")),
                FracOf(Mul(Mul(Num(2), Pi), Cast(Call("pellM", F.Id("j")), Reals())),
                    Named("bStar"))));

    private static Formula TailBoundingSetFormula()
    {
        Formula N = F.Id("N"), y = F.Id("y"), k = F.Id("k"), l = F.Id("l"),
            i = F.Id("i"), j = F.Id("j");
        Formula nR = Cast(Call("treeOrder", k, l), Reals());
        Formula pred = Some("k", Nats(), Some("l", Nats(),
            AndAll(LeOf(Num(2), k), LeOf(Num(1), l), LeOf(N, nR),
                Some("i", FinOf(k), Some("j", FinOf(l),
                    Eqn(y, Mul(Pow(nR, ThreeHalves()),
                        Pow(Call("leafBoundingEntry", k, l, i, j), Num(2)))))))));
        return All("N", Reals(),
            Eqn(Call("tailBoundingSet", N), SetOf("y", Reals(), pred)));
    }

    private static Formula TailTransferSetFormula()
    {
        Formula N = F.Id("N"), y = F.Id("y"), k = F.Id("k"), l = F.Id("l"),
            i = F.Id("i"), j = F.Id("j"), t = F.Id("t");
        Formula nR = Cast(Call("treeOrder", k, l), Reals());
        Formula pred = Some("k", Nats(), Some("l", Nats(),
            AndAll(LeOf(Num(2), k), LeOf(Num(1), l), LeOf(N, nR),
                Some("i", FinOf(k), Some("j", FinOf(l), Some("t", Reals(),
                    Eqn(y, Mul(Pow(nR, ThreeHalves()),
                        Call("leafTransferProb", k, l, i, j, t)))))))));
        return All("N", Reals(),
            Eqn(Call("tailTransferSet", N), SetOf("y", Reals(), pred)));
    }

    private static Formula TailBoundingSupFormula() =>
        All("N", Reals(),
            Eqn(Call("tailBoundingSup", F.Id("N")),
                Call("sSup", Call("tailBoundingSet", F.Id("N")))));

    private static Formula TailTransferSupFormula() =>
        All("N", Reals(),
            Eqn(Call("tailTransferSup", F.Id("N")),
                Call("sSup", Call("tailTransferSet", F.Id("N")))));

    private static Formula TailThresholdDFormula()
    {
        Formula N = F.Id("N");
        return All("N", Reals(),
            Eqn(Call("tailThresholdD", N),
                Call("max", SqrtOf(Num(5)),
                    SqrtOf(Sub(Mul(Num(4), SqrtOf(Sub(N, Num(1)))), Num(3))))));
    }

    private static Formula SupremumAndPellFormula()
    {
        Formula m = F.Id("m"), i0 = F.Id("i0"), j0 = F.Id("j0"), k = F.Id("k"), l = F.Id("l"),
            i = F.Id("i"), j = F.Id("j"), t = F.Id("t");
        Formula st = Named("scaledTransferSet"), cOpt = Named("optimalTransferConst");
        Formula s21 = Call("scaledTransferSet21", i0, j0);
        Formula nR = Cast(Call("treeOrder", k, l), Reals());
        Formula atTop = Dotted("Filter", "atTop"), tendsto = Dotted("Filter", "Tendsto");
        Formula clause21 = All("i0", FinOf(Num(2)), All("j0", FinOf(Num(1)),
            AndAll(App(Dotted("Set", "Nonempty"), s21), Call("BddAbove", s21),
                Call("IsLUB", s21, cOpt), Eqn(Call("sSup", st), Call("sSup", s21)),
                Eqn(Call("sSup", s21), cOpt))));
        Formula strict = All("k", Nats(), All("l", Nats(),
            Imp(LeOf(Num(2), k), Imp(LeOf(Num(1), l),
                All("i", FinOf(k), All("j", FinOf(l), All("t", Reals(),
                    LtOf(Mul(Pow(nR, ThreeHalves()),
                        Call("leafTransferProb", k, l, i, j, t)), cOpt))))))));
        Formula pellLim = All("i0", FinOf(Num(2)), All("j0", FinOf(Num(1)),
            App(tendsto,
                LambdaOf("j", Nats(), Mul(Pow(Num(5), ThreeHalves()),
                    Call("leafTransferProb", Num(2), Num(1), i0, j0, Call("approxTime", j)))),
                atTop, Call("nhds", cOpt))));
        return All("m", Nats(), AndAll(
            LtOf(Call("approxTime", m), Call("approxTime", Add(m, Num(1)))),
            App(Dotted("Set", "Nonempty"), st), Call("BddAbove", st),
            Call("IsLUB", st, cOpt), Eqn(Call("sSup", st), cOpt),
            clause21, strict, App(tendsto, Named("approxTime"), atTop, atTop), pellLim));
    }

    private static Formula TailDecayFormula()
    {
        Formula N = F.Id("N"), M = F.Id("M"), eps = F.Id("eps"), N0 = F.Id("N0"),
            k = F.Id("k"), l = F.Id("l"), i = F.Id("i"), j = F.Id("j"), t = F.Id("t"),
            beta = F.Id("beta"), C = F.Id("C");
        Formula tbM = Call("tailBoundingSet", M), ttM = Call("tailTransferSet", M);
        Formula dN = Call("tailThresholdD", N);
        Formula nR = Cast(Call("treeOrder", k, l), Reals());
        Formula bndSq = Pow(Call("leafBoundingEntry", k, l, i, j), Num(2));
        Formula atTop = Dotted("Filter", "atTop"), tendsto = Dotted("Filter", "Tendsto");
        Formula lubAll = All("M", Reals(), AndAll(
            App(Dotted("Set", "Nonempty"), tbM), Call("BddAbove", tbM),
            Call("IsLUB", tbM, Call("tailBoundingSup", M)),
            App(Dotted("Set", "Nonempty"), ttM), Call("BddAbove", ttM),
            Call("IsLUB", ttM, Call("tailTransferSup", M))));
        Formula unif = All("eps", Reals(), Imp(LtOf(Num(0), eps),
            Some("N0", Reals(), All("k", Nats(), All("l", Nats(),
                Imp(LeOf(Num(2), k), Imp(LeOf(Num(1), l), Imp(LeOf(N0, nR),
                    All("i", FinOf(k), All("j", FinOf(l), All("t", Reals(),
                        AndAll(LeOf(Call("leafTransferProb", k, l, i, j, t), bndSq),
                            LeOf(bndSq, Mul(Add(Num(1), eps),
                                Pow(nR, NegThreeHalves())))))))))))))));
        Formula sharp = All("beta", Reals(), Imp(LtOf(ThreeHalves(), beta),
            NotOf(Some("C", Reals(), All("k", Nats(), All("l", Nats(),
                Imp(LeOf(Num(2), k), Imp(LeOf(Num(1), l),
                    All("i", FinOf(k), All("j", FinOf(l), All("t", Reals(),
                        LeOf(Call("leafTransferProb", k, l, i, j, t),
                            Mul(C, Pow(nR, NegOf(beta)))))))))))))));
        return All("N", Reals(), Imp(LeOf(Num(4), N), AndAll(
            LeOf(Num(1), Call("tailTransferSup", N)),
            LeOf(Call("tailTransferSup", N), Call("tailBoundingSup", N)),
            LeOf(Call("tailBoundingSup", N),
                Call("max", Call("envelopeG", dN), Call("envelopeH", dN))),
            lubAll,
            App(tendsto, Named("tailBoundingSup"), atTop, Call("nhds", Cast(Num(1), Reals()))),
            App(tendsto, Named("tailTransferSup"), atTop, Call("nhds", Cast(Num(1), Reals()))),
            unif, sharp)));
    }
}
