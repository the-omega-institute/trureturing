using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class SynchronousDoilyClassicalValueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/lau2026doily");
    private const string Question = "However, it is possible that for p < 1/7, the value of the p-synchronous doily game is less than 31/35. In particular, if Lemma 4.3 can be improved to state that an optimal asymmetric strategy for the doily game wins on at most 12 of 15 synchronous questions, the 1/10-synchronous doily game would have a classical value of 22/25 < 31/35. The author estimates that this could be checked exhaustively using about three years of continuous work on an RTX 4090 graphics card.";
    private const string Game = "For p ∈ [0, 1], the p-synchronous (p-sync) doily game is defined as the nonlocal game ([15], [15], {0, 1}³, {0, 1}³, (1 − p)π₁ + pπ₂, R), for π₁ being the uniform distribution over {(j, k) ∈ [15] × [15] : Eⱼ and Eₖ have exactly one variable in common}, (13) π₂ being the uniform distribution over {(j, j) ∈ [15] × [15] : j ∈ [15]}, (14) and R : [15] × [15] × {0, 1}³ × {0, 1}³ → {0, 1} being the function such that R(j, k, a, b) = 1 if and only if a satisfies the parity of Eⱼ, b satisfies the parity of Eₖ and the bits corresponding to any variables shared between Eⱼ and Eₖ in a are the same as those in b.";
    private const string Strategies = "For the nonlocal game G = (X, Y, A, B, π, V), a classical deterministic strategy S is any pair of functions S = (A, B) with A : X → A and B : Y → B. A and B will be referred to as Alice’s local strategy and Bob’s local strategy, respectively. Then, the probability that Alice and Bob win G using S is given by the expression Σ_{x∈X, y∈Y} π(x, y)V(x, y, A(x), B(y)). (1)";
    private const string Value = "We may then define the classical value and entangled value of a game G as the supremal probability of winning G over all classical strategies and over all entangled strategies, respectively.";
    private const string Equations = "E₀ V₀ + V₃ + V₆ = 0; E₁ V₁ + V₃ + V₇ = 0; E₂ V₂ + V₃ + V₈ = 0; E₃ V₀ + V₄ + V₉ = 0; E₄ V₁ + V₄ + V₁₀ = 0; E₅ V₂ + V₄ + V₁₁ = 0; E₆ V₀ + V₅ + V₁₂ = 0; E₇ V₁ + V₅ + V₁₃ = 0; E₈ V₂ + V₅ + V₁₄ = 0; E₉ V₆ + V₁₁ + V₁₃ = 0; E₁₀ V₁₀ + V₁₂ + V₈ = 0; E₁₁ V₁₄ + V₇ + V₉ = 0; E₁₂ V₆ + V₁₀ + V₁₄ = 1; E₁₃ V₁₁ + V₁₂ + V₇ = 1; E₁₄ V₁₃ + V₈ + V₉ = 1.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The classical value of Tony Lau's one-tenth synchronous doily game is exactly 22/25. The proof combines an explicit attaining strategy with the odd parities of ten grids and a bound on the effect of synchronous disagreements.",
        H("The one-tenth synchronous doily game"),
        Blocks(
            Node("vars", "The fifteen equations", VarsFormula(),
                "Table 3, p. 6: “" + Equations + "” The Boolean equation additions are modulo two. The displayed list defines vars : Fin 15 → Fin 3 → Fin 15: its entry at equation e and position i is the variable index in precisely the printed order, including E₁₀ and E₁₁.", DescribeRole.Definition),
            Node("odd", "Right-hand-side parity", OddFormula(),
                "Table 3, p. 6: “" + Equations + "” The function odd is true exactly at equations 12, 13 and 14; val takes the natural-number value of a finite index. The operator decide converts a decidable proposition into a Boolean.", DescribeRole.Definition),
            Node("sat", "Parity-valid answers", SatFormula(),
                "Definition 4.1, p. 15: “" + Game + "” An answer is any function Fin 3 → Bool. The operator toNat sends false to 0 and true to 1, and mod is natural-number remainder. Thus sat states exactly the Boolean equation's required parity.", DescribeRole.Definition),
            Node("meet", "Intersecting questions", MeetFormula(),
                "Definition 4.1, p. 15: “" + Game + "” The finite variable set of an equation is the image of Finset.univ under its vars map. Distinct equations meet when the intersection of those sets has cardinality one. Identical equations share three variables and are excluded. Ordered pairs are counted separately.", DescribeRole.Definition),
            Node("R", "The referee predicate", RefereeFormula(),
                "Definition 4.1, p. 15: “" + Game + "” The proposition R represents payoff 1. On a diagonal question the universally quantified shared-position condition requires equality of all three answer bits, as well as both parity conditions.", DescribeRole.Definition),
            Node("winProb", "Winning probability", ProbabilityFormula(),
                "Definition 4.1, p. 15: “" + Game + "” Definition 2.2, p. 2: “" + Strategies + "” The first finite set in the fraction is the filter of all ordered intersecting pairs by R; its denominator is the cardinality of all ordered intersecting pairs, computed from Table 3 as 90. The diagonal denominator is 15. Both cardinalities are cast to real numbers, as shown by the displayed typed coercion. The definition extends to real p; the game uses p ∈ [0, 1], and the theorem uses p = 1/10. Answer functions remain unrestricted, including parity-invalid answers.", DescribeRole.Definition),
            Node("classicalValue", "The deterministic classical value", ValueFormula(),
                "Section 2, p. 3: “" + Value + "” The displayed Finset.sup' is taken over the nonempty finite universe of all pairs of functions Fin 15 → Fin 3 → Bool, with S mapped to winProb(p, S.1, S.2). Fintype.ofFinite supplies the complete finite enumeration; it imposes no parity restriction. This finite maximum is the source supremum over every deterministic strategy.", DescribeRole.Definition),
            Node("claim", "Lau's candidate value", ClaimFormula(),
                "Section 5, p. 20: “" + Question + "” Table 3, p. 6: “" + Equations + "” Definition 4.1, p. 15: “" + Game + "” Section 2, pp. 2–3: “" + Strategies + "” “" + Value + "” The equality selects the explicitly named candidate p = 1/10. All fifteen equations, all eight local answers per equation, both independent deterministic strategies, and the ordered-question convention are retained.", DescribeRole.Definition),
            Node("result", "The exact value", Disp(Equal(Call("classicalValue", Fraction(1, 10)), Fraction(22, 25))),
                "Answer 000 at equations 0 through 11 and 100 at equations 12 through 14, for both players. This wins 78 of the 90 intersecting ordered pairs and every diagonal question, attaining 22/25. For the upper bound, repair invalid parities without losing a won question. Each of the ten odd grids forces a loss in each orientation, and every ordered intersecting pair lies in two grids, so the total intersecting loss L is at least 10. If the players disagree on at most two equations, minority-event counting and parity-valid local flips give L ≥ 12. Writing r for their number of differing equation answers yields 3L + 2r ≥ 36, while 300(1 − winProb) = 3L + 2r. Consequently every strategy has winProb ≤ 22/25, and the explicit strategy attains the finite maximum. The conclusion is at the single parameter 1/10; the full parameter dependence and higher-dimensional games require further results.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("doily-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula),
            role == DescribeRole.Theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) => new Formula.Logic(left, op, right);
    private static Formula And(Formula left, Formula right) => Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Fin(int n) => Call("Fin", Num(n));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Answer => Arrow(Fin(3), F.Id("Bool"));
    private static Formula Strategy => Arrow(Fin(15), Parenthesized(Answer));
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula PairType => Product(Fin(15), Fin(15));
    private static Formula LambdaAt(string name, Formula type, Formula body) =>
        Seq(Lambda, Sp, F.Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Item(Formula q, int i) => Seq(q, Dot, Num(i));
    private static Formula Fraction(int n, int d) => new Formula.Fraction(Num(n), Num(d));
    private static Formula NatToReal(Formula n) => Parenthesized(Seq(n, Sp, Colon, Sp, Real));
    private static Formula Filter(string name, Formula type, Formula condition, Formula set) =>
        Call("filter", Parenthesized(LambdaAt(name, type, condition)), set);
    private static Formula Universe(Formula type) => Call("univ", type);
    private static Formula Questions() => Filter("q", PairType,
        Call("meet", Item(F.Id("q"), 1), Item(F.Id("q"), 2)), Universe(PairType));

    private static Formula VarsFormula()
    {
        int[][] table = [
            [0,3,6], [1,3,7], [2,3,8], [0,4,9], [1,4,10], [2,4,11],
            [0,5,12], [1,5,13], [2,5,14], [6,11,13], [10,12,8], [14,7,9],
            [6,10,14], [11,12,7], [13,8,9]];
        Formula[] triples = table.Select(row => (Formula)Seq(OpenBracket, Num(row[0]), Comma, Sp,
            Num(row[1]), Comma, Sp, Num(row[2]), CloseBracket)).ToArray();
        Formula[] list = triples.SelectMany((t, i) => i == 0 ? new[] { t } : new[] { Comma, Sp, t }).ToArray();
        return Disp(Equal(Seq(F.Id("vars"), Sp, Colon, Sp, Arrow(Fin(15), Parenthesized(Arrow(Fin(3), Fin(15))))),
            Seq(OpenBracket, Seq(list), CloseBracket)));
    }

    private static Formula OddFormula() => Disp(All("e", Fin(15),
        Equal(Call("odd", F.Id("e")), Call("decide", new Formula.Relation(Num(12),
            FormulaRelationOperator.LessThanOrEqual, Call("val", F.Id("e")))))));

    private static Formula SatFormula()
    {
        Formula e = F.Id("e"), a = F.Id("a"), i = F.Id("i");
        Formula sum = Seq(new Formula.Subscript(F.Sum, Seq(i, Sp, InMacro, Sp, Fin(3))), Sp,
            Call("toNat", At(a, i)));
        return Disp(All("e", Fin(15), All("a", Answer,
            Iff(Call("sat", e, a), Equal(Call("mod", sum, Num(2)), Call("toNat", Call("odd", e)))))));
    }

    private static Formula MeetFormula()
    {
        Formula e = F.Id("e"), f = F.Id("f");
        Formula common = Call("inter", Call("image", Call("vars", e), Universe(Fin(3))),
            Call("image", Call("vars", f), Universe(Fin(3))));
        return Disp(All("e", Fin(15), All("f", Fin(15),
            Iff(Call("meet", e, f), And(NotEqual(e, f), Equal(Call("card", common), Num(1)))))));
    }

    private static Formula RefereeFormula()
    {
        Formula e = F.Id("e"), f = F.Id("f"), a = F.Id("a"), b = F.Id("b"), i = F.Id("i"), j = F.Id("j");
        Formula consistency = All("i", Fin(3), All("j", Fin(3),
            Logic(Equal(Call("vars", e, i), Call("vars", f, j)), FormulaLogicOperator.Implies, Equal(At(a, i), At(b, j)))));
        return Disp(All("e", Fin(15), All("f", Fin(15), All("a", Answer, All("b", Answer,
            Iff(Call("R", e, f, a, b), And(Call("sat", e, a), And(Call("sat", f, b), consistency))))))));
    }

    private static Formula ProbabilityFormula()
    {
        Formula p = F.Id("p"), a = F.Id("A"), b = F.Id("B"), q = F.Id("z"), e = F.Id("e");
        Formula winningPairs = Filter("z", PairType,
            Call("R", Item(q, 1), Item(q, 2), At(a, Item(q, 1)), At(b, Item(q, 2))), Questions());
        Formula diagonal = Filter("e", Fin(15), Call("R", e, e, At(a, e), At(b, e)), Universe(Fin(15)));
        Formula value = Add(Multiply(Parenthesized(Subtract(Num(1), p)),
                new Formula.Fraction(NatToReal(Call("card", winningPairs)), NatToReal(Call("card", Questions())))),
            Multiply(p, new Formula.Fraction(NatToReal(Call("card", diagonal)), Num(15))));
        return Disp(All("p", Real, All("A", Strategy, All("B", Strategy, Equal(Call("winProb", p, a, b), value)))));
    }

    private static Formula ValueFormula()
    {
        Formula p = F.Id("p"), s = F.Id("S");
        Formula strategies = Product(Parenthesized(Strategy), Parenthesized(Strategy));
        return Disp(All("p", Real, Equal(Call("classicalValue", p), At(Seq(F.Id("Finset"), Dot, F.Id("sup"), Apos), Universe(strategies),
            Parenthesized(LambdaAt("S", strategies, Call("winProb", p, Item(s, 1), Item(s, 2))))))));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"),
        Equal(Call("classicalValue", Fraction(1, 10)), Fraction(22, 25))));
}
