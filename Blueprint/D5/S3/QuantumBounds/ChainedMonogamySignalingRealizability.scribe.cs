using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class ChainedMonogamySignalingRealizabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/klobus2016communication");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kłobus, Oszmaniec, Augusiak and Grudka (arXiv:1408.1223, Section 5) conjecture that every vector of the correlators x_A^i, y_A^i, x_B^i, y_B^i satisfying their inequalities (ElPrat) is realized by a signaling box whose chained Bell expression plus twice the correlator of B_0 and E equals 2M + Delta. This holds for every number of settings M at least 2 and every Delta in [0, 2]: an explicit box realizes the coordinates, has all one- and three-party expectation values zero and a common value of the correlator of B_0 and E, and attains R_M = 2M + Delta exactly.",
        H("The realizability conjecture for chained monogamy relations"),
        Blocks(
            Node("sgn", "Outcome signs", SgnFormula(),
                "Outcomes are elements of Bool, and sgn maps true to 1 and false to -1.",
                "sgn", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("box", "Boxes", BoxFormula(),
                "A box assigns to each pair of settings (A_i, B_j) a function p(i, j) of the three outcomes a, b, e; Eve has a single setting. IsBox(M, p) says that for all i, j < M this function is a probability distribution. No relation between different setting pairs is imposed, so signaling is allowed.",
                "IsBox", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("odd", "The class of boxes with vanishing odd moments", OddFormula(),
                "The paper restricts attention to the convex set of boxes whose one-party expectation values and three-party expectation values all vanish, so that only the bipartite correlators are nonzero.",
                "OddMomentsVanish", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ab", "The correlator of A and B", CorrFormula(F.Id("corrAB"), Mul(Sg(F.Id("a")), Sg(F.Id("b")))),
                "The correlator of A_i and B_j at the setting pair (i, j).",
                "corrAB", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ae", "The correlator of A and E", CorrFormula(F.Id("corrAE"), Mul(Sg(F.Id("a")), Sg(F.Id("e")))),
                "The correlator of A_i and E conditioned on the setting B_j of the third party.",
                "corrAE", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("be", "The correlator of B and E", CorrFormula(F.Id("corrBE"), Mul(Sg(F.Id("b")), Sg(F.Id("e")))),
                "The correlator of B_j and E conditioned on the setting A_i of the third party.",
                "corrBE", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("chain", "The chained Bell expression plus Eve's correlator", ChainFormula(),
                "The chained Bell expression is the sum over k < M of the correlators of A_k B_k and of A_(k+1) B_k, with the convention A_M = -A_0, so its last term is minus the correlator of A_0 B_(M-1). R_M adds twice the correlator of B_0 and E, read at the setting A_0; for the boxes of the conjecture it does not depend on the setting of A.",
                "chainR", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("elprat", "The inequalities (ElPrat)", ElPratFormula(),
                "One inequality for each choice of the signs a_i, b_i and c in {0, 1}, with a_i for i from 1 to M - 1 and b_i for i from 1 to M - 2.",
                "ElPrat", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bounds", "The range of the coordinates", BoundsFormula(),
                "The coordinates are correlators, so each lies in [-1, 1]; the bound is required on the indices where the coordinate is defined.",
                "CoordinateBounds", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("realizes", "Realizing the coordinates", RealizesFormula(),
                "The coordinates are x_A^i = <B_i E>_(A_i), y_A^i = <B_i E>_(A_(i+1)), x_B^i = <A_i E>_(B_(i-1)) and y_B^i = <A_i E>_(B_i) for i from 1 to M - 1, together with x_B^0 = <A_0 E>_(B_0) and y_B^0 = <A_0 E>_(B_(M-1)). The setting A_M = -A_0 in y_A^(M-1) is the setting A_0 with relabelled outcomes, which does not change a correlator of B and E, so y_A^(M-1) is read at the setting pair (A_0, B_(M-1)).",
                "Realizes", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "The paper conjectures that all values of the coordinates satisfying (ElPrat) can be realized with some signaling distribution for which R_M = 2M + Delta, within the class of boxes with vanishing one- and three-party expectation values and a common correlator of B_0 and E. The displayed statement reads it for every M at least 2 and every Delta in [0, 2]; the conjecture is the case M at least 3, and for M = 2 the inequalities (ElPrat) are the paper's printed list with the signs of x_A^1 and y_A^1 corrected in two of its four lines.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture holds", Disp(F.Id("claim")),
                "For |v|, |w| at most 1 and -1 + |v + w| <= u <= 1 - |v - w|, the function (1 + ab u + ae v + be w)/8 of the signs a, b, e is a probability distribution whose correlators of A and B, A and E, and B and E are u, v and w, and whose one- and three-party expectation values vanish. Let T be the sum of |x_A^i - y_B^i| over 1 <= i <= M - 1, of |x_B^(i+1) - y_A^i| over 1 <= i <= M - 2, and |y_A^(M-1) + y_B^0|. Choosing every sign in (ElPrat) against its term gives x_B^0 + x_B^1 - T >= Delta, so t = (2 + Delta + T)/(2 + x_B^0 + x_B^1) lies in (0, 1]. Take (u, v, w) = (t x_B^0, x_B^0, t) at (A_0, B_0) and (t x_B^1, x_B^1, t) at (A_1, B_0); (0, 0, t) at the other pairs (A_i, B_0); at (A_i, B_i) and (A_(i+1), B_i) with i >= 1 the prescribed v and w with u = 1 - |v - w|; at (A_0, B_(M-1)) the prescribed v = y_B^0 and w = y_A^(M-1) with u = -1 + |v + w|; and (0, 0, 0) elsewhere. The box realizes the coordinates, the correlator of B_0 and E equals t at every setting of A, and R_M = (2M - 2 - T) + t (x_B^0 + x_B^1 + 2) = 2M + Delta.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("klobus-2016-chained-monogamy-realizability"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("cmr-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LtTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.And, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula NumberSet(Formula name) => Seq(Mathbb, Grp(name));
    private static Formula Nat() => NumberSet(F.Id("N"));
    private static Formula Real() => NumberSet(F.Id("R"));
    private static Formula Abs(Formula x) => new Formula.Absolute(x);
    private static Formula Sg(Formula v) => Call(F.Id("sgn"), v);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(Sum, Underscore, Grp(index), Sp, body);
    private static Formula BoolSum(Formula body)
    {
        Formula a = F.Id("a"), b = F.Id("b"), e = F.Id("e");
        return SumOver(a, SumOver(b, SumOver(e, body)));
    }
    private static Formula Entry(Formula p, Formula i, Formula j) =>
        Call(p, i, j, F.Id("a"), F.Id("b"), F.Id("e"));
    private static Formula BoxType() =>
        Seq(Nat(), Sp, To, Sp, Nat(), Sp, To, Sp, F.Id("Bool"), Sp, To, Sp, F.Id("Bool"), Sp,
            To, Sp, F.Id("Bool"), Sp, To, Sp, Real());
    private static Formula Seqs() => Seq(Nat(), Sp, To, Sp, Real());
    private static Formula Interval(Formula lo, Formula hi) =>
        Call(F.Id("Icc"), lo, hi);
    private static Formula Below(Formula i, Formula m, Formula body) =>
        Imp(LtTo(i, m), body);

    private static Formula SgnFormula()
    {
        return Disp(And(EqTo(Call(F.Id("sgn"), F.Id("true")), D(1)),
            EqTo(Call(F.Id("sgn"), F.Id("false")), Seq(Minus, D(1)))));
    }

    private static Formula BoxFormula()
    {
        Formula m = F.Id("M"), p = F.Id("p"), i = F.Id("i"), j = F.Id("j"), a = F.Id("a"),
            b = F.Id("b"), e = F.Id("e");
        Formula nonneg = All(a, F.Id("Bool"), All(b, F.Id("Bool"), All(e, F.Id("Bool"),
            LeTo(D(0), Entry(p, i, j)))));
        Formula normalized = EqTo(BoolSum(Entry(p, i, j)), D(1));
        return Disp(All(m, Nat(), All(p, BoxType(), Logic(Call(F.Id("IsBox"), m, p),
            FormulaLogicOperator.Iff, All(i, Nat(), All(j, Nat(), Below(i, m, Below(j, m,
                And(nonneg, normalized)))))))));
    }

    private static Formula Moment(Formula weight, Formula p, Formula i, Formula j) =>
        EqTo(BoolSum(Mul(weight, Entry(p, i, j))), D(0));

    private static Formula OddFormula()
    {
        Formula m = F.Id("M"), p = F.Id("p"), i = F.Id("i"), j = F.Id("j");
        Formula sa = Sg(F.Id("a")), sb = Sg(F.Id("b")), se = Sg(F.Id("e"));
        Formula moments = And(Moment(sa, p, i, j), And(Moment(sb, p, i, j),
            And(Moment(se, p, i, j), Moment(Mul(Mul(sa, sb), se), p, i, j))));
        return Disp(All(m, Nat(), All(p, BoxType(), Logic(Call(F.Id("OddMomentsVanish"), m, p),
            FormulaLogicOperator.Iff, All(i, Nat(), All(j, Nat(), Below(i, m, Below(j, m,
                moments))))))));
    }

    private static Formula CorrFormula(Formula name, Formula weight)
    {
        Formula p = F.Id("p"), i = F.Id("i"), j = F.Id("j");
        return Disp(All(p, BoxType(), All(i, Nat(), All(j, Nat(),
            EqTo(Call(name, p, i, j), BoolSum(Mul(weight, Entry(p, i, j))))))));
    }

    private static Formula ChainFormula()
    {
        Formula m = F.Id("M"), p = F.Id("p"), k = F.Id("k");
        Formula kp = Add(k, D(1)), mm = Sub(m, D(1));
        Formula first = SumOver(Seq(k, Lt, m), Call(F.Id("corrAB"), p, k, k));
        Formula second = SumOver(Seq(k, Lt, mm), Call(F.Id("corrAB"), p, kp, k));
        Formula value = Add(Sub(Add(first, second), Call(F.Id("corrAB"), p, D(0), mm)),
            Mul(D(2), Call(F.Id("corrBE"), p, D(0), D(0))));
        return Disp(All(m, Nat(), All(p, BoxType(), EqTo(Call(F.Id("chainR"), m, p), value))));
    }

    private static Formula ElPratFormula()
    {
        Formula m = F.Id("M"), delta = Delta, xa = F.Id("xA"), ya = F.Id("yA"), xb = F.Id("xB"),
            yb = F.Id("yB"), a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), i = F.Id("i");
        Formula sign = Parenthesized(Seq(Minus, D(1)));
        Formula t1 = SumOver(Member(i, Interval(D(1), Sub(m, D(1)))),
            Mul(Pow(sign, Call(a, i)), Parenthesized(Sub(Call(xa, i), Call(yb, i)))));
        Formula t2 = SumOver(Member(i, Interval(D(1), Sub(m, D(2)))),
            Mul(Pow(sign, Call(b, i)), Parenthesized(Sub(Call(xb, Add(i, D(1))), Call(ya, i)))));
        Formula t3 = Mul(Pow(sign, c),
            Parenthesized(Add(Call(ya, Sub(m, D(1))), Call(yb, D(0)))));
        Formula lhs = Add(Add(Add(Add(t1, t2), t3), Call(xb, D(1))), Call(xb, D(0)));
        Formula signs = Seq(Nat(), Sp, To, Sp, Call(F.Id("Fin"), D(2)));
        Formula body = All(a, signs, All(b, signs, All(c, Call(F.Id("Fin"), D(2)),
            LeTo(delta, lhs))));
        return Disp(All(m, Nat(), All(delta, Real(), All(xa, Seqs(), All(ya, Seqs(),
            All(xb, Seqs(), All(yb, Seqs(), Logic(Call(F.Id("ElPrat"), m, delta, xa, ya, xb, yb),
                FormulaLogicOperator.Iff, body))))))));
    }

    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);

    private static Formula BoundsFormula()
    {
        Formula m = F.Id("M"), xa = F.Id("xA"), ya = F.Id("yA"), xb = F.Id("xB"),
            yb = F.Id("yB"), i = F.Id("i");
        Formula inRange = Imp(Member(i, Interval(D(1), Sub(m, D(1)))),
            And(LeTo(Abs(Call(xa, i)), D(1)), And(LeTo(Abs(Call(ya, i)), D(1)),
                And(LeTo(Abs(Call(xb, i)), D(1)), LeTo(Abs(Call(yb, i)), D(1))))));
        Formula zero = And(LeTo(Abs(Call(xb, D(0))), D(1)), LeTo(Abs(Call(yb, D(0))), D(1)));
        return Disp(All(m, Nat(), All(xa, Seqs(), All(ya, Seqs(), All(xb, Seqs(), All(yb, Seqs(),
            Logic(Call(F.Id("CoordinateBounds"), m, xa, ya, xb, yb), FormulaLogicOperator.Iff,
                And(All(i, Nat(), inRange), zero))))))));
    }

    private static Formula RealizesFormula()
    {
        Formula m = F.Id("M"), p = F.Id("p"), xa = F.Id("xA"), ya = F.Id("yA"), xb = F.Id("xB"),
            yb = F.Id("yB"), i = F.Id("i");
        Formula mm = Sub(m, D(1));
        Formula main = Imp(Member(i, Interval(D(1), mm)),
            And(EqTo(Call(F.Id("corrBE"), p, i, i), Call(xa, i)),
                And(EqTo(Call(F.Id("corrAE"), p, i, Sub(i, D(1))), Call(xb, i)),
                    EqTo(Call(F.Id("corrAE"), p, i, i), Call(yb, i)))));
        Formula middle = Imp(Member(i, Interval(D(1), Sub(m, D(2)))),
            EqTo(Call(F.Id("corrBE"), p, Add(i, D(1)), i), Call(ya, i)));
        Formula ends = And(EqTo(Call(F.Id("corrBE"), p, D(0), mm), Call(ya, mm)),
            And(EqTo(Call(F.Id("corrAE"), p, D(0), D(0)), Call(xb, D(0))),
                EqTo(Call(F.Id("corrAE"), p, D(0), mm), Call(yb, D(0)))));
        Formula body = And(All(i, Nat(), main), And(All(i, Nat(), middle), ends));
        return Disp(All(m, Nat(), All(p, BoxType(), All(xa, Seqs(), All(ya, Seqs(),
            All(xb, Seqs(), All(yb, Seqs(), Logic(Call(F.Id("Realizes"), m, p, xa, ya, xb, yb),
                FormulaLogicOperator.Iff, body))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("M"), delta = Delta, xa = F.Id("xA"), ya = F.Id("yA"), xb = F.Id("xB"),
            yb = F.Id("yB"), p = F.Id("p"), i = F.Id("i");
        Formula common = All(i, Nat(), Below(i, m,
            EqTo(Call(F.Id("corrBE"), p, i, D(0)), Call(F.Id("corrBE"), p, D(0), D(0)))));
        Formula conclusion = Some(p, BoxType(), And(Call(F.Id("IsBox"), m, p),
            And(Call(F.Id("OddMomentsVanish"), m, p), And(common,
                And(EqTo(Call(F.Id("chainR"), m, p), Add(Mul(D(2), m), delta)),
                    Call(F.Id("Realizes"), m, p, xa, ya, xb, yb))))));
        Formula body = Imp(Call(F.Id("CoordinateBounds"), m, xa, ya, xb, yb),
            Imp(Call(F.Id("ElPrat"), m, delta, xa, ya, xb, yb), conclusion));
        Formula quantified = All(m, Nat(), Imp(LeTo(D(2), m), All(delta, Real(),
            Imp(LeTo(D(0), delta), Imp(LeTo(delta, D(2)), All(xa, Seqs(), All(ya, Seqs(),
                All(xb, Seqs(), All(yb, Seqs(), body)))))))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, quantified));
    }
}
