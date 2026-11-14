using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class EffectAdditivityStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary defect on all actual effects controls real scaling and signed finite families.",
        H("Effect additivity stability"),
        Blocks(
            Paragraph(Text("Throughout the formulas, Id(d) is the actual identity matrix, real(n) is the real embedding of a natural number, card(J) is the finite type cardinality, and dots denote multiplication or scalar action according to the displayed types. The map ofMatrixInverse is the inverse of the canonical CStarMatrix.ofMatrix equivalence. Type and the anonymous instance brackets retain the universe-polymorphic finite index assumptions.")),
            Paragraph(Text("Write Mat d for Matrix (Fin d) (Fin d) Complex, with d any natural number. An effect E means that E is positive semidefinite and identity minus E is positive semidefinite. Every displayed p is an arbitrary total real function on these actual matrices; only its effect values enter the estimates.")),
            Paragraph(Text("The interval argument applies a supremum contraction to g(t)=p(t*E)-t*p(E). Positivity and normalization bound this function; binary defect gives the contraction. A nonempty weighted list then accumulates its binary and homogeneity errors. Splitting signed coefficients and rescaling by K squared gives the general finite-family estimate. Zero terms are retained throughout.")),
            Describe.Lean(
                DescribeId.Create("mat"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.Mat"),
                H("Mat"),
                StatementSource.FromAuthor(Statement("Mat")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The matrix space in dimension d is the actual complex square matrix algebra indexed by Fin d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.IsEffect"),
                H("IsEffect"),
                StatementSource.FromAuthor(Statement("IsEffect")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("An effect is an actual positive semidefinite complex matrix whose complement to the identity is also positive semidefinite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("effect-iff-order"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.effect_iff_order"),
                H("effect iff order"),
                StatementSource.FromAuthor(Statement("effect_iff_order")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The two positive semidefinite conditions defining an effect are equivalent to the native matrix-order interval from zero to the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cstar-effect-bridge"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.cstar_effect_bridge"),
                H("cstar effect bridge"),
                StatementSource.FromAuthor(Statement("cstar_effect_bridge")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The native C-star matrix equivalence identifies the same actual effects with its order interval from zero to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-interval-stability"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.bounded_interval_stability"),
                H("bounded interval stability"),
                StatementSource.FromAuthor(Statement("bounded_interval_stability")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every bounded real function g on the unit interval with g(1)=0 and binary additive defect at most epsilon has absolute value at most twice epsilon throughout that interval. The bound M is arbitrary; no continuity or measurability is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probability-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.probability_bounds"),
                H("probability bounds"),
                StatementSource.FromAuthor(Statement("probability_bounds")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Nonnegativity on all effects, normalization at the identity and the stated binary defect imply that p(0) lies between zero and epsilon, and every effect value lies between zero and 1+epsilon. No separate sign premise on epsilon is added."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("effect-homogeneity"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.effect_homogeneity"),
                H("effect homogeneity"),
                StatementSource.FromAuthor(Statement("effect_homogeneity")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every actual effect and every real scale in the closed unit interval, the homogeneity error is at most 2*epsilon, under precisely the displayed global positivity, normalization and binary-defect hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-sum-error"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.finite_sum_error"),
                H("finite sum error"),
                StatementSource.FromAuthor(Statement("finite_sum_error")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A list of n+1 positive semidefinite matrices whose total is an effect accumulates at most n*epsilon additive error. Only binary-defect control is assumed; no p(0)=0 or additional epsilon-sign premise is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-finite-sum-error"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.weighted_finite_sum_error"),
                H("weighted finite sum error"),
                StatementSource.FromAuthor(Statement("weighted_finite_sum_error")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For n+1 effects with real weights in the closed unit interval and an effect-valued weighted total, the weighted error is at most (3*(n+1)-1)*epsilon, with n interpreted in the reals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-fintype-error"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.weighted_fintype_error"),
                H("weighted fintype error"),
                StatementSource.FromAuthor(Statement("weighted_fintype_error")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The same weighted estimate holds for every nonempty finite index type, including zero coefficients, with constant 3*card(I)-1 and all displayed effect, weight and total conditions preserved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-positive-family-error"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.finite_positive_family_error"),
                H("finite positive family error"),
                StatementSource.FromAuthor(Statement("finite_positive_family_error")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural matrix dimension and nonempty finite index type I, any effect family with sum at most K times the identity and signed real coefficients of absolute value at most K represents each specified effect E with probability error at most K^2*(6*card(I)+1)*epsilon. The premises require K>=1 and epsilon>=0 and the actual equality for E; the dimension need not be positive in this general helper."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, P(Seq(variable, Colon, Sp, type)), Comma, Sp, P(body));
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(P(clauses[index]));
        }
        return Seq([.. items]);
    }
    private static Formula Imp(Formula premise, Formula result) => Seq(P(premise), Sp, Implies, Sp, P(result));
    private static Formula EqTo(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Le(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Add(Formula left, Formula right) => P(Seq(left, Plus, right));
    private static Formula Sub(Formula left, Formula right) => P(Seq(left, Minus, right));
    private static Formula Mul(Formula left, Formula right) => P(Seq(left, Sp, Cdot, Sp, right));
    private static Formula Scale(Formula scalar, Formula value) => P(Seq(scalar, Sp, Cdot, Sp, value));
    private static Formula Pow(Formula value, Formula exponent) => Seq(P(value), Caret, Grp(exponent));
    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert, Sp);
    private static Formula At(Formula function, params Formula[] arguments) =>
        Seq(function, P(Seq(JoinArguments(arguments))));
    private static Formula[] JoinArguments(Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return [.. items];
    }
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(variable, Colon, Sp, type)), Sp, P(body));
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Inst(string name, Formula type, Formula body) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp, P(body));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula dimension) => Call("Fin", dimension);
    private static Formula Mat(Formula dimension) => Call("Mat", dimension);
    private static Formula Identity(Formula dimension) => Call("Id", dimension);
    private static Formula Psd(Formula value) => Call("PosSemidef", value);
    private static Formula Effect(Formula value, Formula dimension) => And(Psd(value), Psd(Sub(Identity(dimension), value)));
    private static Formula Statement(string name)
    {
        Formula d = V("d"), n = V("n"), p = V("p"), e = V("E"), f = V("F"),
            g = V("g"), t = V("t"), s = V("s"), m = V("M"), k = V("K"),
            i = V("i"), b = V("B"), a = V("A"), c = V("c"), index = V("J");
        Formula eps = Varepsilon, matrix = Mat(d), unit = Identity(d), realFunction = Arrow(matrix, Real);
        Formula Defect(Formula function, Formula x, Formula y) => Abs(Sub(Sub(At(function, Add(x, y)), At(function, x)), At(function, y)));
        Formula Positivity() => All(e, matrix, Imp(Effect(e, d), Le(D(0), At(p, e))));
        Formula Additivity() => All(e, matrix, All(f, matrix,
            Imp(And(Psd(e), Psd(f), Effect(Add(e, f), d)), Le(Defect(p, e, f), eps))));
        Formula Normalized() => EqTo(At(p, unit), D(1));
        Formula Globals() => And(Positivity(), Additivity(), Normalized());
        Formula UnitInterval(Formula x) => And(Le(D(0), x), Le(x, D(1)));
        Formula Dimensions(Formula body) => All(d, Nat, body);
        Formula Parameters(Formula body) => Dimensions(All(p, realFunction, All(eps, Real, body)));
        Formula Weighted(Formula j, Formula weights) => SumOver(i, j, Scale(At(weights, i), At(b, i)));
        Formula Values(Formula j, Formula weights) => SumOver(i, j, Mul(At(weights, i), At(p, At(b, i))));
        Formula Family(Formula j, Formula bound) => All(b, Arrow(j, matrix), All(t, Arrow(j, Real),
            Imp(And(All(i, j, Effect(At(b, i), d)), All(i, j, UnitInterval(At(t, i))),
                Effect(Weighted(j, t), d)), Le(Abs(Sub(At(p, Weighted(j, t)), Values(j, t))), Mul(bound, eps)))));
        Formula FiniteIndex(Formula body) => All(index, Call("Type"),
            Inst("Fintype", index, Inst("Nonempty", index, body)));
        Formula body = name switch
        {
            "Mat" => Dimensions(EqTo(matrix, Call("Matrix", Fin(d), Fin(d), Complex))),
            "IsEffect" => Dimensions(All(e, matrix, Seq(Call("IsEffect", e), Sp, Iff, Sp, P(Effect(e, d))))),
            "effect_iff_order" => Dimensions(All(e, matrix,
                Seq(Call("IsEffect", e), Sp, Iff, Sp, P(And(Le(D(0), e), Le(e, unit)))))),
            "cstar_effect_bridge" => Dimensions(All(V("X"), Call("CStarMatrix", Fin(d), Fin(d), Complex),
                Seq(Call("IsEffect", Call("ofMatrixInverse", V("X"))), Sp, Iff, Sp,
                    P(And(Le(D(0), V("X")), Le(V("X"), D(1))))))),
            "bounded_interval_stability" => All(g, Arrow(Real, Real), All(eps, Real, All(m, Real,
                Imp(And(Le(D(0), eps), EqTo(At(g, D(1)), D(0)),
                    All(t, Real, Imp(UnitInterval(t), Le(Abs(At(g, t)), m))),
                    All(s, Real, All(t, Real, Imp(And(Le(D(0), s), Le(D(0), t), Le(Add(s, t), D(1))),
                        Le(Defect(g, s, t), eps))))),
                    All(t, Real, Imp(UnitInterval(t), Le(Abs(At(g, t)), Mul(D(2), eps)))))))),
            "probability_bounds" => Parameters(Imp(Globals(), And(
                And(Le(D(0), At(p, D(0))), Le(At(p, D(0)), eps)),
                All(e, matrix, Imp(Effect(e, d), And(Le(D(0), At(p, e)), Le(At(p, e), Add(D(1), eps)))))))),
            "effect_homogeneity" => Parameters(Imp(And(Le(D(0), eps), Globals()),
                All(e, matrix, Imp(Effect(e, d), All(t, Real, Imp(UnitInterval(t),
                    Le(Abs(Sub(At(p, Scale(t, e)), Mul(t, At(p, e)))), Mul(D(2), eps)))))))),
            "finite_sum_error" => Parameters(Imp(Additivity(), All(n, Nat,
                All(a, Arrow(Fin(Add(n, D(1))), matrix), Imp(And(
                    All(i, Fin(Add(n, D(1))), Psd(At(a, i))), Effect(SumOver(i, Fin(Add(n, D(1))), At(a, i)), d)),
                    Le(Abs(Sub(At(p, SumOver(i, Fin(Add(n, D(1))), At(a, i))),
                        SumOver(i, Fin(Add(n, D(1))), At(p, At(a, i))))), Mul(Call("real", n), eps))))))),
            "weighted_finite_sum_error" => Dimensions(All(n, Nat, All(p, realFunction, All(eps, Real,
                Imp(And(Le(D(0), eps), Globals()), Family(Fin(Add(n, D(1))),
                    Sub(Mul(D(3), Add(Call("real", n), D(1))), D(1)))))))),
            "weighted_fintype_error" => Dimensions(FiniteIndex(All(p, realFunction, All(eps, Real,
                Imp(And(Le(D(0), eps), Globals()), Family(index, Sub(Mul(D(3), Call("real", Call("card", index))), D(1)))))))),
            "finite_positive_family_error" => Dimensions(FiniteIndex(All(p, realFunction, All(eps, Real, All(k, Real,
                Imp(And(Le(D(0), eps), Le(D(1), k), Globals()),
                    All(b, Arrow(index, matrix), All(c, Arrow(index, Real),
                        Imp(And(All(i, index, Effect(At(b, i), d)),
                            Le(SumOver(i, index, At(b, i)), Scale(k, unit)),
                            All(i, index, Le(Abs(At(c, i)), k))), All(e, matrix,
                                Imp(And(Effect(e, d), EqTo(e, Weighted(index, c))),
                                    Le(Abs(Sub(At(p, e), Values(index, c))),
                                        Mul(Mul(Pow(k, D(2)), Add(Mul(D(6), Call("real", Call("card", index))), D(1))), eps))))))))))))),
            _ => throw new ArgumentOutOfRangeException(nameof(name))
        };
        return Disp(body);
    }
}
