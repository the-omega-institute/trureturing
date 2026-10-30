using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class SelfConjugateTwoNodeSchurRatioRegionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/ostrovskii2025amplitude");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On two-node self-conjugate grids in the closed unit disk, both inequalities in Conjecture 6.2 of Ostrovskii and Shcherbakov collapse across all degrees t >= 2 to their first nontrivial degree t = 3. The shifted Schur-ratio bound holds precisely in a closed sector of opening 2*pi/3 with vertex -1, whose largest inscribed origin-centred disk has radius sqrt(3)/2; the nonnegative-real-part hook-Schur bound holds precisely in a closed hyperbolic region inside the right half-disk.",
        H("Exact two-node regions for self-conjugate Schur-ratio and hook-Schur bounds"),
        Blocks(
            Node("two-h", "Two-variable complete homogeneous symmetric polynomial", TwoHFormula(),
                "For any commutative ring R and natural degree m, twoH(m,x,y) sums x^i y^(m-i) over i in Finset.range(m+1), where i ranges over 0,...,m and natural subtraction is truncated at zero. Type denotes an arbitrary universe Type u.",
                "twoH", DescribeRole.Definition),
            Node("conj-pair", "Two-node complex conjugate pair", ConjPairFormula(),
                "Given real coordinates a and b, conjPair(a,b) is the two-entry complex vector on Fin 2 taking value a + b*i at index 0 and a - b*i at index 1. ofReal embeds R into C, Complex.I is the imaginary unit, and ![u,v] denotes the Fin 2 vector literal.",
                "conjPair", DescribeRole.Definition),
            Node("neg-conj-pair", "Negated two-node complex conjugate pair", NegConjPairFormula(),
                "Given real coordinates a and b, negConjPair(a,b) is the two-entry complex vector on Fin 2 taking value -(a + b*i) at index 0 and -(a - b*i) at index 1, so that 1 - (negConjPair(a,b) + 1) equals conjPair(a,b) pointwise.",
                "negConjPair", DescribeRole.Definition),
            Node("slack-f", "Real slack function for the shifted Schur ratio", SlackFFormula(),
                "For natural t and real a, b, F(t,a,b) is the real numerator slack t*(t-1)*(1-a) - t + Re(h(t-1, conjPair(a,b))). Natural subtraction t-1 is truncated at zero, Nat.cast embeds N into R, Re extracts the real part, and h is the complete homogeneous symmetric function on Fin 2 -> C.",
                "F", DescribeRole.Definition),
            Node("first-sector", "Closed sector with vertex minus one", InFirstSectorFormula(),
                "A two-node grid z : Fin 2 -> C lies in inFirstSector(z) when every entry satisfies |Im(z(i))| <= sqrt(3)*(Re(z(i)) + 1), cutting out the closed sector with vertex -1, axis [-1, infinity), and half-opening angle pi/3.",
                "inFirstSector", DescribeRole.Definition),
            Node("char-poly-neg", "Real characteristic polynomial of a negated conjugate pair",
                CharPolyNegConjFormula(),
                "For real a and b, charPolyNegConj(a,b) is the monic quadratic real polynomial (X + C(a))^2 + C(b^2) in Polynomial(R), where Polynomial.X is the indeterminate and Polynomial.C embeds constants.",
                "charPolyNegConj", DescribeRole.Definition),
            Node("char-poly-conj", "Real characteristic polynomial of a conjugate pair",
                CharPolyConjFormula(),
                "For real a and b, charPolyConj(a,b) is the monic quadratic real polynomial (X - C(a))^2 + C(b^2) in Polynomial(R).",
                "charPolyConj", DescribeRole.Definition),
            Node("alt-choose-two-h", "Alternating binomial identity for twoH",
                AlternatingChooseTwoHFormula(),
                "Over any commutative ring R and for every integer t >= 2, the alternating sum over d in Finset.range(t-1) of (-1)^d * choose(t, d+2) * twoH(d+1, x, y) equals t - twoH(t-1, 1-x, 1-y). Induction on t >= 2 splits choose(t+1, d+2) by Pascal's identity and decomposes twoH(d+1, x, y) = x*twoH(d, x, y) + y^(d+1).",
                "alternating_choose_twoH_eq", DescribeRole.Lemma),
            Node("q-closed-form", "Closed form of the two-node shifted Schur ratio",
                QTwoNodeClosedFormFormula(),
                "For t >= 2 and w = a + b*i in the closed unit disk with w != 1, the two-node tableau hook Schur function schurHook(d,0,zeta) reduces to h(d+1,zeta) on zeta = negConjPair(a,b) + 1, while choose(t,2)*e(1,zeta) = t*(t-1)*(1-a) != 0. Applying alternating_choose_twoH_eq yields Q(t,2,1,negConjPair(a,b)+1) = (t - h(t-1,conjPair(a,b))) / (t*(t-1)*(1-a)), and in particular Q(2,2,1,negConjPair(a,b)+1) = 1.",
                "Q_two_node_closed_form", DescribeRole.Lemma),
            Node("first-iff-f", "Equivalence between the ratio bound and nonnegativity of F",
                FirstIffFFormula(),
                "Because conjPair(a,b) is invariant under coordinate swap after complex conjugation, h(t-1,conjPair(a,b)) is real and bounded in absolute value by t on the closed unit disk, so t - h(t-1,conjPair(a,b)) >= 0 while t*(t-1)*(1-a) > 0 for w != 1. Consequently ||Q(t,2,1,negConjPair(a,b)+1)|| <= 1 holds if and only if 0 <= F(t,a,b).",
                "first_inequality_iff_F_nonneg", DescribeRole.Lemma),
            Node("first-region", "Exact sector region for the first two-node inequality",
                FirstRegionFormula(),
                "For w = a + b*i in the closed unit disk with w != 1, charPolyNegConj(a,b) factors over C as (X - z_0)*(X - z_1) for z = negConjPair(a,b). Moreover, ||Q(t,2,1,z+1)|| <= 1 holds for all t >= 2 if and only if it holds at t = 3, which is equivalent to b^2 <= 3*(1-a)^2, to inFirstSector(z), and to P(-1) <= P'(-1)^2 for P = charPolyNegConj(a,b). Uniform Lipschitz monotonicity of F(t,a,b) in a on the unit disk reduces the interior to the upper circular cap b^2 >= 3/4 and the sector boundary b = (sqrt(3)/2)*beta (0 < beta <= 1), where a cube-root-of-unity expansion and a large-t envelope establish F(t,a,b) >= 0 for all t >= 4.",
                "first_inequality_region", DescribeRole.Theorem),
            Node("largest-disk", "Largest origin-centred disk for the two-node Schur-ratio bound",
                LargestDiskFormula(),
                "For 0 < rho <= 1, the universal bound ||Q(t,2,1,z+1)|| <= 1 holds for all t >= 2 and all two-node self-conjugate grids z != ![-1,-1] with ||z(i)|| <= rho if and only if rho <= sqrt(3)/2. Every two-node self-conjugate grid satisfies z(1) = conj(z(0)); when rho <= sqrt(3)/2, the sum-of-squares identity 3*(1-a)^2 - b^2 = (2*a - 3/2)^2 + (3/4 - (a^2 + b^2)) places z inside the admissible sector, whereas for rho > sqrt(3)/2 the boundary pair a = (sqrt(3)/2)*rho, b = rho/2 violates the t = 3 inequality.",
                "largest_admissible_disk", DescribeRole.Theorem),
            Node("second-region", "Exact hyperbolic region for the second two-node inequality",
                SecondRegionFormula(),
                "For w = a + b*i in the closed unit disk with a >= 0, charPolyConj(a,b) factors over C as (X - w_0)*(X - w_1) for w = conjPair(a,b). For every t >= 2, the hook-Schur bound ||schurHook(t-2,0,w)|| <= choose(t,2)*||e(1,w)|| is equivalent to ||h(t-1,w)|| <= t*(t-1)*a, with equality at t = 2 where ||h(1,w)|| = 2*a. Across all t >= 2, the family of inequalities is equivalent to its t = 3 instance, to b^2 <= 3*a^2 + 6*a, and to P(0) <= P'(0)^2 - 3*P'(0) for P = charPolyConj(a,b). Lipschitz transport in a reduces the region to the boundary hyperbola arc b^2 = 3*c^2 + 6*c (0 <= c <= 1/4), where explicit recurrence polynomials handle 3 <= t <= 7 and geometric norm decay handles t >= 8.",
                "second_inequality_region", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("two-node-schur-region-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Op(string name)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp([.. parts]));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Op(name), [.. arguments]);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, domain, Comma, Sp, body);
    private static Formula AllRing(Formula ringVar, Formula body) =>
        Seq(Forall, Sp, ringVar, Colon, Sp, Op("Type"), Comma, Sp,
            OpenBracket, Call("CommRing", ringVar), CloseBracket, Comma, Sp, body);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) =>
        new Formula.Relation(x, op, y);
    private static Formula Eqn(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula NeqTo(Formula x, Formula y) => Rel(x, FormulaRelationOperator.NotEqual, y);
    private static Formula LeqTo(Formula x, Formula y) =>
        Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula IffTo(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula e) => new Formula.Power(x, e);
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula Type(string letter) => Seq(Mathbb, Grp(F.Id(letter)));
    private static Formula Fin2() => Call("Fin", D(2));
    private static Formula Family2() => new Formula.TypeArrow(Fin2(), Type("C"));
    private static Formula At(Formula f, Formula i) => new Formula.Apply(f, [i]);
    private static Formula Vec2(Formula u, Formula v) =>
        Seq(Bang, OpenBracket, u, Comma, Sp, v, CloseBracket);
    private static Formula SumRange(Formula i, Formula bound, Formula body) =>
        Seq(Sum, Underscore, Grp(i, InMacro, Sp, Call("Finset.range", bound)), Sp, body);
    private static Formula ProdFin2(Formula i, Formula body) =>
        Seq(Prod, Underscore, Grp(i, Colon, Fin2()), Sp, body);
    private static Formula Choose(Formula t, Formula k) => Call("choose", t, k);
    private static Formula Cast(Formula target, Formula x) => Call("Nat.cast", target, x);
    private static Formula ComplexPairPlus(Formula a, Formula b) =>
        Add(Call("ofReal", a), Mul(Call("ofReal", b), Op("Complex.I")));
    private static Formula ComplexPairMinus(Formula a, Formula b) =>
        Sub(Call("ofReal", a), Mul(Call("ofReal", b), Op("Complex.I")));
    private static Formula DiskHyp(Formula a, Formula b) =>
        LeqTo(Add(Pow(a, D(2)), Pow(b, D(2))), D(1));
    private static Formula NotOneHyp(Formula a, Formula b) =>
        NeqTo(ComplexPairPlus(a, b), D(1));
    private static Formula ShiftedNeg(Formula a, Formula b) =>
        Parenthesized(Add(Call("negConjPair", a, b), D(1)));

    private static Formula TwoHFormula()
    {
        Formula r = F.Id("R"), m = F.Id("m"), x = F.Id("x"), y = F.Id("y"), i = F.Id("i");
        return Disp(AllRing(r, All(m, Type("N"), All(x, r, All(y, r,
            Eqn(Call("twoH", m, x, y),
                SumRange(i, Add(m, D(1)), Mul(Pow(x, i), Pow(y, Sub(m, i))))))))));
    }

    private static Formula ConjPairFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        return Disp(All(a, Type("R"), All(b, Type("R"),
            Eqn(Call("conjPair", a, b), Vec2(ComplexPairPlus(a, b), ComplexPairMinus(a, b))))));
    }

    private static Formula NegConjPairFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        return Disp(All(a, Type("R"), All(b, Type("R"),
            Eqn(Call("negConjPair", a, b),
                Vec2(Neg(Parenthesized(ComplexPairPlus(a, b))),
                    Neg(Parenthesized(ComplexPairMinus(a, b))))))));
    }

    private static Formula SlackFFormula()
    {
        Formula t = F.Id("t"), a = F.Id("a"), b = F.Id("b"), tr = Cast(Type("R"), t);
        Formula lead = Mul(Mul(tr, Parenthesized(Sub(tr, D(1)))), Parenthesized(Sub(D(1), a)));
        Formula hre = Call("Re", Call("h", Sub(t, D(1)), Call("conjPair", a, b)));
        return Disp(All(t, Type("N"), All(a, Type("R"), All(b, Type("R"),
            Eqn(Call("F", t, a, b), Add(Sub(lead, tr), hre))))));
    }

    private static Formula InFirstSectorFormula()
    {
        Formula z = F.Id("z"), i = F.Id("i");
        Formula bound = LeqTo(new Formula.Absolute(Call("Im", At(z, i))),
            Mul(Call("Real.sqrt", D(3)), Parenthesized(Add(Call("Re", At(z, i)), D(1)))));
        return Disp(All(z, Parenthesized(Family2()),
            IffTo(Call("inFirstSector", z), All(i, Fin2(), bound))));
    }

    private static Formula CharPolyNegConjFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula quad = Add(Pow(Parenthesized(Add(Op("Polynomial.X"), Call("Polynomial.C", a))), D(2)),
            Call("Polynomial.C", Pow(b, D(2))));
        return Disp(All(a, Type("R"), All(b, Type("R"), Eqn(Call("charPolyNegConj", a, b), quad))));
    }

    private static Formula CharPolyConjFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula quad = Add(Pow(Parenthesized(Sub(Op("Polynomial.X"), Call("Polynomial.C", a))), D(2)),
            Call("Polynomial.C", Pow(b, D(2))));
        return Disp(All(a, Type("R"), All(b, Type("R"), Eqn(Call("charPolyConj", a, b), quad))));
    }

    private static Formula AlternatingChooseTwoHFormula()
    {
        Formula r = F.Id("R"), t = F.Id("t"), x = F.Id("x"), y = F.Id("y"), d = F.Id("d");
        Formula term = Mul(Mul(Pow(Parenthesized(Neg(D(1))), d),
            Cast(r, Choose(t, Add(d, D(2))))), Call("twoH", Add(d, D(1)), x, y));
        Formula lhs = SumRange(d, Sub(t, D(1)), term);
        Formula rhs = Sub(Cast(r, t),
            Call("twoH", Sub(t, D(1)), Sub(D(1), x), Sub(D(1), y)));
        return Disp(AllRing(r, All(t, Type("N"), All(x, r, All(y, r,
            Imp(LeqTo(D(2), t), Eqn(lhs, rhs)))))));
    }

    private static Formula QTwoNodeClosedFormFormula()
    {
        Formula t = F.Id("t"), a = F.Id("a"), b = F.Id("b"), tc = Cast(Type("C"), t);
        Formula num = Sub(tc, Call("h", Sub(t, D(1)), Call("conjPair", a, b)));
        Formula den = Mul(Mul(tc, Parenthesized(Sub(tc, D(1)))),
            Parenthesized(Sub(D(1), Call("ofReal", a))));
        Formula c1 = Eqn(Call("Q", t, D(2), D(1), ShiftedNeg(a, b)), new Formula.Fraction(num, den));
        Formula c2 = Eqn(Call("Q", D(2), D(2), D(1), ShiftedNeg(a, b)), D(1));
        return Disp(All(t, Type("N"), All(a, Type("R"), All(b, Type("R"),
            Imp(LeqTo(D(2), t), Imp(DiskHyp(a, b), Imp(NotOneHyp(a, b), And(c1, c2))))))));
    }

    private static Formula FirstIffFFormula()
    {
        Formula t = F.Id("t"), a = F.Id("a"), b = F.Id("b");
        Formula body = IffTo(LeqTo(new Formula.Norm(Call("Q", t, D(2), D(1), ShiftedNeg(a, b))), D(1)),
            LeqTo(D(0), Call("F", t, a, b)));
        return Disp(All(t, Type("N"), All(a, Type("R"), All(b, Type("R"),
            Imp(LeqTo(D(2), t), Imp(DiskHyp(a, b), Imp(NotOneHyp(a, b), body)))))));
    }

    private static Formula FirstRegionFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), t = F.Id("t"), i = F.Id("i");
        Formula p = Call("charPolyNegConj", a, b), z = Call("negConjPair", a, b);
        Formula q3 = LeqTo(new Formula.Norm(Call("Q", D(3), D(2), D(1), ShiftedNeg(a, b))), D(1));
        Formula cone = LeqTo(Pow(b, D(2)), Mul(D(3), Pow(Parenthesized(Sub(D(1), a)), D(2))));
        Formula c1 = Eqn(Call("Polynomial.map", Call("algebraMap", Type("R"), Type("C")), p),
            ProdFin2(i, Parenthesized(Sub(Op("Polynomial.X"), Call("Polynomial.C", At(z, i))))));
        Formula c2 = IffTo(All(t, Type("N"),
            Imp(LeqTo(D(2), t), LeqTo(new Formula.Norm(Call("Q", t, D(2), D(1), ShiftedNeg(a, b))), D(1)))), q3);
        Formula c3 = IffTo(q3, cone);
        Formula c4 = IffTo(cone, Call("inFirstSector", z));
        Formula c5 = IffTo(cone, LeqTo(Call("Polynomial.eval", Neg(D(1)), p),
            Pow(Parenthesized(Call("Polynomial.eval", Neg(D(1)), Call("Polynomial.derivative", p))), D(2))));
        return Disp(All(a, Type("R"), All(b, Type("R"),
            Imp(DiskHyp(a, b), Imp(NotOneHyp(a, b), And(c1, And(c2, And(c3, And(c4, c5)))))))));
    }

    private static Formula LargestDiskFormula()
    {
        Formula rho = Rho, t = F.Id("t"), z = F.Id("z"), i = F.Id("i");
        Formula lhs = All(t, Type("N"), All(z, Parenthesized(Family2()),
            Imp(LeqTo(D(2), t), Imp(Call("selfConjugate", z),
                Imp(All(i, Fin2(), LeqTo(new Formula.Norm(At(z, i)), rho)),
                    Imp(NeqTo(z, Vec2(Neg(D(1)), Neg(D(1)))),
                        LeqTo(new Formula.Norm(Call("Q", t, D(2), D(1),
                            Parenthesized(Add(z, D(1))))), D(1))))))));
        Formula rhs = LeqTo(rho, new Formula.Fraction(Call("Real.sqrt", D(3)), D(2)));
        return Disp(All(rho, Type("R"), Imp(Less(D(0), rho), Imp(LeqTo(rho, D(1)), IffTo(lhs, rhs)))));
    }

    private static Formula SecondRegionFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), t = F.Id("t"), i = F.Id("i");
        Formula p = Call("charPolyConj", a, b), w = Call("conjPair", a, b);
        Formula tr = Cast(Type("R"), t), e1 = new Formula.Norm(Call("e", D(1), w));
        Formula hookT = LeqTo(new Formula.Norm(Call("schurHook", Sub(t, D(2)), D(0), w)),
            Mul(Cast(Type("R"), Choose(t, D(2))), e1));
        Formula hook3 = LeqTo(new Formula.Norm(Call("schurHook", D(1), D(0), w)),
            Mul(Cast(Type("R"), Choose(D(3), D(2))), e1));
        Formula hyp = LeqTo(Pow(b, D(2)), Add(Mul(D(3), Pow(a, D(2))), Mul(D(6), a)));
        Formula dp0 = Call("Polynomial.eval", D(0), Call("Polynomial.derivative", p));
        Formula c1 = Eqn(Call("Polynomial.map", Call("algebraMap", Type("R"), Type("C")), p),
            ProdFin2(i, Parenthesized(Sub(Op("Polynomial.X"), Call("Polynomial.C", At(w, i))))));
        Formula c2 = All(t, Type("N"), Imp(LeqTo(D(2), t), IffTo(hookT,
            LeqTo(new Formula.Norm(Call("h", Sub(t, D(1)), w)),
                Mul(Mul(tr, Parenthesized(Sub(tr, D(1)))), a)))));
        Formula c3 = Eqn(new Formula.Norm(Call("schurHook", D(0), D(0), w)),
            Mul(Cast(Type("R"), Choose(D(2), D(2))), e1));
        Formula c4 = Eqn(new Formula.Norm(Call("h", D(1), w)), Mul(D(2), a));
        Formula c5 = IffTo(All(t, Type("N"), Imp(LeqTo(D(2), t), hookT)), hook3);
        Formula c6 = IffTo(hook3, hyp);
        Formula c7 = IffTo(hyp, LeqTo(Call("Polynomial.eval", D(0), p),
            Sub(Pow(Parenthesized(dp0), D(2)), Mul(D(3), dp0))));
        return Disp(All(a, Type("R"), All(b, Type("R"),
            Imp(LeqTo(D(0), a), Imp(DiskHyp(a, b),
                And(c1, And(c2, And(c3, And(c4, And(c5, And(c6, c7)))))))))));
    }
}
