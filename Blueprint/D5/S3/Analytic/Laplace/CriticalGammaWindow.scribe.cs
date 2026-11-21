using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class CriticalGammaWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concentration of normalized Laplace moments outside a critical window",
        H("Normalized moments on a multiplicative window"),
        Blocks(Describe.Lean(
            DescribeId.Create("gamma-window"),
            DeclarationHandle.Create("D5/S3/Analytic/Laplace/CriticalGammaWindow.critical_window_off_mass"),
            H("An explicit moment order controls both tails"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("After the growth bound, the remaining damping rate is 510. On the "
                    + "left tail use rate 542 with multiplier exp(32a). On the right use rate 478 "
                    + "with multiplier exp(−48a). Extending each positive majorant to the whole "
                    + "positive half-line gives r to the power −(k+1) by the Gamma integral.")),
                Paragraph(Text("The inequalities 640a−1 ≤ k ≤ 640a and the elementary logarithmic "
                    + "bounds absorb the two multipliers. The left and right contributions are at "
                    + "most M times 512 to the power −k divided by 542 and 478 respectively."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("adjustable-gamma-window"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/CriticalGammaWindow.adjustable_window_off_mass"),
                H("Both tails at an adjustable order and width"),
                StatementSource.FromAuthor(AdjustableClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix 1 < h < b. The left decay rate is σ(h log h − h + 1) − 2. "
                        + "The right decay rate is σ(b − h − h log(b/h)) − 2b. Strictness in the "
                        + "logarithmic inequality log x < x − 1 gives positive slopes for both rates. "
                        + "Every prescribed lower bound therefore holds for both at all sufficiently "
                        + "large σ. The choice of σ may depend on how close h is to b.")),
                    Paragraph(Text("For a positive cutoff a choose k = floor(σha). On the left tail, "
                        + "tilt to hσ and use σha < k+1. On the right tail, tilt to hσ/b and use "
                        + "k ≤ σha. Extending the tilted densities to the positive axis gives the "
                        + "Gamma integral at each rate. After factoring out M times σ to the power "
                        + "−k, the two exponentials carry "
                        + "prefactors 1/σ and b/(hσ). The estimate applies even when k is zero."))),
                DescribeRole.Theorem))));

    private static Formula AdjustableClaim()
    {
        var h = F.Id("h"); var b = F.Id("b"); var s = F.Id("s"); var a = F.Id("a");
        var k = F.Id("k"); var m = F.Id("M"); var u = F.Id("u"); var g = F.Id("g");
        var f = F.Id("f"); var outside = F.Id("S"); var t = F.Id("T");
        var real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var zero = F.D(0); var one = F.D(1); var two = F.D(2);
        Formula Sub(Formula x, Formula y) => F.Seq(F.Open, x, F.Minus, y, F.Close);
        Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
        Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
        var left = Sub(Multiply(s, Add(Sub(Multiply(h, Call("log", h)), h), one)), two);
        var right = Sub(Multiply(s, Sub(Sub(b, h), Multiply(h, Call("log", Frac(b,h))))), Multiply(two,b));
        var tilt = Lt(two, Multiply(s, Sub(one, Frac(h,b))));
        var eventually = All("T", real, new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("C"), real, All("s", real, Implies(Le(F.Id("C"),s),
                And(tilt, And(Lt(t,left), Lt(t,right)))))));
        var growth = All("u", real, Implies(Le(zero,u), Le(new Formula.Absolute(new Formula.Apply(g,[u])),
            Multiply(m, Call("exp", Multiply(two,u))))));
        var kernel = Frac(Multiply(new Formula.Power(u,k), Call("exp", new Formula.Negate(Multiply(s,u)))),
            F.Seq(k,F.Bang));
        var density = Multiply(new Formula.Absolute(new Formula.Apply(g,[u])), kernel);
        var set = F.Seq(F.Open, zero, F.Comma, F.Infty, F.Close, F.Sp, F.Setminus, F.Sp,
            F.OpenBracket, a, F.Comma, Multiply(b,a), F.CloseBracket);
        var bound = Multiply(Multiply(m,new Formula.Power(s,new Formula.Negate(k))),
            Add(Frac(Call("exp",new Formula.Negate(Multiply(left,a))),s),
                Multiply(Frac(b,Multiply(h,s)),Call("exp",new Formula.Negate(Multiply(right,a))))));
        var mass = F.Seq(F.Int, F.Underscore, F.Grp(outside), F.Sp, new Formula.Apply(f,[u]), F.Sp,F.Id("d"),u);
        var estimate = new Formula.Aligned([
            Let(k,new Formula.Floor(Multiply(Multiply(s,h),a))),
            Let(outside,set), Let(f,F.Seq(F.Open,u,F.Sp,F.Mapsto,F.Sp,density,F.Close)),
            And(Call("IntegrableOn",f,outside), Le(mass,bound))]);
        var allInputs = All("s",real,Implies(And(Lt(zero,s),tilt),All("a",real,Implies(Lt(zero,a),
            All("g",new Formula.TypeArrow(real,real),Implies(Call("Measurable",g),
                All("M",real,Implies(growth,estimate))))))));
        return F.Disp(All("h",real,All("b",real,Implies(And(Lt(one,h),Lt(h,b)),And(eventually,allInputs)))));
    }

    private static Formula Claim()
    {
        var a = F.Id("a");
        var u = F.Id("u");
        var k = F.Id("k");
        var g = F.Id("g");
        var m = F.Id("M");
        var f = F.Id("f");
        var s = F.Id("S");
        var real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var hypothesis = All("u", real, Implies(Le(F.D(0), u),
            Le(new Formula.Absolute(new Formula.Apply(g, [u])), Multiply(m, Call("exp", Multiply(F.D(2), u))))));
        var mass = F.Seq(F.Int, F.Underscore, F.Grp(s), F.Sp, new Formula.Apply(f, [u]),
            F.Sp, F.Id("d"), u);
        var constant = Add(new Formula.Fraction(F.D(1), F.D(5,4,2)),
            new Formula.Fraction(F.D(1), F.D(4,7,8)));
        var bound = Multiply(Multiply(m, constant), new Formula.Power(F.D(5,1,2), new Formula.Negate(k)));
        var order = new Formula.Floor(Multiply(F.D(6,4,0), a));
        var rightEndpoint = new Formula.Fraction(Multiply(F.D(3), a), F.D(2));
        var outside = F.Seq(F.Open, F.D(0), F.Comma, F.Infty, F.Close, F.Sp, F.Setminus, F.Sp,
            F.OpenBracket, a, F.Comma, rightEndpoint, F.CloseBracket);
        var density = Multiply(new Formula.Absolute(new Formula.Apply(g, [u])),
            new Formula.Fraction(Multiply(new Formula.Power(u, k),
                Call("exp", new Formula.Negate(Multiply(F.D(5,1,2), u)))), F.Seq(k, F.Bang)));
        var conclusion = new Formula.Aligned([
            Let(k, order),
            Let(f, F.Seq(F.Open, u, F.Sp, F.Mapsto, F.Sp, density, F.Close)),
            Let(s, outside),
            And(Le(a, k), And(Call("IntegrableOn", f, s), Le(mass, bound))),
        ]);
        return F.Disp(All("a", real, Implies(Le(F.D(1), a),
            All("g", new Formula.TypeArrow(real, real), Implies(Call("Measurable", g),
                All("M", real, Implies(hypothesis, conclusion)))))));
    }

    private static Formula Let(Formula name, Formula value) =>
        F.Seq(F.Operatorname, F.Grp(F.Id("let")), F.Sp, name, F.Sp, F.Colon, F.Eq, F.Sp, value, F.Comma);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
