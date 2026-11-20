using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class PolynomialMeshBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted pressure interpolation on increasing real meshes",
        H("Real-mesh interpolation and polynomial specialization"),
        Blocks(Describe.Lean(DescribeId.Create("polynomial-mesh-geometry"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.mesh_geometry"),
            H("Uniform geometry for every natural r>=2 and k>=4"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let N=k^r, H=2^r and G=r*2^(r-1), with the natural "
                    + "powers cast to the reals. The next mesh point is at most H*N, "
                    + "its distance from N is at most G*N/k, and it is at most N^2. "
                    + "The pow_step estimate applies Mathlib abs_pow_sub_pow_le to obtain "
                    + "(t+1)^(n+1)-t^(n+1)<=(n+1)*(t+1)^n for t>=0. "
                    + "mesh_bracket specializes the least-index construction to the "
                    + "polynomial mesh. power_atTop supplies divergence, and power_large "
                    + "supplies the positive base used to rewrite N/k as N^(1-1/r) "
                    + "in polynomial_gap.")),
                Paragraph(Text("mesh_power_balance converts r*(a+beta)<=r+1 into "
                    + "N^a*N^beta<=N*k for k>=1. price_gap bounds "
                    + "price(a)-price(b) by 2*(b-a)/(a^2*log(a)) when 1<a<=b "
                    + "and log(a)>=1. record_weight bounds "
                    + "P^a*log(P) by 4*L^a*log(L) for 0<=a<=1, P>1, L>=2 "
                    + "and P<=2*L. price_gap is used in real-mesh interpolation, "
                    + "and record_weight is used to transport the Robin lower bounds.")),
                Paragraph(Text("W_factor is the exact positive-base exponent identity. "
                    + "sample_exponent_lower preserves the same nonnegative lower-bound "
                    + "constant when the exponent decreases at a base greater than one. "
                    + "rescale_lower transports a fixed nonpositive lower bound through "
                    + "a nonnegative bounded weight ratio."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-mesh-pressure-interpolation"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.pressure_mesh_samples_to_all"),
                H("An eventual pressure bound on a real mesh extends to the full real tail"),
                StatementSource.FromAuthor(ClaimMeshInterpolation()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write W(a,X)=X^a*log(X) and "
                        + "S(X)=EulerGamma+log(log(X))-1/log(X)-pressure(price(X)). "
                        + "The mesh is strictly increasing and tends to positive infinity. "
                        + "The gap and sample bounds each hold eventually in the natural "
                        + "index. The clock bound holds at every real X>=2. "
                        + "The exponent balance includes equality.")),
                    Paragraph(Text("The least next mesh point above X gives a bracket "
                        + "n<=X<mesh(k+1), where n=mesh(k). On the chosen tail the "
                        + "gap bound gives X<=(1+G)*n<=n^2. The pressure integral "
                        + "and the derivative of log(log(X))-1/log(X) give "
                        + "|S(X)-S(n)|<=E*(price(n)-price(X)), with "
                        + "E=C*((1+G)*n)^beta. Combining price_gap with the gap bound "
                        + "leaves the power n^(alpha+beta-eta-1) after weighting at n. "
                        + "It is at most one by the exponent balance. The proof uses "
                        + "W(alpha,X)<=2*(1+G)*W(alpha,n) and rescale_lower to "
                        + "transport the resulting lower bound to X."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polynomial-full-pressure-interpolation"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.pressure_samples_to_all"),
                H("From natural polynomial samples to the full real tail"),
                StatementSource.FromAuthor(ClaimInterpolation()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take mesh(k) to be the real cast of k^r, "
                    + "G=r*2^(r-1), eta=1/r and alpha=1-sigma in "
                    + "pressure_mesh_samples_to_all. Strict increase and divergence "
                    + "come from the natural powers. polynomial_gap supplies the "
                    + "eventual gap bound, and beta-1/r<sigma implies "
                    + "alpha+beta-eta<=1. The same W and S give the original "
                    + "polynomial sample bound and the same real-tail conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula All(string name, Formula body) => All(name, Nat, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula AllR(string name, Formula body) => All(name, Real, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static Formula ClaimMeshInterpolation()
    {
        var mesh = F.Id("mesh");
        var g = F.Id("G");
        var eta = F.Id("eta");
        var alpha = F.Id("alpha");
        var beta = F.Id("beta");
        var c = F.Id("C");
        var a = F.Id("A");
        var k = F.Id("k");
        var x = F.Id("X");
        var b = F.Id("B");
        Formula Point(Formula index) => new Formula.Apply(mesh, [index]);
        Formula Value(Formula point) => Multiply(Call("W", alpha, point), Call("S", point));

        var n = Point(k);
        var divergence = AllR("Y", Ex("K", Nat, All("k", Imp(Le(F.Id("K"), k),
            Le(F.Id("Y"), n)))));
        var gap = Ex("K", Nat, All("k", Imp(Le(F.Id("K"), k),
            Le(Subtract(Point(Add(k, D(1))), n),
                Multiply(g, Call("rpow", n, Subtract(D(1), eta)))))));
        var clock = AllR("X", Imp(Le(D(2), x), Le(
            new Formula.Absolute(Subtract(x, Call("clock", x))),
            Multiply(c, Call("rpow", x, beta)))));
        var samples = Ex("K", Nat, All("k", Imp(Le(F.Id("K"), k),
            Le(new Formula.Negate(a), Value(n)))));
        var tail = Ex("B", Real, And(Le(D(0), b), Ex("T", Real,
            AllR("X", Imp(Le(F.Id("T"), x), Le(new Formula.Negate(b), Value(x)))))));

        Formula body = Imp(gap, Imp(clock, Imp(samples, tail)));
        foreach (var premise in new[] {
            Le(Subtract(Add(alpha, beta), eta), D(1)), Le(D(0), a), Le(D(0), c),
            Le(D(0), beta), Le(alpha, D(1)), Le(D(0), alpha), Lt(D(0), eta), Le(D(0), g)
        }) body = Imp(premise, body);
        foreach (var name in new[] { "A", "C", "beta", "alpha", "eta", "G" })
            body = AllR(name, body);
        return Disp(All("mesh", new Formula.TypeArrow(Nat, Real),
            Imp(Call("StrictMono", mesh), Imp(divergence, body))));
    }

    private static Formula ClaimInterpolation()
    {
        var r = F.Id("r"); var beta = F.Id("beta"); var sigma = F.Id("sigma");
        var c = F.Id("C"); var a = F.Id("A"); var x = F.Id("X");
        var k = F.Id("k"); var n = Call("pow", k, r);
        var exponent = Subtract(D(1), sigma);
        Formula Value(Formula t) => Multiply(Call("W", exponent, t), Call("S", t));
        var clock = AllR("X", Imp(Le(D(2), x), Le(
            new Formula.Absolute(Subtract(x, Call("clock", x))),
            Multiply(c, Call("rpow", x, beta)))));
        var samples = Ex("K", Nat, All("k", Imp(Le(F.Id("K"), k),
            Le(new Formula.Negate(a), Value(n)))));
        var conclusion = Ex("B", Real, And(Le(D(0), F.Id("B")), Ex("T", Real,
            AllR("X", Imp(Le(F.Id("T"), x),
                Le(new Formula.Negate(F.Id("B")), Value(x)))))));
        Formula body = Imp(Le(D(0), c), Imp(Le(D(0), a),
            Imp(Lt(new Formula.Fraction(D(1), D(2)), sigma), Imp(Lt(sigma, D(1)),
            Imp(Le(D(0), beta), Imp(Lt(Subtract(beta, new Formula.Fraction(D(1), r)), sigma),
            Imp(clock, Imp(samples, conclusion))))))));
        foreach (var name in new[] { "A", "C", "sigma", "beta" }) body = AllR(name, body);
        return Disp(All("r", Imp(Le(D(2), r), body)));
    }

    private static Formula Claim()
    {
        var r = F.Id("r");
        var k = F.Id("k");
        var n = Call("pow", k, r);
        var next = Call("pow", Add(k, D(1)), r);
        var h = Call("pow", D(2), r);
        var g = Multiply(r, Call("pow", D(2), Subtract(r, D(1))));
        return Disp(All("r", Imp(Le(D(2), r), All("k", Imp(Le(D(4), k),
            And(Le(next, Multiply(h, n)), And(
                Le(Subtract(next, n), Multiply(g, new Formula.Fraction(n, k))),
                Le(next, Call("pow", n, D(2))))))))));
    }
}
