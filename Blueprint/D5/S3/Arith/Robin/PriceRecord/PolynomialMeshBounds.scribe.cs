using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class PolynomialMeshBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial meshes and weighted lower-bound transport",
        H("Bounds consumed by the canonical-record criterion"),
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
                    + "mesh_bracket uses the least next mesh point to bracket every real "
                    + "X>=K^r. power_atTop supplies unboundedness, and power_large "
                    + "supplies the arithmetic logarithm domain.")),
                Paragraph(Text("mesh_power_balance converts r*(a+beta)<=r+1 into "
                    + "N^a*N^beta<=N*k for k>=1. price_gap bounds "
                    + "price(a)-price(b) by 2*(b-a)/(a^2*log(a)) when 1<a<=b "
                    + "and log(a)>=1. record_weight bounds "
                    + "P^a*log(P) by 4*L^a*log(L) for 0<=a<=1, P>1, L>=2 "
                    + "and P<=2*L. These bounds are consumed in the complete "
                    + "polynomial pressure interpolation and original-record transport; "
                    + "none asserts a zeta zero bound.")),
                Paragraph(Text("W_factor is the exact positive-base exponent identity. "
                    + "sample_exponent_lower preserves the same nonnegative lower-bound "
                    + "constant when the exponent decreases at a base greater than one. "
                    + "rescale_lower transports a fixed nonpositive lower bound through "
                    + "a nonnegative bounded weight ratio, treating the sign of the "
                    + "variable explicitly. These algebraic helpers have live consumers "
                    + "in PolynomialCanonicalRecordCriterion.result; they are proof "
                    + "organization rather than additional mathematical endpoints."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polynomial-full-pressure-interpolation"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.pressure_samples_to_all"),
                H("From natural polynomial samples to the full real tail"),
                StatementSource.FromAuthor(ClaimInterpolation()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here W(a,X)=X^a*log(X) and "
                    + "S(X)=EulerGamma+log(log(X))-1/log(X)-pressure(price(X)). "
                    + "For every natural r>=2, real beta,sigma,C,A with C,A>=0, "
                    + "1/2<sigma<1, beta>=0 and beta-1/r<sigma, the displayed "
                    + "full-clock power bound and eventual natural sample lower bound "
                    + "imply one nonnegative uniform constant on the entire real tail. "
                    + "The compact-interval modulus follows from the complete pressure "
                    + "FTC and the derivative of log(log(X))-1/log(X). "
                    + "The polynomial mesh estimate pays the interpolation error, and "
                    + "sign-sensitive rescaling handles negative values of S. "
                    + "There is no beta<=1 assumption and no zero-strip premise. "
                    + "The complete closed-strip iff consumes this theorem internally."))),
                DescribeRole.Theorem))));

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula AllR(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Real, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

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
