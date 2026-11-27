using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletZeroPowerSumsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arithmetic moments and the actual Dirichlet zero divisor",
        H("All zeros with analytic multiplicity"),
        Blocks(
            Paragraph(Text("Let χ be a primitive nonprincipal complex Dirichlet character "
                + "of positive modulus q. The index set is the zero set of the original "
                + "L-function, including its trivial zeros. Each distinct zero ρ carries "
                + "the weight m(ρ) = analyticOrderNatAt(Lχ,ρ). Thus repeated zeros are "
                + "counted with their actual analytic multiplicities. No hypothesis on "
                + "the location of the nontrivial zeros is imposed.")),
            Paragraph(Text("For a complex Dirichlet character χ modulo q, moment(χ,k,t) is "
                + "the negative real part of the sum over n ≥ 2 of "
                + "Λ(n)χ(n)(log n)^k divided by k! n^(2+it). "
                + "The finite moment uses 2 ≤ n ≤ X with the same normalization. "
                + "The zero and one terms vanish. The bound is independent of t and q, "
                + "and includes principal and imprimitive characters and k = 0.")),
            ArithmeticDefinition("moment-term", "momentTerm", "The normalized complex summand",
                ArithmeticTermFormula(), "LSeriesTerm(f,s,n) is zero at n = 0 and equals f(n)/n^s "
                    + "otherwise. The coefficient function uses the real von Mangoldt value "
                    + "and real logarithm, each cast to the complex numbers. The inverse "
                    + "factorial is also a complex scalar."),
            ArithmeticDefinition("moment", "moment", "The full negative real moment",
                ArithmeticMomentFormula(false),
                "The unbounded tsum ranges over all natural numbers. "
                    + "The zero and one summands vanish; the minus sign is outside the "
                    + "real-part operation."),
            ArithmeticDefinition("finite-moment", "finiteMoment", "The arithmetic cutoff moment",
                ArithmeticMomentFormula(true), "The finite sum is over range(X+1), namely "
                    + "0 ≤ n ≤ X. It uses the same complex summand and negative real "
                    + "part as the full moment, with no change of normalization."),
            Describe.Lean(DescribeId.Create("finite-moment-error"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletZeroPowerSums.finite_moment_error"),
                H("An explicit arithmetic cutoff"),
                StatementSource.FromAuthor(TruncationClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The cutoff condition is exp(4(k+1)) ≤ X. "
                        + "The error between the full and finite negative real parts is "
                        + "at most (2/3)^(k+1), as is the norm of the complex series error. "
                         + "The series converges without a cutoff condition. "
                        + "Thus X may be "
                        + "the ceiling of exp(4(k+1)), "
                        + "or any larger natural number.")),
                    Paragraph(Text("Use |χ(n)| ≤ 1 and Λ(n) ≤ log n. "
                        + "The exponential series bounds (log n/2)^(k+1)/(k+1)! by √n. "
                        + "Consequently the normalized summand is bounded by "
                        + "2^(k+1)(k+1)n^(-3/2). The integral test bounds its tail "
                        + "after every positive X by 2^(k+2)(k+1)X^(-1/2). "
                        + "The cutoff and k+1 ≤ 2^k reduce this to "
                        + "(4/exp(2))^(k+1) ≤ (2/3)^(k+1).")),
                    Paragraph(Text("The cutoff estimate holds for every character, including "
                        + "principal and imprimitive characters. Combined with the zero "
                        + "power-sum identity below, it transports finite arithmetic tests "
                        + "to bounds on the full zero moments."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("moment-zero-power-has-sum"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletZeroPowerSums.moment_zero_power_hasSum"),
                H("The absolutely convergent moment identity"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real t and positive integer k, the complex "
                        + "zero power sum equals the negative of the normalized arithmetic "
                        + "series. Its real part is precisely moment(χ,k,t). The norm "
                        + "series also converges, so the identity is independent of the "
                        + "order in which zeros are summed.")),
                    Paragraph(Text("To use the entire-function difference formula for the "
                        + "original L-function, first bound the reciprocal Gamma function "
                        + "globally. On the right half-plane its vertical product and the "
                        + "positive global minimum of the real Gamma function give an "
                        + "exponential height bound. On the left half-plane the reflection "
                        + "formula reduces it to the right-half-plane Gamma growth bound, "
                        + "multiplied by a sine of exponential height. Both estimates are "
                        + "bounded by exp(C(1+|s|)^(3/2)). Combining this with completed "
                        + "L-function growth proves the same type of bound for Lχ itself, "
                        + "including the points where the meromorphic Gamma factor has a pole.")),
                    Paragraph(Text("The general logarithmic derivative power-sum theorem "
                        + "applies to the entire Lχ using its nonzero value at the center "
                        + "2+it; the general theorem needs only this local nonvanishing. "
                        + "The completed growth and Gamma interfaces are reused directly "
                        + "from DirichletTrivialZeros. On Re(s)>1, the logarithmic derivative "
                        + "is the negative "
                        + "L-series of χΛ. Differentiating that absolutely convergent "
                        + "L-series k times inserts (−log n)^k. The factorial and sign "
                        + "normalizations then give the stated complex identity. Iterated "
                        + "coefficient multiplication uses Mathlib mul_left_iterate_apply "
                        + "on the function multiplication monoid.")),
                    Paragraph(Text("The restriction k≥1 removes the undetermined constant "
                        + "in the logarithmic derivative. Primitivity is used for the "
                        + "completed functional equation and its global growth bound; "
                        + "nonprincipality supplies entire continuation. The result "
                        + "does not assert the finite arithmetic inequalities needed "
                        + "for zero exclusion."))),
                DescribeRole.Theorem))));

    private static DocumentBlock ArithmeticDefinition(string id, string name, string title,
        Formula formula, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/CharacterSums/DirichletZeroPowerSums." + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ArithmeticTermFormula()
    {
        var q = F.Id("q");
        var c = F.Id("chi");
        var k = F.Id("k");
        var t = F.Id("t");
        var n = F.Id("n");
        var m = F.Id("m");
        var coefficient = Lambda("m", At("Naturals"),
            Mul(Mul(At("apply", c, At("natToZMod", q, m)),
                At("realToComplex", At("vonMangoldtReal", m))),
                new Formula.Power(At("realToComplex", At("realLog", At("natToReal", m))), k)));
        var line = Add(F.D(2), Mul(At("realToComplex", t), At("imaginaryUnit")));
        var term = Mul(At("inverse", At("natToComplex", At("factorial", k))),
            At("LSeriesTerm", coefficient, line, n));
        return F.Disp(All("q", At("Naturals"), All("chi", At("ComplexDirichletCharacters", q),
            All("k", At("Naturals"), All("t", At("Reals"), All("n", At("Naturals"),
                Equal(At("momentTerm", c, k, t, n), term)))))));
    }

    private static Formula ArithmeticMomentFormula(bool finite)
    {
        var q = F.Id("q");
        var c = F.Id("chi");
        var k = F.Id("k");
        var x = F.Id("X");
        var t = F.Id("t");
        var summands = Lambda("n", At("Naturals"), At("momentTerm", c, k, t, F.Id("n")));
        var sum = finite ? At("finsetSum", At("range", Add(x, F.D(1))), summands)
            : At("tsum", summands);
        var left = finite ? At("finiteMoment", c, k, x, t) : At("moment", c, k, t);
        var body = All("t", At("Reals"), Equal(left, At("neg", At("re", sum))));
        if (finite) body = All("X", At("Naturals"), body);
        return F.Disp(All("q", At("Naturals"), All("chi", At("ComplexDirichletCharacters", q),
            All("k", At("Naturals"), body))));
    }

    private static Formula TruncationClaim()
    {
        var q = F.Id("q");
        var c = F.Id("chi");
        var k = F.Id("k");
        var x = F.Id("X");
        var t = F.Id("t");
        var cutoff = Le(At("exp", At("mul", F.D(4), At("add", k, F.D(1)))), x);
        var diff = At("abs", At("sub", At("moment", c, k, t),
            At("finiteMoment", c, k, x, t)));
        var bound = At("power", new Formula.Fraction(F.D(2), F.D(3)), Add(k, F.D(1)));
        var error = At("complexErrorNorm", c, k, x, t);
        var general = Mul(Mul(At("power", F.D(2), Add(k, F.D(2))),
            Add(k, F.D(1))), At("realPower", x, At("ratio", At("neg", F.D(1)), F.D(2))));
        var conclusion = And(At("Summable", At("momentTerms", c, k, t)),
            And(Implies(At("lt", F.D(0), x), Le(error, general)),
                Implies(cutoff, And(Le(error, bound), Le(diff, bound)))));
        return F.Disp(All("q", At("Naturals"),
            All("chi", At("ComplexDirichletCharacters", q), All("k", At("Naturals"),
                All("X", At("Naturals"), All("t", At("Reals"), conclusion))))));
    }

    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula Claim()
    {
        var q = F.Id("q");
        var c = F.Id("chi");
        var k = F.Id("k");
        var t = F.Id("t");
        var z = F.Id("rho");
        var zeros = At("zeroSet", At("LFunction", c));
        var center = Add(F.D(2), Mul(At("realToComplex", t), At("imaginaryUnit")));
        var summand = Mul(At("natToComplex", At("analyticOrderNatAt", At("LFunction", c), z)),
            At("power", At("inverse", Sub(center, z)), Add(k, F.D(1))));
        var terms = Lambda("rho", zeros, summand);
        var arithmetic = At("neg", At("tsum", Lambda("n", At("Naturals"),
            At("momentTerm", c, k, t, F.Id("n")))));
        var result = And(At("HasSum", terms, arithmetic),
            And(At("Summable", Lambda("rho", zeros, At("norm", summand))),
                Equal(At("moment", c, k, t), At("re", At("tsum", terms)))));
        return F.Disp(All("q", At("PositiveNaturals"),
            All("chi", At("ComplexDirichletCharacters", q),
                Implies(And(At("IsPrimitive", c), At("Nonprincipal", c)),
                    All("k", At("PositiveNaturals"), All("t", At("Reals"), result))))));
    }

    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Lambda(string name, Formula type, Formula body) => F.Seq(
        F.Open, F.Id("fun"), F.Sp, F.Open, F.Id(name), F.Colon, F.Sp, type, F.Close,
        F.Sp, F.Mapsto, F.Sp, body, F.Close);
}
