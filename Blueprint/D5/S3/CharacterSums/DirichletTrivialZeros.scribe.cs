using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletTrivialZerosDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete Dirichlet zero divisor",
        H("Simple parity zeros and the completed divisor"),
        Blocks(
            Paragraph(Text("Let χ be a complex Dirichlet character of positive "
                + "modulus q. Its parity a is zero when χ is even, and one otherwise. "
                + "The ordinary and completed L-functions use the Mathlib continuations, "
                + "while completion(χ,s) includes the nonvanishing factor exp(s log(q)/2).")),
            Describe.Lean(DescribeId.Create("trivial-point"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletTrivialZeros.trivialPoint"),
                H("The parity lattice"),
                StatementSource.FromAuthor(TrivialPointDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here n is any natural number and a is the parity. "
                    + "The even lattice includes zero; the odd lattice begins at minus one."))),
                DescribeRole.Definition),
            Definition("completion", "completion", CompletionDefinition(),
                "Fχ(s) = exp(s log(q)/2) completedLFunction(χ,s). The exponential "
                    + "is never zero, so this normalization preserves the zero divisor."),
            Definition("gamma-constant", "gammaConstant", GammaConstantDefinition(),
                "The constant A = max(1,Γ(1/4)) controls Gamma values near zero."),
            Definition("growth-constant", "growthConstant", GrowthConstantDefinition(),
                "G(q) = max(log(A totient(q))+log(q)/2+2 log(2),3)."),
            Auxiliary("gamma-growth-bounds", "gamma_growth_bounds", "Gamma upper bounds",
                GammaClaim(), "For Re z > 0, |Γ(z)| ≤ Γ(Re z). For u ≥ 1/4, the "
                    + "real Gamma value is at most max(Γ(1/4),(ceilNat(u)-1)!), "
                    + "and is either at most Γ(1/4) or strictly below "
                    + "exp((u+1)log(u+1)). The factorial and exponential conclusions "
                    + "are both retained; the factorial subtraction is natural subtraction."),
            Auxiliary("completion-power-growth", "completion_power_growth",
                "Explicit, logarithmic and power growth", GrowthClaim(),
                "For χ nonprincipal, the three displayed bounds hold whenever "
                    + "Re s ≥ 1/2 or χ is primitive. The explicit Gamma prefactor bound "
                    + "and exp(G(q)(1+|s|)(1+log(1+|s|))) are retained alongside the "
                    + "power bound exp(3G(q)(1+|s|)^(3/2)) used by Hadamard analysis. "
                    + "Primitivity supplies reflection on the left half-plane."),
            Auxiliary("completion-zero-strip", "completion_zero_strip", "The open strip",
                StripClaim(), "Every zero of a primitive completion has 0 < Re ρ < 1. "
                    + "The Euler product excludes Re ρ ≥ 1 and the functional equation "
                    + "excludes Re ρ ≤ 0. Nonprincipality is not assumed here."),
            Auxiliary("completion-vertical-resolvent", "completion_vertical_resolvent",
                "The vertical resolvent identity", ResolventClaim(),
                "For primitive nonprincipal χ and Fχ(σ+it) ≠ 0, the real logarithmic derivative "
                    + "at σ+it is the absolutely convergent sum of mρ(σ-Re ρ)/|σ+it-ρ|². "
                    + "The same-character reflection ρ ↦ 1-conj(ρ) preserves orders. "
                    + "Pairing the existing two-point Hadamard identity removes the "
                    + "undetermined constant. The inverse-square zero sum and the strip bound "
                    + "|σ-Re ρ| ≤ |σ|+1 give absolute convergence at every nonzero center."),
            Auxiliary("completion-log-deriv", "completion_logDeriv",
                "Conductor, Gamma and arithmetic logarithmic derivatives", LogDerivClaim(),
                "For Re s > 0, Lχ(s) ≠ 0 and (s ≠ 1 or χ nonprincipal), the normalized "
                    + "logarithmic derivative is (log(q)-log(π))/2 plus half the digamma "
                    + "at (s+a)/2 plus Lχ′/Lχ(s), where a is the parity."),
            Paragraph(Text("Gamma estimates give the growth bounds, while the functional "
                + "equation and half-plane nonvanishing place completed zeros in the open "
                + "strip. The two-point Hadamard identity and reflection yield the "
                + "resolvent formula. Negative-integer derivative nonvanishing gives the "
                + "simple Gamma lattice multiplicities used in the divisor identity.")),
            Describe.Lean(DescribeId.Create("lfunction-zero-divisor"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletTrivialZeros.LFunction_zero_divisor"),
                H("Exact zero set and multiplicity"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every complex s with (s ≠ 0 or q ≠ 1) and "
                        + "(s ≠ 1 or χ nonprincipal), L(s,χ) vanishes exactly when "
                        + "the completed L-function vanishes or s = -a-2n for some n ≥ 0. "
                        + "Its analytic order equals the completed analytic order plus one "
                        + "on that lattice, and equals the completed order elsewhere. "
                        + "Analytic orders take values in the extended natural numbers.")),
                    Paragraph(Text("Write H(z) = 1/Γ(z). The global recurrence "
                        + "H(z) = z H(z+1) proves H′(0) = 1, and at negative integers "
                        + "gives H′(-n-1) = (-n-1)H′(-n). Thus every reciprocal Gamma "
                        + "zero is simple. The nonvanishing exponential factor in ΓR "
                        + "and its affine argument preserve those orders. Multiply the "
                        + "completed function by the reciprocal parity Gamma factor "
                        + "near each regular center to obtain the asserted zero set and additive "
                        + "order formula. Both local exceptions hold everywhere for "
                        + "nonprincipal characters.")),
                    Paragraph(Text("Primitivity is unnecessary for this identity. For "
                        + "primitive characters, a separate nonvanishing theorem for the "
                        + "completed function on Re s ≤ 0 makes the lattice and completed "
                        + "zero sets disjoint. Without that theorem this result allows "
                        + "their multiplicities to add at common zeros. It supplies the "
                        + "divisor correspondence, and asserts no zero-free rectangle."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string name, Formula claim,
        string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/CharacterSums/DirichletTrivialZeros." + name),
            H(name), StatementSource.FromAuthor(claim), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Auxiliary(string id, string name, string title,
        Formula claim, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/CharacterSums/DirichletTrivialZeros." + name),
            H(title), StatementSource.FromAuthor(claim), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula TrivialPointDefinition() => F.Disp(
        All("q", At("Naturals"), All("chi", At("ComplexDirichletCharacters", F.Id("q")),
            All("n", At("Naturals"), Equal(At("trivialPoint", F.Id("chi"), F.Id("n")),
                At("sub", At("neg", At("parity", F.Id("chi"))),
                    At("mul", F.D(2), At("natToComplex", F.Id("n")))))))));

    private static Formula CompletionDefinition()
    {
        var q = F.Id("q");
        var c = F.Id("chi");
        var s = F.Id("s");
        return F.Disp(All("q", At("PositiveNaturals"),
            All("chi", At("ComplexDirichletCharacters", q), All("s", At("Complexes"),
                Equal(At("completion", c, s), At("mul",
                    At("complexExp", At("mul", At("realToComplex",
                        At("div", At("log", q), F.D(2))), s)),
                    At("completedLFunction", c, s)))))));
    }

    private static Formula GammaConstantDefinition() => F.Disp(
        Equal(At("gammaConstant"), At("max", F.D(1), At("RealGamma", At("quarter")))));

    private static Formula GrowthConstantDefinition()
    {
        var q = F.Id("q");
        return F.Disp(All("q", At("Naturals"), Equal(At("growthConstant", q),
            At("max", At("add", At("log", At("mul", At("gammaConstant"),
                At("totient", q))), At("add", At("div", At("log", q), F.D(2)),
                    At("mul", F.D(2), At("log", F.D(2))))), F.D(3)))));
    }

    private static Formula GammaClaim()
    {
        var z = F.Id("z");
        var u = F.Id("u");
        var gamma = At("RealGamma", u);
        var quarter = At("RealGamma", At("quarter"));
        var premise = At("le", At("div", F.D(1), F.D(4)), u);
        var exponential = At("exp", At("mul", At("add", u, F.D(1)),
            At("log", At("add", u, F.D(1)))));
        var normBound = All("z", At("Complexes"), At("implies",
            At("lt", F.D(0), At("re", z)), At("le", At("norm", At("Gamma", z)),
                At("RealGamma", At("re", z)))));
        var alternative = All("u", At("Reals"), At("implies", premise,
            At("or", At("le", gamma, quarter), At("lt", gamma, exponential))));
        var factorial = At("factorial", At("natSub", At("ceilingNat", u), F.D(1)));
        var factorialBound = All("u", At("Reals"), At("implies", premise,
            At("le", gamma, At("max", quarter, factorial))));
        return F.Disp(At("and", normBound, At("and", alternative, factorialBound)));
    }

    private static Formula GrowthClaim()
    {
        var q = F.Id("q");
        var c = F.Id("chi");
        var s = F.Id("s");
        var r = At("add", F.D(1), At("norm", s));
        var u = At("div", At("add", At("norm", s), F.D(4)), F.D(2));
        var explicitBound = At("mul", At("gammaConstant"), At("totient", q), r,
            At("exp", At("add", At("mul", At("div", At("log", q), F.D(2)), r),
                At("mul", u, At("log", u)))));
        var logarithmic = At("exp", At("mul", At("growthConstant", q), r,
            At("add", F.D(1), At("log", r))));
        var power = At("exp", At("mul", F.D(3), At("growthConstant", q),
            At("power", r, At("div", F.D(3), F.D(2)))));
        var size = At("norm", At("completion", c, s));
        return F.Disp(All("q", At("PositiveNaturals"),
            All("chi", At("ComplexDirichletCharacters", q), At("implies",
                At("notPrincipal", c), All("s", At("Complexes"), At("implies",
                    At("or", At("le", At("div", F.D(1), F.D(2)), At("re", s)),
                        At("primitive", c)), At("and", At("lt", size, explicitBound),
                            At("and", At("lt", size, logarithmic), At("lt", size, power)))))))));
    }

    private static Formula StripClaim()
    {
        var c = F.Id("chi");
        var rho = F.Id("rho");
        return F.Disp(All("q", At("PositiveNaturals"),
            All("chi", At("ComplexDirichletCharacters", F.Id("q")), At("implies",
                At("primitive", c), All("rho", At("Complexes"), At("implies",
                    Equal(At("completion", c, rho), F.D(0)), At("and",
                        At("lt", F.D(0), At("re", rho)), At("lt", At("re", rho), F.D(1)))))))));
    }

    private static Formula ResolventClaim()
    {
        var c = F.Id("chi");
        var rho = F.Id("rho");
        var f = At("completion", c);
        var sigma = F.Id("sigma");
        var t = F.Id("t");
        var dx = At("sub", sigma, At("re", rho));
        var dy = At("sub", t, At("im", rho));
        var summand = At("div", At("mul", At("analyticOrderNatAt", f, rho), dx),
            At("add", At("power", dx, F.D(2)), At("power", dy, F.D(2))));
        var point = At("add", At("realToComplex", sigma),
            At("mul", At("realToComplex", t), At("imaginaryUnit")));
        return F.Disp(All("q", At("PositiveNaturals"),
            All("chi", At("ComplexDirichletCharacters", F.Id("q")), At("implies",
                At("primitiveNonprincipal", c), All("sigma", At("Reals"),
                    All("t", At("Reals"), At("implies",
                        At("ne", At("apply", f, point), F.D(0)),
                        At("HasSum", Lambda("rho", At("zeroSet", f), summand),
                            At("re", At("logDeriv", f, point))))))))));
    }

    private static Formula LogDerivClaim()
    {
        var q = F.Id("q");
        var c = F.Id("chi");
        var s = F.Id("s");
        var ordinary = At("LFunction", c);
        var gamma = At("digamma", At("div", At("add", s, At("parity", c)), F.D(2)));
        var conductor = At("realToComplex", At("div",
            At("sub", At("log", q), At("log", At("pi"))), F.D(2)));
        var value = At("add", conductor, At("add", At("mul", At("half"), gamma),
            At("logDeriv", ordinary, s)));
        var premises = At("and", At("lt", F.D(0), At("re", s)), At("and",
            At("ne", At("apply", ordinary, s), F.D(0)),
            At("or", At("ne", s, F.D(1)), At("notPrincipal", c))));
        return F.Disp(All("q", At("PositiveNaturals"),
            All("chi", At("ComplexDirichletCharacters", q), All("s", At("Complexes"),
                At("implies", premises, Equal(At("logDeriv", At("completion", c), s),
                    value))))));
    }

    private static Formula Claim()
    {
        var c = F.Id("chi");
        var s = F.Id("s");
        var lattice = At("existsNatural", At("equalTrivialPoint", c, s));
        var completed = At("completedLFunction", c);
        var ordinary = At("LFunction", c);
        var zeros = At("iff", Equal(At("apply", ordinary, s), F.D(0)),
            At("or", Equal(At("apply", completed, s), F.D(0)), lattice));
        var orders = Equal(At("analyticOrderAt", ordinary, s),
            At("add", At("analyticOrderAt", completed, s),
                At("ifThenElse", lattice, F.D(1), F.D(0))));
        return F.Disp(All("q", At("PositiveNaturals"),
            All("chi", At("ComplexDirichletCharacters", F.Id("q")),
            All("s", At("Complexes"), At("implies", At("and",
                At("or", At("ne", s, F.D(0)), At("ne", F.Id("q"), F.D(1))),
                At("or", At("ne", s, F.D(1)), At("notPrincipal", c))),
                At("and", zeros, orders))))));
    }

    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Lambda(string name, Formula type, Formula body) => F.Seq(
        F.Open, F.Id("fun"), F.Sp, F.Open, F.Id(name), F.Colon, F.Sp, type, F.Close,
        F.Sp, F.Mapsto, F.Sp, body, F.Close);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
