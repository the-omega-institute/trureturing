using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class DampedSpinKernelPositivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/brodygraefemelanathuru2026phasespace");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The damped spin kernel criterion fails for spin three-halves.",
        H("A negative damped spin distribution satisfying the Husimi coefficient bound"),
        Blocks(
            Node("SpinValid", "Doubled spin selection rules", SpinFormula(),
                "The integers j and m are twice the spin and magnetic quantum numbers. The parity condition uses Euclidean integer remainder.", true),
            Node("CGValid", "Clebsch–Gordan selection rules", ValidFormula(),
                "All three magnetic rules, magnetic conservation, the triangle inequalities and total-spin parity are imposed. Variables jone, mone, jtwo and mtwo denote j₁, m₁, j₂ and m₂.", true),
            Node("CG", "The Condon–Shortley Clebsch–Gordan coefficient", CGFormula(),
                "Racah's factorial formula on doubled integer arguments is zero outside the selection rules. The local fac function is the real cast of the factorial of the nonnegative part of its integer argument. Each live summand has nonnegative factorial arguments. ediv is Lean's Euclidean integer division; mod is its remainder. The alternating sign is the Condon–Shortley phase.", true),
            Node("mag", "The ordered spin basis", MagFormula(),
                "The index i in Fin(n+1) labels the basis J, J−1, …, −J, with J=n/2. val is the natural value of a Fin index; castInt is the integer cast.", true),
            Node("T", "Irreducible tensors", TensorFormula(),
                "Equation (12), page 2: \"the matrix elements of the irreducible tensors in the standard Ĵz-bases are given by ⟨J, m′|T̂^J_{L,k}|J, m⟩ = √((2L + 1)/(2J + 1)) C^{Jm′}_{Jm Lk}, where the C^{JM}_{j1 m1 j2 m2} denote the Clebsch-Gordan coefficients.\" Row i is m′ and column j is m. castReal, castInt and ofReal make the scalar embeddings explicit.", true),
            Node("rhoCoeff", "Density-matrix multipoles", CoeffFormula(),
                "Equation (13), page 2: \"ρ̂ = Σ_{L=0}^{2J} Σ_{k=−L}^{L} ρ_{Lk} T̂^J_{L,k}, ρ_{L,k} = tr((T̂^J_{L,k})† ρ̂).\" The adjoint precedes the density matrix in the product.", true),
            Node("legendre", "Legendre polynomials", LegendreFormula(),
                "Polynomial.shiftedLegendre L is the integer polynomial P_L(1−2x). Mapping to real coefficients and composing with (1−X)/2 gives the ordinary Legendre polynomial for every natural degree.", true),
            Node("assocLegendre", "Associated Legendre functions", AssociatedFormula(),
                "The Condon–Shortley factor is (−1)^m. iterate(derivative,m,p) means m applications of Polynomial.derivative to p; eval evaluates the resulting polynomial at x. The square root is the nonnegative real square root.", true),
            Node("Ypos", "Scaled harmonics of nonnegative order", PositiveHarmonicFormula(),
                "Footnote 1, page 3: \"We use the convention Y^0_0 = 1, so that the spherical harmonics are orthonormal with respect to the uniform probability measure dµ^0_{θ,ϕ} = (4π)^{−1} sin θ dθ dϕ. This differs from the Condon–Shortley convention by a factor of √4π: Y_{Lm} = √4π Y_{Lm,CS}\". The usual 1/√4π factor is therefore absent. The imaginary unit is I. Natural subtraction in L−m is expressed by natSub, and factorials have natural arguments.", true),
            Node("Y", "Scaled harmonics of all integer orders", HarmonicFormula(),
                "Nonnegative k uses toNat(k). Negative k uses the Condon–Shortley conjugation identity with natAbs(k). Harmonics vanish outside |k|≤L.", true),
            Node("r", "The binomial ratio", RatioFormula(),
                "The binomial ratio in equations (44) and (53) is a quotient of real casts of natural binomial coefficients.", true),
            Node("F", "The damped quasidistribution", DistributionFormula(),
                "Equation (44), page 5: \"F^σ(θ, ϕ, t) = a_J Σ_{L,k} e^{−γ L(L+1) t/2} ( C(2J, L) / C(2J+L+1, L) )^{−σ/2} ρ_{Lk}(0) overline(Y_{Lk}(θ, ϕ)).\" Equations (35)–(36) give a_J=(2J+1)^{−1/2}. The outer sum is over range(n+1) and the inner sum over the integer interval Icc(−castInt(L),castInt(L)). rpow denotes the real power, ofReal the complex embedding. sigma, gamma, theta and phi stand for σ, γ, θ and ϕ.", true),
            Node("claim", "The positivity conjecture", ClaimFormula(), SourceQuotation(), true),
            Node("result", "Refutation at spin three-halves", new Formula.Not(Named("claim")),
                "Set n=3, sigma=1, gamma=log(20/11), t=1, rho=Matrix.single(3,3,1) on Fin 4, and theta=phi=0. The four binomial ratios are 1, 3/5, 1/5 and 1/35, and q=exp(−gamma)=11/20 satisfies q^(L(L+1)/2)≤r(3,L) for every L≤3. At the north pole only k=0 contributes. The lowest-weight state's multipole signs alternate, giving F=(1−3q+5q³−7q⁶)/4=−760927/256000000<0. The density predicate is reused directly from D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity: positive semidefinite and trace one. The counterexample has t=1, so equation (53)'s printed omission of t does not affect the refutation.", false, DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool literature, DescribeRole role = DescribeRole.Definition) => Describe.Lean(
            DescribeId.Create("damped-spin-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Alls(string[] names, Formula type, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; i--) body = All(names[i], type, body);
        return body;
    }
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ltq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iffq(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Negate(Formula a) => Sub(D(0), a);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula ChooseIf(Formula cond, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, Parenthesized(cond), Sp, Named("then"), Sp, Parenthesized(yes), Sp, Named("else"), Sp, Parenthesized(no));
    private static Formula SumOver(string variable, Formula set, Formula body) =>
        Seq(Sum, Underscore, Grp(V(variable), Sp, InMacro, Sp, set), Sp, Parenthesized(body));
    private static Formula NumType(string letter) => Seq(Mathbb, Grp(V(letter)));
    private static Formula N => NumType("N");
    private static Formula Z => NumType("Z");
    private static Formula R => NumType("R");
    private static Formula Cx => NumType("C");
    private static Formula FinN => Call("Fin", Add(V("n"), D(1)));
    private static Formula Mat => Call("Matrix", FinN, FinN, Cx);
    private static Formula Rcast(Formula a) => Call("castReal", a);
    private static Formula Icast(Formula a) => Call("castInt", a);
    private static Formula Cr(Formula a) => Call("ofReal", a);
    private static Formula Half(Formula a) => Call("ediv", a, D(2));

    private static Formula SpinFormula() => Alls(["j", "m"], Z, Iffq(Call("SpinValid", V("j"), V("m")),
        And(Leq(D(0), V("j")), And(Leq(Negate(V("j")), V("m")),
            And(Leq(V("m"), V("j")), Eqn(Call("mod", Sub(V("j"), V("m")), D(2)), D(0)))))));

    private static Formula ValidBody() => And(Call("SpinValid", V("jone"), V("mone")),
        And(Call("SpinValid", V("jtwo"), V("mtwo")), And(Call("SpinValid", V("J"), V("M")),
        And(Eqn(V("M"), Add(V("mone"), V("mtwo"))), And(Leq(V("J"), Add(V("jone"), V("jtwo"))),
        And(Leq(Sub(V("jone"), V("jtwo")), V("J")), And(Leq(Sub(V("jtwo"), V("jone")), V("J")),
            Eqn(Call("mod", Add(Add(V("jone"), V("jtwo")), V("J")), D(2)), D(0)))))))));
    private static Formula ValidFormula() => Alls(["jone", "mone", "jtwo", "mtwo", "J", "M"], Z,
        Iffq(Call("CGValid", V("jone"), V("mone"), V("jtwo"), V("mtwo"), V("J"), V("M")), ValidBody()));

    private static Formula CGFormula()
    {
        var jone = V("jone"); var jtwo = V("jtwo"); var mone = V("mone"); var mtwo = V("mtwo"); var j = V("J"); var m = V("M");
        var a = V("A"); var b = V("B"); var c = V("C"); var d = V("D"); var e = V("E"); var z = V("z"); var iz = Icast(z);
        Formula Fac(Formula x) => Call("fac", x);
        var prefactor = Mul(Mul(Mul(Mul(Mul(Mul(
            Div(Mul(Mul(Mul(Rcast(Add(j, D(1))), Fac(Half(Sub(Add(j, jone), jtwo)))),
                Fac(Half(Add(Sub(j, jone), jtwo)))), Fac(a)), Fac(Add(Half(Add(Add(jone, jtwo), j)), D(1)))),
            Fac(Half(Add(j, m)))), Fac(Half(Sub(j, m)))), Fac(Half(Add(jone, mone)))), Fac(b)), Fac(c)), Fac(Half(Sub(jtwo, mtwo))));
        var guard = And(Leq(iz, a), And(Leq(iz, b), And(Leq(iz, c), And(Leq(D(0), Add(d, iz)), Leq(D(0), Add(e, iz))))));
        var denom = Mul(Mul(Mul(Mul(Mul(Fac(iz), Fac(Sub(a, iz))), Fac(Sub(b, iz))), Fac(Sub(c, iz))), Fac(Add(d, iz))), Fac(Add(e, iz)));
        var sum = SumOver("z", Call("range", Add(Call("toNat", a), D(1))), ChooseIf(guard, Div(Pow(Negate(D(1)), z), denom), D(0)));
        var lets = Seq(Named("let"), Sp, Eqn(a, Half(Sub(Add(jone, jtwo), j))), Semi, Sp,
            Eqn(b, Half(Sub(jone, mone))), Semi, Sp, Eqn(c, Half(Add(jtwo, mtwo))), Semi, Sp,
            Eqn(d, Half(Add(Sub(j, jtwo), mone))), Semi, Sp, Eqn(e, Half(Sub(Sub(j, jone), mtwo))), Semi, Sp,
            Eqn(V("fac"), Seq(Named("fun"), Sp, Parenthesized(Seq(V("u"), Colon, Z)), Sp, Mapsto, Sp,
                Rcast(Call("factorial", Call("toNat", V("u")))))), Sp,
            Named("in"), Sp, Mul(Call("sqrt", prefactor), sum));
        return Alls(["jone", "mone", "jtwo", "mtwo", "J", "M"], Z,
            Eqn(Call("CG", jone, mone, jtwo, mtwo, j, m), ChooseIf(Call("CGValid", jone, mone, jtwo, mtwo, j, m), lets, D(0))));
    }

    private static Formula MagFormula() => All("n", N, All("i", FinN,
        Eqn(Call("mag", V("n"), V("i")), Sub(Icast(V("n")), Mul(D(2), Icast(Call("val", V("i"))))))));
    private static Formula TensorFormula() => Alls(["n", "L"], N, All("k", Z, Alls(["i", "j"], FinN,
        Eqn(new Formula.Apply(Call("T", V("n"), V("L"), V("k")), [V("i"), V("j")]),
            Cr(Mul(Call("sqrt", Div(Add(Mul(D(2), Rcast(V("L"))), D(1)), Add(Rcast(V("n")), D(1)))),
                Call("CG", Icast(V("n")), Call("mag", V("n"), V("j")), Mul(D(2), Icast(V("L"))), Mul(D(2), V("k")),
                    Icast(V("n")), Call("mag", V("n"), V("i")))))))));
    private static Formula CoeffFormula() => All("n", N, All("rho", Mat, All("L", N, All("k", Z,
        Eqn(Call("rhoCoeff", V("rho"), V("L"), V("k")), Call("trace", Mul(Call("conjTranspose", Call("T", V("n"), V("L"), V("k"))), V("rho"))))))));
    private static Formula LegendreFormula() => All("L", N, Eqn(Call("legendre", V("L")),
        Call("comp", Call("map", Call("shiftedLegendre", V("L")), Call("castRingHom", R)),
            Mul(Call("C", Div(D(1), D(2))), Parenthesized(Sub(D(1), V("X")))))));
    private static Formula AssociatedFormula() => Alls(["L", "m"], N, All("x", R,
        Eqn(Call("assocLegendre", V("L"), V("m"), V("x")),
            Mul(Mul(Pow(Negate(D(1)), V("m")), Pow(Call("sqrt", Sub(D(1), Pow(V("x"), D(2)))), V("m"))),
                Call("eval", Call("iterate", Named("derivative"), V("m"), Call("legendre", V("L"))), V("x"))))));
    private static Formula PositiveHarmonicFormula() => Alls(["L", "m"], N, Alls(["theta", "phi"], R,
        Eqn(Call("Ypos", V("L"), V("m"), V("theta"), V("phi")), ChooseIf(Leq(V("m"), V("L")),
            Mul(Cr(Mul(Call("sqrt", Div(Mul(Add(Mul(D(2), Rcast(V("L"))), D(1)), Rcast(Call("factorial", Call("natSub", V("L"), V("m"))))),
                    Rcast(Call("factorial", Add(V("L"), V("m")))))), Call("assocLegendre", V("L"), V("m"), Call("cos", V("theta"))))),
                Call("complexExp", Mul(Mul(V("I"), Call("castComplex", V("m"))), Cr(V("phi"))))), D(0)))));
    private static Formula HarmonicFormula() => All("L", N, All("k", Z, Alls(["theta", "phi"], R,
        Eqn(Call("Y", V("L"), V("k"), V("theta"), V("phi")), ChooseIf(Leq(D(0), V("k")),
            Call("Ypos", V("L"), Call("toNat", V("k")), V("theta"), V("phi")),
            Mul(Pow(Cr(Negate(D(1))), Call("natAbs", V("k"))), Call("star", Call("Ypos", V("L"), Call("natAbs", V("k")), V("theta"), V("phi")))))))));
    private static Formula RatioFormula() => Alls(["n", "L"], N,
        Eqn(Call("r", V("n"), V("L")), Div(Rcast(Call("choose", V("n"), V("L"))), Rcast(Call("choose", Add(Add(V("n"), V("L")), D(1)), V("L"))))));
    private static Formula Damping() => Call("exp", Div(Mul(Mul(Mul(Negate(V("gamma")), Rcast(V("L"))), Add(Rcast(V("L")), D(1))), V("t")), D(2)));
    private static Formula Weight() => Pow(Call("r", V("n"), V("L")), Div(Negate(V("sigma")), D(2)));
    private static Formula DistributionFormula() => All("n", N, Alls(["sigma", "gamma", "t"], R, All("rho", Mat, Alls(["theta", "phi"], R,
        Eqn(Call("F", V("n"), V("sigma"), V("gamma"), V("t"), V("rho"), V("theta"), V("phi")),
            Mul(Cr(Pow(Add(Rcast(V("n")), D(1)), Div(Negate(D(1)), D(2)))),
                SumOver("L", Call("range", Add(V("n"), D(1))), SumOver("k", Call("Icc", Negate(Icast(V("L"))), Icast(V("L"))),
                    Mul(Mul(Cr(Mul(Damping(), Weight())), Call("rhoCoeff", V("rho"), V("L"), V("k"))), Call("star", Call("Y", V("L"), V("k"), V("theta"), V("phi"))))))))))));
    private static Formula ClaimFormula()
    {
        var premise = All("L", N, Imp(Leq(V("L"), V("n")), Leq(Mul(Damping(), Weight()), Pow(Call("r", V("n"), V("L")), Div(D(1), D(2))))));
        var conclusion = All("rho", Mat, Imp(Call("IsDensity", V("rho")), Alls(["theta", "phi"], R,
            Leq(D(0), Call("re", Call("F", V("n"), V("sigma"), V("gamma"), V("t"), V("rho"), V("theta"), V("phi")))))));
        return Iffq(Named("claim"), All("n", N, Imp(Leq(D(2), V("n")), All("sigma", R,
            Imp(new Formula.Relation(V("sigma"), FormulaRelationOperator.MemberOf, Call("Icc", Negate(D(1)), D(1))),
                All("gamma", R, Imp(Ltq(D(0), V("gamma")), All("t", R, Imp(Leq(D(0), V("t")), Imp(premise, conclusion))))))))));
    }

    private static string SourceQuotation() =>
        "Section VI, page 8: \"For J > 1/2 we do not have an exact result, but it seems reasonable to conjecture that positivity is ensured provided that the damped σ kernel in (44), due to decoherence, becomes no sharper than the Husimi (σ = −1) kernel. That is, if e^{−½γL(L+1)} ( C(2J,L)/C(2J+L+1,L) )^{−σ/2} ≤ ( C(2J,L)/C(2J+L+1,L) )^{1/2} (53) for all L, then we restore positivity.\" "
        + "Equation (12), page 2: \"the matrix elements of the irreducible tensors in the standard Ĵz-bases are given by ⟨J, m′|T̂^J_{L,k}|J, m⟩ = √((2L + 1)/(2J + 1)) C^{Jm′}_{Jm Lk}, where the C^{JM}_{j1 m1 j2 m2} denote the Clebsch-Gordan coefficients.\" "
        + "Equation (13), page 2: \"ρ̂ = Σ_{L=0}^{2J} Σ_{k=−L}^{L} ρ_{Lk} T̂^J_{L,k}, ρ_{L,k} = tr((T̂^J_{L,k})† ρ̂).\" "
        + "Equation (44), page 5: \"F^σ(θ, ϕ, t) = a_J Σ_{L,k} e^{−γ L(L+1) t/2} ( C(2J, L) / C(2J+L+1, L) )^{−σ/2} ρ_{Lk}(0) overline(Y_{Lk}(θ, ϕ)).\" "
        + "Footnote 1, page 3: \"We use the convention Y^0_0 = 1, so that the spherical harmonics are orthonormal with respect to the uniform probability measure dµ^0_{θ,ϕ} = (4π)^{−1} sin θ dθ dϕ. This differs from the Condon–Shortley convention by a factor of √4π: Y_{Lm} = √4π Y_{Lm,CS}\". "
        + "The encoding uses n=2J≥2, sigma∈[−1,1], gamma>0, t≥0, every L≤n, every positive semidefinite unit-trace matrix rho on Fin(n+1), and all real angles theta and phi. IsDensity is the existing positive-semidefinite unit-trace predicate. Equation (53) is printed without t; the time-dependent premise follows (44), and the counterexample has t=1 so both readings coincide. Real-part nonnegativity is a necessary condition for positivity. The symbols X and I in the definitions denote Polynomial.X and Complex.I, respectively.";
}
