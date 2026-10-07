using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class PrecessionUniversalThresholdRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/huynhvu2024universal");
    private static readonly Formula n = F.Id("N"), j = F.Id("j"), k = F.Id("K"),
        r = F.Id("r"), x = F.Id("x"), y = F.Id("y"), rho = F.Id("rho"), s = F.Id("S");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A spin-1/2 singlet tensored with the spin-3/2 endpoint state scores 3/4 at K = 3 while remaining separable across the pair–rest bipartition. The threshold 23/32 therefore fails to certify genuine multipartite entanglement.",
        H("Singlet padding and the universal precession threshold"),
        Blocks(
            Node("siteOperator", "Local operator", SiteFormula(),
                "The operator on site n is tensored with identity operators at every other site. The configuration basis is the dependent product of Fin (j n + 1), where j n is twice the physical spin and ℏ = 1.", DescribeRole.Definition),
            Node("ensembleJ", "Total precession observable", EnsembleFormula(),
                "The source states: \"In each round, one system is prepared in some state, then its total angular momentum is measured along one of the directions\" J_k := cos(2πk/K)J_x + sin(2πk/K)J_y, Eq. (1), PDF p. 2. It then uses J_k = Σ_n J_k^(j_n), Eqs. (4)–(6), PDF p. 3. The spin matrices Jx and Jy and the angle theta are the existing spin definitions; the total components are literal sums of site operators.", DescribeRole.Definition),
            Node("ensembleQ", "Averaged spectral weight", AverageFormula(),
                "The source states: \"Meanwhile, the expected score for a quantum system in the state ρ is given by P_K = tr(ρ Q_K), with\" Q_K := (1/K) Σ_k pos(J_k), Eq. (3), PDF p. 2. pos is the existing Hermitian spectral calculus with weight (1+sgn(m))/2, including half weight at zero. The displayed h supplies a Hermiticity proof for each ensembleJ j K k. Proof irrelevance makes the expression independent of that choice.", DescribeRole.Definition),
            Node("conjecturedThreshold", "Conjectured threshold", ThresholdFormula(),
                "Result 4, PDF p. 9, defines the threshold piecewise: 23/32 for K = 3, (69+√181)/128 for K = 5, and ½[1+c_K(K−1)/(K+1)] otherwise. c K is the existing normalized central binomial coefficient 2^{−(K−1)} binom(K−1, (K−1)/2). Its (K−1)/2 index uses natural floor division; the displayed threshold ratio casts K−1 and K+1 into ℝ.", DescribeRole.Definition),
            Node("SeparableAcross", "Separability over one cut", SeparableFormula(),
                "The source states: \"With these notations, a state ρ_{𝐉,𝐉ᶜ} of a spin ensemble is separable over the 𝐉-𝐉ᶜ bipartition if ρ_{𝐉,𝐉ᶜ} = Σ_k p_k ρ_{𝐉,k} ⊗ ρ_{𝐉ᶜ,k}, where ρ_{𝐉,k} (or ρ_{𝐉ᶜ,k}) is a state within the subspace ⊗_{j∈𝐉} ℋ^(j) (or ⊗_{j′∈𝐉ᶜ} ℋ^(j′)).\" PDF p. 3. The probabilities are nonnegative and sum to one; both factors are normalized density matrices. Tensor-product entries are pulled back by restriction of configurations to the two complementary sets. The finite unnormalized PSD cone separableCone does not include these normalization conditions or these dependent local dimensions.", DescribeRole.Definition),
            Node("SpinGME", "Genuine multipartite entanglement", GmeFormula(),
                "The source states: \"Conversely, ρ_GME is GME if it is not a convex combination of states separable over any bipartition 𝐉: that is, ρ_GME ≠ Σ_𝐉 p_𝐉 ρ_{𝐉,𝐉ᶜ}.\" PDF p. 3. Each summand may use its own cut; both sides of every cut are nonempty. Repeated cuts in a finite mixture allow arbitrary finite decompositions and do not impose a preferred bipartition.", DescribeRole.Definition),
            Node("claim", "Huynh-Vu–Zaw–Scarani Conjecture 3", ClaimFormula(),
                "The source states: \"Consider a spin ensemble. Perform the precession protocol with odd K ≥ 3 on the total angular momentum of the system. If the score P_K > 𝐏_K^conj is obtained, then the spin ensemble is GME.\" Conjecture 3, PDF p. 9. N ≥ 2 counts particles, j n ≥ 1 encodes all positive half-integer spins as twice their value, ρ ranges over every density matrix on the full tensor product, and the score is the real part of trace (ρ * ensembleQ j K).",
                DescribeRole.Definition),
            Node("result", "Refutation", Disp(Not(F.Id("claim"))),
                "The ensemble has spins {1/2,1/2,3/2}. The normalized two-spin singlet projector is tensored with the normalized projector onto the difference of the two extreme spin-3/2 basis vectors. For every remaining spin list, every matrix on its configuration space and every K, prepending two spin-1/2 particles in their normalized singlet preserves the literal precession score. Splitting the sum of site operators gives the pair observable tensored with the rest identity plus the pair identity tensored with the rest observable. The pair's angular momentum annihilates the singlet, so finite spectral calculus preserves its embedding of the remaining system. The score is 3/4 > 23/32. A one-term convex decomposition across the pair–rest cut establishes that the state is not GME.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("huynh-vu-zaw-scarani-2023-universal-gme-threshold-refutation"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("universal-precession-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance ?? AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Call(Formula name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(name)), [.. args]);
    private static Formula Call(string name, params Formula[] args) => Call(F.Id(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Bound(Formula name, Formula type) => Seq(name, Colon, Sp, type);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ge(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.GreaterThanOrEqual, b);
    private static Formula And(params Formula[] terms) => terms.Reverse().Aggregate((b, a) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Not(Formula body) => Seq(Neg, Sp, body);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Parenthesized(type), body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Parenthesized(type), body);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Q(string owner, string name) => Seq(F.Id(owner), Dot, F.Id(name));
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Config(Formula sites) => Seq(Forall, Sp, Bound(F.Id("n"), sites), Comma, Sp,
        Call("Fin", Add(Call("j", Val(F.Id("n"))), D(1))));
    private static Formula FullConfig() => Seq(Forall, Sp, Bound(F.Id("n"), Call("Fin", n)), Comma, Sp,
        Call("Fin", Add(Call("j", F.Id("n")), D(1))));
    private static Formula Mat(Formula t) => Call("Matrix", Parenthesized(t), Parenthesized(t), Complex());
    private static Formula SumOn(string variable, Formula domain, Formula body) => Seq(
        new Formula.Subscript(Sum, Bound(F.Id(variable), domain)), Sp, body);
    private static Formula Ands(params Formula[] items) => And(System.Array.ConvertAll(items, Parenthesized));
    private static Formula NJ(Formula body) => All("N", Nat(), All("j", Arrow(Call("Fin", n), Nat()), body));
    private static Formula Density(Formula a) => Call(Q("GHZMeasureBiseparableBound", "IsDensity"), a);
    private static Formula Eqv(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));

    private static Formula SiteFormula()
    {
        var site = F.Id("n"); var a = F.Id("A");
        var locals = Call("Fin", Add(Call("j", site), D(1)));
        var prod = Seq(new Formula.Subscript(Prod, Seq(r, Sp, InMacro, Sp,
            Call(Q("Finset", "erase"), Q("Finset", "univ"), site))), Sp,
            Call("if", Eq(Call("x", r), Call("y", r)), D(1), D(0)));
        return Disp(NJ(All("n", Call("Fin", n), All("A", Mat(locals),
            All("x", FullConfig(), All("y", FullConfig(),
                Eq(Call("siteOperator", j, site, a, x, y),
                    Mul(Call("A", Call("x", site), Call("y", site)), prod))))))));
    }
    private static Formula EnsembleFormula()
    {
        var kk = F.Id("k"); var site = F.Id("n");
        Formula Component(string op) => SumOn("n", Call("Fin", n),
            Call("siteOperator", j, site, Call(Q("PrecessionSpinOneSeparableBound", op), Call("j", site))));
        var angle = Call(Q("PrecessionSpinOneSeparableBound", "theta"), k, kk);
        var value = Add(Call(Q("HSMul", "hSMul"), Cast(Call(Q("Real", "cos"), angle), Complex()), Component("Jx")),
            Call(Q("HSMul", "hSMul"), Cast(Call(Q("Real", "sin"), angle), Complex()), Component("Jy")));
        return Disp(NJ(All("K", Nat(), All("k", Call("Fin", k), Eq(Call("ensembleJ", j, k, kk), value)))));
    }
    private static Formula AverageFormula()
    {
        var kk = F.Id("k"); var h = F.Id("h");
        var proofType = Seq(Forall, Sp, Bound(kk, Call("Fin", k)), Comma, Sp,
            Call(Q("Matrix", "IsHermitian"), Call("ensembleJ", j, k, kk)));
        var average = Call(Q("HSMul", "hSMul"), Div(D(1), Cast(k, Complex())),
            SumOn("k", Call("Fin", k),
                Call(Q("PrecessionSpinOneSeparableBound", "pos"), Call(h, kk))));
        return Disp(NJ(All("K", Nat(), All("h", proofType,
            Eq(Call("ensembleQ", j, k), average)))));
    }
    private static Formula ThresholdFormula()
    {
        var rest = Mul(Div(D(1), D(2)), Parenthesized(Add(D(1),
            Div(Mul(Call(Q("PrecessionSpinOneSeparableBound", "c"), k), Cast(Parenthesized(Sub(k, D(1))), Real())),
                Cast(Parenthesized(Add(k, D(1))), Real())))));
        return Disp(All("K", Nat(), Eq(Call("conjecturedThreshold", k),
            Call("if", Eq(k, D(3)), Div(D(2, 3), D(3, 2)), Call("if", Eq(k, D(5)),
                Div(Parenthesized(Add(D(6, 9), Call(Q("Real", "sqrt"), D(1, 8, 1)))), D(1, 2, 8)), rest)))));
    }
    private static Formula SeparableFormula()
    {
        var m = F.Id("m"); var p = F.Id("p"); var a = F.Id("A"); var b = F.Id("B");
        var comp = new Formula.Power(s, F.Id("c"));
        Formula Restrict(Formula v, Formula sites) => Parenthesized(Seq(LambdaLower, Sp, Bound(F.Id("n"), sites), Comma, Sp, Call(v, Val(F.Id("n")))));
        var entry = All("x", FullConfig(), All("y", FullConfig(), Eq(Call(rho, x, y),
            SumOn("r", Call("Fin", m), Mul(Mul(Cast(Call("p", r), Complex()),
                Call(a, r, Restrict(x, s), Restrict(y, s))), Call(b, r, Restrict(x, comp), Restrict(y, comp)))))));
        var body = Exists("m", Nat(), Exists("p", Arrow(Call("Fin", m), Real()),
            Exists("A", Arrow(Call("Fin", m), Mat(Config(s))),
            Exists("B", Arrow(Call("Fin", m), Mat(Config(comp))), Ands(
                All("r", Call("Fin", m), Ge(Call("p", r), D(0))),
                Eq(SumOn("r", Call("Fin", m), Call("p", r)), D(1)),
                All("r", Call("Fin", m), Ands(Density(Call("A", r)), Density(Call("B", r)))), entry)))));
        return Disp(NJ(All("S", Call("Finset", Call("Fin", n)), All("rho", Mat(FullConfig()),
            Eqv(Call("SeparableAcross", j, s, rho), body)))));
    }
    private static Formula GmeFormula()
    {
        var m = F.Id("m"); var p = F.Id("p"); var sigma = F.Id("sigma");
        var cut = Call("S", r);
        var body = Exists("m", Nat(), Exists("p", Arrow(Call("Fin", m), Real()),
            Exists("S", Arrow(Call("Fin", m), Call("Finset", Call("Fin", n))),
            Exists("sigma", Arrow(Call("Fin", m), Mat(FullConfig())), Ands(
                All("r", Call("Fin", m), Ge(Call("p", r), D(0))),
                Eq(SumOn("r", Call("Fin", m), Call("p", r)), D(1)),
                All("r", Call("Fin", m), Ands(Call(Q("Finset", "Nonempty"), cut),
                    Call(Q("Finset", "Nonempty"), new Formula.Power(Parenthesized(cut), F.Id("c"))),
                    Density(Call(sigma, r)), Call("SeparableAcross", j, cut, Call(sigma, r)))),
                Eq(rho, SumOn("r", Call("Fin", m), Call(Q("HSMul", "hSMul"), Cast(Call("p", r), Complex()), Call(sigma, r)))))))));
        return Disp(NJ(All("rho", Mat(FullConfig()), Eqv(Call("SpinGME", j, rho), Not(Parenthesized(body))))));
    }
    private static Formula ClaimFormula()
    {
        var site = F.Id("n");
        var score = Call(Q("Complex", "re"), Parenthesized(Call(Q("Matrix", "trace"), Mul(rho, Call("ensembleQ", j, k)))));
        var body = All("K", Nat(), Imp(Call("Odd", k), Imp(Ge(k, D(3)), All("N", Nat(),
            Imp(Ge(n, D(2)), All("j", Arrow(Call("Fin", n), Nat()),
            Imp(All("n", Call("Fin", n), Ge(Call("j", site), D(1))),
            All("rho", Mat(FullConfig()), Imp(Density(rho),
                Imp(Lt(Call("conjecturedThreshold", k), score), Call("SpinGME", j, rho)))))))))));
        return Disp(Eqv(F.Id("claim"), body));
    }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a),
        FormulaLogicOperator.Implies, Parenthesized(b));
}
