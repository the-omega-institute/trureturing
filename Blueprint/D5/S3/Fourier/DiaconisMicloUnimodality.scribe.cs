using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class DiaconisMicloUnimodalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Fourier/DiaconisMicloUnimodality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/diaconismiclo2013secondorder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The absolute spectral gap of a four-speed walk on ZMod 11 has a strict three-point valley.",
        H("A counterexample to Diaconis–Miclo absolute-gap unimodality"),
        Blocks(
            Definition("K", KernelFormula(), "Interpolated speed transfer",
                "Equation (1.9), p. 578: “∀ a ∈ [0,1],  K⁽ᵃ⁾ := (1 − a)K⁽⁰⁾ + aK⁽¹⁾”. Here K⁽⁰⁾ is uniform on S and K⁽¹⁾ is the identity. Speed values are elements of the subtype {v : G // v ∈ S}."),
            Definition("positionSpeed", PositionFormula(), "Position–speed transition",
                "Equation (1.6), p. 577: “P((x,y),(x′,y′)) = δ_xy(x′) K_{x′}(y,y′)”. In additive notation the next position is x+v and the new speed is sampled from K."),
            Definition("randomWalk", WalkFormula(), "The first-order walk",
                "Equation (1.8), p. 578: “L(x,x′) = μ(x′ − x)”. The measure μ is uniform on the symmetric generating set S."),
            Definition("meanZero", MeanFormula(), "Stationary-mean-zero functions",
                "Page 575: “By invariance of m, the subspace F_*(m,ℂ) := {F ∈ F(V²,ℂ) : m[F] = 0} is stable under M, so let Θ_*(M) ⊂ ℂ be the spectrum of M_*, the restriction of M to F_*(m,ℂ).” Finite weighted expectation is a sum; real weights are coerced to ℂ."),
            Definition("eigenvaluesMeanZero", EigenFormula(), "Eigenvalues on mean-zero functions",
                "Page 575: “By invariance of m, the subspace F_*(m,ℂ) := {F ∈ F(V²,ℂ) : m[F] = 0} is stable under M, so let Θ_*(M) ⊂ ℂ be the spectrum of M_*, the restriction of M to F_*(m,ℂ).” The finite-dimensional expression asks for a nonzero complex eigenfunction of stationary mean zero."),
            Definition("spectralRadiusOnMeanZero", RadiusFormula(), "Absolute spectral radius",
                "Page 575: “The spectral gap of M is λ(M) := 1 − max{|θ| : θ ∈ Θ_*(M)} ∈ [0,1]”. The finite nonempty eigenvalue set in this example permits the maximum's expression as sSup of the norm image."),
            Definition("spectralGapOnMeanZero", GapFormula(), "Absolute spectral gap",
                "Page 575: “The spectral gap of M is λ(M) := 1 − max{|θ| : θ ∈ Θ_*(M)} ∈ [0,1]”. The maximum concerns modulus, including negative and nonreal eigenvalues."),
            Definition("lambdaM", LambdaMFormula(), "The interpolated second-order gap",
                "Equation (1.10), p. 578: “∀ x,x′ ∈ G,  m(x,x′) := 1/(|G||S|)” if x′ − x ∈ S, and “0” otherwise. The gap is computed on G × {v : G // v ∈ S}, with the uniform weights and the position–speed matrix. The displayed expression expands the gap and its mean-zero eigenvalue set. A finite instance on this subtype is supplied by Fintype.ofFinite."),
            Definition("lambdaL", LambdaLFormula(), "The underlying first-order gap",
                "Page 576: “Similar definitions can be given for the spectral gap of L, by replacing the state space V² by V.” The underlying first-order walk uses weight 1/|G| on G and the same absolute spectral gap."),
            Definition("claim", Eqn(Id("claim"), ClaimBody()), "Conjecture 1.3",
                "Conjecture 1.3, p. 580, verbatim: “Let G be a finite Abelian group and S be a generating set of G with |S| ≥ 2. Let K⁽¹⁾ be the identity S × S matrix (seen as a speed transfer kernel, it forces the chain to keep going always in the same direction) and consider again the interpolating kernels given in (1.9), as well as the associated second order Markov kernels M⁽ᵃ⁾ for a ∈ [0,1], which are also trajectorially reversible with respect to the probability measure m defined in (1.10). There exists a₀ ∈ [0,1] such that λ(M⁽ᵃ⁾) is nondecreasing for a ∈ [0,a₀] and nonincreasing on [a₀,1]. Furthermore there exists two values 0 < c₁ < c₂ (perhaps depending on |S|), such that c₁ √λ(L) ≤ λ(M⁽ᵃ⁰⁾) ≤ c₂ √λ(L).” The additive finite group G and symmetric generating finset S carry the stated construction. Both clauses use the same turning point. The result concerns Type at universe zero, which contains ZMod 11."),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For G=ZMod 11 and S={1,2,9,10}={±1,±2}, the gap is greater than 261/500 at a=1/5 and a=3/10, and less than 261/500 at a=1/4. No monotone-then-antitone function has this strict valley. Fourier reduction gives four-dimensional character blocks; exact Schur inequalities bound their endpoint roots by 239/500. A middle-parameter real root has larger modulus. This refutes the conjunction through its unimodality clause. The square-root comparison considered separately and product-group extensions remain open."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, Formula formula, string heading, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(heading),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Id(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(Id(owner)), Dot, Operatorname, Grp(Id(name)));
    private static Formula App(Formula head, params Formula[] args) => new Formula.Apply(head, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Id(name), args);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(Id("C")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string name, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Some(string name, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula And(params Formula[] clauses) => Seq(clauses.SelectMany((clause, index) =>
        index == 0 ? new[] { Parenthesized(clause) } : new[] { Land, Sp, Parenthesized(clause) }).ToArray());
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula LambdaAt(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Proj(Formula a, byte field) => Seq(a, Dot, D(field));
    private static Formula SumAt(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Inst(string name, Formula type) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Group(Formula body, bool finite = false, bool commutative = false, bool group = true) =>
        All("G", Id("Type"), Seq(finite ? Inst("Fintype", Id("G")) : Sp,
            group ? Inst(commutative ? "AddCommGroup" : "AddGroup", Id("G")) : Sp, Comma, Sp,
            All("S", Call("Finset", Id("G")), body)));
    private static Formula Finite(Formula body) => All("alpha", Id("Type"),
        Seq(Inst("Fintype", Id("alpha")), Comma, Sp, body));
    private static Formula Speeds() => Seq(OpenBrace, Id("v"), Colon, Sp, Id("G"), Sp,
        Slash, Slash, Sp, Member(Id("v"), Id("S")), CloseBrace);
    private static Formula States() => Seq(Id("G"), Sp, Times, Sp, Speeds());
    private static Formula CardS() => Cast(App(Q("Finset", "card"), Id("S")), Real());
    private static Formula Uniform() => new Formula.Fraction(D(1), CardS());
    private static Formula MatrixAt(Formula domain) => Call("Matrix", domain, domain, Real());
    private static Formula Weight(Formula domain) => Arrow(domain, Real());
    private static Formula MatrixContext(Formula body) => Finite(All("A", MatrixAt(Id("alpha")),
        All("w", Weight(Id("alpha")), body)));
    private static Formula EigenNorms() => App(Q("Set", "image"),
        LambdaAt("theta", Complex(), new Formula.Norm(Id("theta"))), Call("eigenvaluesMeanZero", Id("A"), Id("w")));

    private static Formula KernelFormula()
    {
        var v = Id("v"); var w = Id("w"); var a = Id("a");
        var uniform = Mul(Sub(D(1), a), Uniform());
        return Group(All("a", Real(), All("v", Speeds(), All("w", Speeds(),
            Eqn(Call("K", Id("S"), a, v, w), Call("ite", Eqn(v, w), Add(uniform, a), uniform))))));
    }
    private static Formula PositionFormula()
    {
        var p = Id("p"); var q = Id("q");
        return Group(All("a", Real(), All("p", States(), All("q", States(),
            Eqn(Call("positionSpeed", Id("S"), Id("a"), p, q),
                Call("ite", Eqn(Proj(q, 1), Add(Proj(p, 1), Proj(Proj(p, 2), 1))),
                    Call("K", Id("S"), Id("a"), Proj(p, 2), Proj(q, 2)), D(0)))))));
    }
    private static Formula WalkFormula() => Group(All("x", Id("G"), All("y", Id("G"),
        Eqn(Call("randomWalk", Id("S"), Id("x"), Id("y")),
            Call("ite", Member(Sub(Id("y"), Id("x")), Id("S")), Uniform(), D(0))))));
    private static Formula MeanFormula() => Finite(All("w", Weight(Id("alpha")),
        All("f", Arrow(Id("alpha"), Complex()), Eqn(Call("meanZero", Id("w"), Id("f")),
            Eqn(SumAt("x", Id("alpha"), Mul(Cast(Call("w", Id("x")), Complex()), Call("f", Id("x")))), D(0))))));
    private static Formula EigenFormula()
    {
        var theta = Id("theta"); var f = Id("f"); var i = Id("i"); var j = Id("j");
        var body = Some("f", Arrow(Id("alpha"), Complex()), And(
            Some("x", Id("alpha"), Ne(Call("f", Id("x")), D(0))),
            Call("meanZero", Id("w"), f),
            All("i", Id("alpha"), Eqn(SumAt("j", Id("alpha"),
                Mul(Cast(Call("A", i, j), Complex()), Call("f", j))), Mul(theta, Call("f", i))))));
        return MatrixContext(Eqn(Call("eigenvaluesMeanZero", Id("A"), Id("w")),
            Seq(OpenBrace, theta, Colon, Sp, Complex(), Sp, Mid, Sp, body, CloseBrace)));
    }
    private static Formula RadiusFormula() => MatrixContext(Eqn(
        Call("spectralRadiusOnMeanZero", Id("A"), Id("w")), Call("sSup", EigenNorms())));
    private static Formula GapFormula() => MatrixContext(Eqn(
        Call("spectralGapOnMeanZero", Id("A"), Id("w")),
        Sub(D(1), Call("spectralRadiusOnMeanZero", Id("A"), Id("w")))));
    private static Formula LambdaMFormula()
    {
        var theta = Id("theta"); var f = Id("f"); var p = Id("p"); var q = Id("q");
        var state = States();
        var uniform = new Formula.Fraction(D(1), Cast(Mul(
            App(Q("Fintype", "card"), Id("G")), App(Q("Finset", "card"), Id("S"))), Real()));
        var eigen = Some("f", Arrow(state, Complex()), And(
            Some("p", state, Ne(Call("f", p), D(0))),
            Eqn(SumAt("p", state, Mul(Cast(uniform, Complex()), Call("f", p))), D(0)),
            All("p", state, Eqn(SumAt("q", state,
                Mul(Cast(Call("positionSpeed", Id("S"), Id("a"), p, q), Complex()), Call("f", q))),
                Mul(theta, Call("f", p))))));
        var radius = Call("sSup", new Formula.SetBuilder(new Formula.Norm(theta), theta,
            Seq(OpenBrace, theta, Colon, Sp, Complex(), Sp, Mid, Sp, eigen, CloseBrace)));
        return Group(All("a", Real(), Eqn(Call("lambdaM", Id("S"), Id("a")), Sub(D(1), radius))), true);
    }
    private static Formula LambdaLFormula()
    {
        var theta = Id("theta"); var f = Id("f"); var x = Id("x"); var y = Id("y");
        var uniform = new Formula.Fraction(D(1), Cast(App(Q("Fintype", "card"), Id("G")), Real()));
        var eigen = Some("f", Arrow(Id("G"), Complex()), And(
            Some("x", Id("G"), Ne(Call("f", x), D(0))),
            Eqn(SumAt("x", Id("G"), Mul(Cast(uniform, Complex()), Call("f", x))), D(0)),
            All("x", Id("G"), Eqn(SumAt("y", Id("G"),
                Mul(Cast(Call("randomWalk", Id("S"), x, y), Complex()), Call("f", y))),
                Mul(theta, Call("f", x))))));
        var radius = Call("sSup", new Formula.SetBuilder(new Formula.Norm(theta), theta,
            Seq(OpenBrace, theta, Colon, Sp, Complex(), Sp, Mid, Sp, eigen, CloseBrace)));
        return Group(Eqn(Call("lambdaL", Id("S")), Sub(D(1), radius)), true);
    }
    private static Formula ClaimBody()
    {
        var s = Id("S"); var a = Id("a"); var peak = Id("a0"); var c1 = Id("c1"); var c2 = Id("c2");
        var gap = LambdaAt("a", Real(), Call("lambdaM", s, a));
        var target = Some("a0", Real(), And(Leq(D(0), peak), Leq(peak, D(1)),
            Call("MonotoneOn", gap, App(Q("Set", "Icc"), D(0), peak)),
            Call("AntitoneOn", gap, App(Q("Set", "Icc"), peak, D(1))),
            Some("c1", Real(), Some("c2", Real(), And(Less(D(0), c1), Less(c1, c2),
                Leq(Mul(c1, App(Q("Real", "sqrt"), Call("lambdaL", s))), Call("lambdaM", s, peak)),
                Leq(Call("lambdaM", s, peak), Mul(c2, App(Q("Real", "sqrt"), Call("lambdaL", s)))))))));
        return Group(Imp(Leq(D(2), App(Q("Finset", "card"), s)),
            Imp(All("v", Id("G"), Imp(Member(Id("v"), s), Member(new Formula.Negate(Id("v")), s))),
                Imp(Eqn(App(Q("AddSubgroup", "closure"), Cast(s, Call("Set", Id("G")))), Q("Top", "top")), target))), true, true);
    }
}
