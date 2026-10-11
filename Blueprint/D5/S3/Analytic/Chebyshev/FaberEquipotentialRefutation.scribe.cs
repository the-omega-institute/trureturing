using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Chebyshev;

internal sealed class FaberEquipotentialRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/minadiaz2025chebyshev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A degree-one monic Faber polynomial is Chebyshev on a compact set but fails on an exterior equipotential.",
        H("Miña-Díaz–Rubin Equipotential Refutation"),
        Blocks(
            Entry("chebyshev", "IsChebyshev", "Monic sup-norm minimization", Chebyshev(),
                "A monic polynomial p of degree n is Chebyshev on E if every uniform real bound "
                + "for any monic degree-n competitor q also bounds p on E. On a compact nonempty set "
                + "this is sup-norm minimization. The definition uses pointwise bounds rather than a supremum operator.",
                DescribeRole.Definition, true),
            Entry("monic-faber", "IsMonicFaber", "The monic Faber normalization", MonicFaber(),
                "Write κ=cap(K)=1/c for the leading coefficient of ψ=φ⁻¹. A monic degree-n polynomial F "
                + "is the monic Faber polynomial when F(ψ(w))−(κw)ⁿ tends to zero at infinity. "
                + "Here infinity is the cobounded filter on ℂ. In the paper F_n is the polynomial part of φⁿ "
                + "and F̂_n=c⁻ⁿF_n. The normalization retains the constant term as well as the leading coefficient.",
                DescribeRole.Definition, true),
            Entry("propagation-claim", "claim", "Equality on K and on its equipotentials", Claim(),
                "Section 2, Problem 2.2, states verbatim: “Suppose the compact set K is such that for some "
                + "n∈ℕ, T_{n,K}=F̂_n, where F̂_n is the nth monic Faber polynomial associated to the map φ "
                + "that satisfies (1.2). Is it true then that T_{n,L_r}=F̂_n for all r>1?” "
                + "The unbounded component Ω of ℂ∖K has g_Ω(z,∞)=log|φ(z)|, with "
                + "φ(z)=cz+c₀+c₋₁/z+… and c=cap(K)⁻¹. When Ω is simply connected, ψ=φ⁻¹ "
                + "and L_r=ψ({w:|w|=r}). In the displayed statement U is {w:1<‖w‖}, "
                + "K is the complement of ψ(U), and L_r is the image of the radius-r sphere. "
                + "The bounded-correction hypothesis is written for ‖w‖>2; n≥1 expresses positive degree. "
                + "Differentiability, injectivity, positive κ and compact complement specify the exterior-map setting.",
                DescribeRole.Definition, true),
            Entry("refutation", "result", "Equality need not persist", Disp(Seq(Neg, Sp, V("claim"))),
                "Take ψ(w)=w+1/(4w)+(1/100)(w⁻²−w⁻⁴), κ=1, n=1 and F=X. "
                + "For |u|,|v|≥1 the perturbation difference is at most (31/100)|u−v|. "
                + "The power-difference bound D5.S3.AnalyticClosure.ComplexPowerDifference.norm_pow_sub_pow_le "
                + "at H=1 supplies this estimate. "
                + "The perturbation estimate gives injectivity on the closed exterior, an upper Lipschitz bound 131/100 "
                + "and the lower bound |u−v|≤2|ψ(u)−ψ(v)|. The open mapping theorem and closedness "
                + "of the closed exterior image show that K is compact and contained in the disc of radius 5/4. "
                + "The boundary values ψ(±1)=±5/4 lie in K, forcing every monic linear competitor "
                + "to have norm at least 5/4. Thus X is Chebyshev on K; ψ(w)−w→0 makes it the monic Faber polynomial. "
                + "For r≥1 and |w|=r, the circle estimate is |ψ(w)−(1/100)(r⁻²−r⁻⁴)|≤r+1/(4r). "
                + "Its proof expands the norm square on a normalized circle and bounds the cross and residual terms. "
                + "At r=2, X−C(3/1600) has norm at most 17/8=3400/1600 on L₂, whereas "
                + "ψ(2)=3403/1600 lies on L₂. Therefore X is not Chebyshev there. "
                + "The supporting lemmas are private: perturbation_lipschitz and injective_closed supply injectivity, "
                + "compact_complement supplies the compact disc containment, circle_algebra_bound and circle_bound "
                + "supply the norm estimate, and chebyshev_of_disc and faber establish the initial equality. "
                + "The conclusion uses one radius and does not assert a formula for the minimizer on every outer curve. "
                + "Theorem 2.1's convergence as r tends to infinity is literature-attested and not formalized here; "
                + "it is consistent with the centre expression tending to zero.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("minadiaz-rubin-2025-chebyshev-faber-equipotential"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => name switch
    {
        "ψ" => Psi,
        "κ" => Kappa,
        _ => F.Id(name)
    };
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula value, Formula arg) => new Formula.Apply(value, [arg]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Polynomial => Call("Polynomial", Complex);
    private static Formula Sets => Call("Set", Complex);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.And, P(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Implies, P(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, P(y));
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert);
    private static Formula Exterior => Seq(Left, OpenBrace, V("w"), Colon, Sp, Complex,
        Sp, Mid, Sp, Less(D(1), Norm(V("w"))), Right, CloseBrace);
    private static Formula Image(Formula psi, Formula set) => Call("image", psi, set);
    private static Formula Complement(Formula set) => Call("compl", set);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        P(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));

    private static Formula Chebyshev()
    {
        Formula e = V("E"), n = V("n"), p = V("p"), q = V("q"), m = V("M"), z = V("z");
        Formula Bound(Formula polynomial) => All("z", Complex,
            Imp(Member(z, e), Leq(Norm(Call("eval", polynomial, z)), m)));
        Formula comparison = All("q", Polynomial, Imp(Call("Monic", q),
            Imp(Eqn(Call("natDegree", q), n), All("M", Real, Imp(Bound(q), Bound(p))))));
        Formula body = And(Call("Monic", p), And(Eqn(Call("natDegree", p), n), comparison));
        return Disp(All("E", Sets, All("n", Nat, All("p", Polynomial,
            Iff(Call("IsChebyshev", e, n, p), body)))));
    }

    private static Formula MonicFaber()
    {
        Formula psi = V("ψ"), kappa = V("κ"), n = V("n"), f = V("F"), w = V("w");
        Formula correction = Lambda("w", Complex,
            Sub(Call("eval", f, At(psi, w)), Pow(Mul(P(Seq(kappa, Colon, Sp, Complex)), w), n)));
        Formula limit = Call("Tendsto", correction, Call("cobounded", Complex), Call("nhds", D(0)));
        return Disp(All("ψ", Seq(Complex, To, Sp, Complex), All("κ", Real,
            All("n", Nat, All("F", Polynomial, Iff(Call("IsMonicFaber", psi, kappa, n, f),
                And(Call("Monic", f), And(Eqn(Call("natDegree", f), n), limit))))))));
    }

    private static Formula Claim()
    {
        Formula psi = V("ψ"), kappa = V("κ"), n = V("n"), f = V("F"), r = V("r"), w = V("w");
        Formula k = Complement(Image(psi, Exterior));
        Formula conclusion = All("r", Real, Imp(Less(D(1), r),
            Call("IsChebyshev", Image(psi, Call("sphere", D(0), r)), n, f)));
        Formula polynomials = All("n", Nat, All("F", Polynomial, Imp(Leq(D(1), n),
            Imp(Call("IsMonicFaber", psi, kappa, n, f),
                Imp(Call("IsChebyshev", k, n, f), conclusion)))));
        Formula bounded = Ex("C", Real, All("w", Complex, Imp(Less(D(2), Norm(w)),
            Leq(Norm(Sub(At(psi, w), Mul(P(Seq(kappa, Colon, Sp, Complex)), w))), V("C")))));
        Formula body = Imp(Less(D(0), kappa), Imp(Call("DifferentiableOn", Complex, psi, Exterior),
            Imp(Call("InjOn", psi, Exterior), Imp(Call("IsCompact", k), Imp(bounded, polynomials)))));
        return Disp(Iff(V("claim"), All("ψ", Seq(Complex, To, Sp, Complex), All("κ", Real, body))));
    }
}
