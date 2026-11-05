using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class VacuumOnePhotonWignerMajorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ContinuousObservables/deboer2025wignermajorization");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vacuum and one-photon mixtures form two oppositely ordered chains meeting at one half.", H("Vacuum and one-photon Wigner-majorization chains"), Blocks(
            Node("fockWigner", All("n", Nat(), All("x", Real(), All("p", Real(), Eqn(Call("fockWigner", Id("n"), Id("x"), Id("p")), Mul(Mul(Div(Pow(Negate(D(1)), Id("n")), Qualified("Real.pi")), Call("Real.exp", Negate(Add(Pow(Id("x"), D(2)), Pow(Id("p"), D(2)))))), Call("D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality.genLaguerre", D(0), Id("n"), Mul(D(2), Add(Pow(Id("x"), D(2)), Pow(Id("p"), D(2)))))))))),
                "Page 16, Eq. (99), gives “W_{|n⟩}(x,p) = ((−1)ⁿ/π) e^{−(x²+p²)} Lₙ(2(x²+p²))”. The polynomial Lₙ is genLaguerre 0 n, with natural occupation n and real phase-space coordinates x and p.", false, AssessedProvenance.FromLiterature(Source)),
            Node("mixtureWigner", All("u", Real(), All("x", Real(), All("p", Real(), Eqn(Call("mixtureWigner", Id("u"), Id("x"), Id("p")), Add(Mul(Sub(D(1), Id("u")), Call("fockWigner", D(0), Id("x"), Id("p"))), Mul(Id("u"), Call("fockWigner", D(1), Id("x"), Id("p")))))))),
                "Page 16, Eq. (100): “W̃_u(r) = (1 − u) W_{|0⟩}(r) + u W_{|1⟩}(r)”, with “u ∈ [0, 1]”. The expression is defined for real u; the two chain statements restrict the physical interval.", false, AssessedProvenance.FromLiterature(Source)),
            Node("levelFunctional", All("W", Arrow(Real(), Arrow(Real(), Real())), All("t", Real(), Eqn(Call("levelFunctional", Id("W"), Id("t")), Integral("r", Seq(Real(), Times, Real()), null, Call("max", Sub(Call("abs", At(Id("W"), Call("Prod.fst", Id("r")), Call("Prod.snd", Id("r")))), Id("t")), D(0)))))),
                "Page 16, Eq. (97): “I_t[|W_ρ̂|] ≡ ∫ [|W_ρ̂(r)| − t]₊ dr”. The positive part is max with zero and the integral uses product Lebesgue measure on the actual plane.", false, AssessedProvenance.FromLiterature(Source)),
            Node("WignerMajorizes", All("W1", Arrow(Real(), Arrow(Real(), Real())), All("W2", Arrow(Real(), Arrow(Real(), Real())), Eqn(Call("WignerMajorizes", Id("W1"), Id("W2")), All("t", Real(), Imp(Leqn(D(0), Id("t")), Leqn(Call("levelFunctional", Id("W2"), Id("t")), Call("levelFunctional", Id("W1"), Id("t")))))))),
                "Page 16, Result 8: “We define that ρ̂₁ ≻_W ρ̂₂ if and only if |W₁| ≻_w |W₂|”. The threshold formulation in Eq. (98) compares these level functionals for every t ≥ 0. The two mixtures have integrable absolute values.", false, AssessedProvenance.FromLiterature(Source)),
            Node("claim", Eqn(Id("claim"), ClaimBody()),
                "Page 17, Section V.A.1: “By trying for several instances, we may conjecture that there is a majorization order along the family W̃_u only as long as u > 1/2.” “It would be interesting to understand this observation better analytically. We leave this question for future works.” The proposition specifies increasing order on [1/2,1] and decreasing order on [0,1/2], including both endpoints.", false, AssessedProvenance.FromLiterature(Source)),
            Node("result", ClaimBody(),
                "Both intervals form chains for every nonnegative threshold. Polar integration identifies the level functional with the affine family h+c*h′, where h(s)=s*exp(−s), c=1−2*u and T=pi*t. Derivative cancellation gives a convex minimum at c=0. The two monotone rays give the opposite directions on the two parameter intervals. Strictness and complete comparisons between the intervals remain separate questions.", true, AssessedProvenance.FromRepo(Source))
        )));

    private static DocumentBlock Node(string name, Formula formula, string prose, bool theorem, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("vacuumonephotonwignermajorization-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(name), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            theorem ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("de-boer-di-giulio-keski-vakkuri-tonni-2024-wigner-majorization-chains"),
                ResolutionKind.Proved) : null);

    private static Formula ClaimBody() => And(All("u", Real(), All("v", Real(), Imp(Leqn(Div(D(1), D(2)), Id("u")), Imp(Leqn(Id("u"), Id("v")), Imp(Leqn(Id("v"), D(1)), Call("WignerMajorizes", Call("mixtureWigner", Id("v")), Call("mixtureWigner", Id("u")))))))), All("u", Real(), All("v", Real(), Imp(Leqn(D(0), Id("u")), Imp(Leqn(Id("u"), Id("v")), Imp(Leqn(Id("v"), Div(D(1), D(2))), Call("WignerMajorizes", Call("mixtureWigner", Id("u")), Call("mixtureWigner", Id("v")))))))));

    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Qualified(string name)
    {
        var parts = name.Split('.');
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Seq(Operatorname, Grp(Id(part))));
        }
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Qualified(name), [.. args]);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula Leqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Negate(Formula a) => new Formula.Negate(Parenthesized(a));
    private static Formula Nat() => Seq(Mathbb, Grp(Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Integral(string name, Formula type, Formula? domain, Formula body) =>
        Seq(Int, Underscore, Grp(Seq(Id(name), Colon, type,
            domain is null ? Seq() : Seq(Sp, InMacro, Sp, domain))), Sp, Parenthesized(body));
}
