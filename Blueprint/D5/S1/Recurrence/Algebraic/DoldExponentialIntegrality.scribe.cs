using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class DoldExponentialIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/aintlib2026dieudonnedwork");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dold prime-power congruences imply integrality of a formal exponential.",
        H("Dold Congruences and Formal Exponential Integrality"),
        Blocks(
            Node("Dold", "Prime-power congruences", All("c", Seq(N(), Sp, To, Sp, Z()), Seq(Call("Dold", V("c")), Sp, Iff, Sp, P(DoldBody()))),
                "Dold(c) requires divisibility by p to the valuation of m plus one for every prime p and every nonzero natural m.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("logInput", "The rational logarithmic input", All("c", Seq(N(), Sp, To, Sp, Z()), Eqn(Call("logInput", V("c")), Call("mk", Lam("n", N(), new Formula.Fraction(Cast(new Formula.Apply(V("c"), [V("n")]), Q()), Cast(V("n"), Q())))))),
                "The degree-n input coefficient is c(n)/n over the rationals; rational division makes the constant coefficient zero.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("expSeries_nsmul", "Scaling the input takes powers", All("f", PS(Q()), Imp(Eqn(Call("constantCoeff", V("f")), D(0)), All("n", N(), Eqn(Exponential(QualifiedCall("HSMul", "hSMul", V("n"), V("f"))), Pow(Exponential(V("f")), V("n")))))),
                "Substitution into PowerSeries.exp_pow_eq_rescale_exp gives the natural-scaling identity.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("integral_exp_of_dold", "Dold congruences imply integrality", All("c", Seq(N(), Sp, To, Sp, Z()), Imp(Call("Dold", V("c")), All("n", N(), Ex("z", Z(), Eqn(Coeff(V("n"), Exponential(Call("logInput", V("c")))), Cast(V("z"), Q())))))),
                "Apply the sufficient Dieudonne-Dwork criterion at each prime. The Dold congruences make the logarithmic difference locally integral; a rational coefficient integral at every prime has denominator one. The local-integrality induction is adapted from AINTLIB.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("doldexponentialintegrality-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula P(Formula value) => Parenthesized(value);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS(Formula ring) => Call("PowerSeries", ring);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Cast(Formula a, Formula type) => P(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(P(a), Sp, Implies, Sp, P(b));
    private static Formula Lam(string name, Formula type, Formula body) =>
        P(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Coeff(Formula n, Formula series) => Call("coeff", n, series);
    private static Formula DoldBody()
    {
        var p = V("p"); var m = V("m"); var c = V("c");
        var difference = new Formula.Binary(new Formula.Apply(c, [Mul(p, m)]),
            FormulaBinaryOperator.Subtract, new Formula.Apply(c, [m]));
        var divides = Seq(Pow(Cast(p, Z()), Add(Call("padicValNat", p, m), D(1))),
            Sp, Mid, Sp, P(difference));
        var nonzero = Seq(m, Sp, Neq, Sp, D(0));
        return All("p", N(), Imp(QualifiedCall("Nat", "Prime", p),
            All("m", N(), Imp(nonzero, divides))));
    }
    private static Formula QualifiedCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Exponential(Formula input) => Call("subst", input, Call("exp", Q()));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
