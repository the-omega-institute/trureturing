using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FunctionField;

internal sealed class CarlitzFiveOrbitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FunctionField/CarlitzFiveOrbit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closing all five conjugate equations forces the exact quintic difference field.",
        H("The Carlitz Five-Orbit Elimination Certificate"),
        Blocks(
            Paragraph(Text("K denotes a field of characteristic nineteen in the theorem. "
                + "The two polynomial definitions make sense in every commutative ring. "
                + "sigma is an actual ring endomorphism; sigma^i(theta) below means "
                + "i-fold composition, not a field-element power. For a q-power Frobenius "
                + "it equals theta^(q^i).")),
            Describe.Lean(
                DescribeId.Create("carlitz-five-residual"),
                DeclarationHandle.Create(Prefix + "residual"),
                H("The literal Thakur residual"),
                StatementSource.FromAuthor(ResidualFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/FunctionFields/niedbala2026carlitz")),
                Blocks(Paragraph(Text("R(a,b,c,d)=1-d*(1-c*(1-b*(1-a))). "
                    + "These arguments are the four actual conjugate differences in "
                    + "equation (2) of arXiv:2607.15305v2. No substituted recurrence "
                    + "or approximate residual is used."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("carlitz-five-quintic"),
                DeclarationHandle.Create(Prefix + "quintic"),
                H("The specified quintic"),
                StatementSource.FromAuthor(QuinticFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/FunctionFields/niedbala2026carlitz")),
                Blocks(Paragraph(Text("mu(a)=a^5+5*a^3+3*a^2-4*a-9. "
                    + "This is the polynomial already exhibited in Theorem 4.1 and "
                    + "Conjecture 4.2 of the cited version. It is not claimed to be "
                    + "a newly discovered polynomial."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("carlitz-five-no-hidden-root"),
                DeclarationHandle.Create(Prefix + "result"),
                H("No hidden difference field in a closed five-orbit"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every field K of characteristic nineteen, every "
                        + "ring endomorphism sigma of K and every theta in K, assume that "
                        + "sigma^5(theta)=theta and that R(sigma(theta)-theta, "
                        + "sigma^2(theta)-theta, sigma^3(theta)-theta, "
                        + "sigma^4(theta)-theta)=0. Then mu(sigma(theta)-theta)=0. "
                        + "No quintic-root, irreducibility, finite-field size or "
                        + "pairwise-distinctness hypothesis is supplied.")),
                    Paragraph(Text("Applying the actual endomorphism to the residual "
                        + "produces all five cyclic-origin equations. The proof then "
                        + "uses five explicitly supplied polynomial multipliers, of "
                        + "total degrees at most eight, whose weighted sum is mu(a) "
                        + "in characteristic nineteen. Integer expansion independently "
                        + "gives a difference divisible coefficientwise by nineteen. "
                        + "The Lean candidate expands this identity with ring_nf and "
                        + "reduces its coefficients with reduce_mod_char!.")),
                    Paragraph(Text("For sigma(x)=x^q this rules out every additional "
                        + "common root in the source's exactness conjecture, including "
                        + "the previously unresolved degree-fifteen difference case. "
                        + "The complete monic-gcd equality and the extension-degree "
                        + "classification are ordinary proofs in the associated dossier. "
                        + "They are not additional conclusions silently attributed "
                        + "to this formal declaration. No integer Wall-Sun-Sun prime "
                        + "is asserted to exist."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), xs);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, int n) => new Formula.Power(a, D(n));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula R(Formula a, Formula b, Formula c, Formula d) => C("residual", a, b, c, d);
    private static Formula Q(Formula a) => C("quintic", a);
    private static Formula ApplySigma(int n)
    {
        Formula x = V("theta");
        for (var i = 0; i < n; i++) { x = C("sigma", x); }
        return x;
    }
    private static Formula ResidualFormula()
    {
        var a = V("a"); var b = V("b"); var c = V("c"); var d = V("d");
        return Disp(All("a", V("K"), All("b", V("K"), All("c", V("K"), All("d", V("K"),
            Eqn(R(a,b,c,d), Sub(D(1), Mul(d, Sub(D(1), Mul(c, Sub(D(1), Mul(b, Sub(D(1), a)))))))))))));
    }
    private static Formula QuinticFormula() => Disp(All("a", V("K"), Eqn(Q(V("a")),
        Sub(Sub(Add(Add(Pow(V("a"),5), Mul(D(5),Pow(V("a"),3))),
            Mul(D(3),Pow(V("a"),2))), Mul(D(4),V("a"))), D(9)))));
    private static Formula ResultFormula()
    {
        var close = Eqn(ApplySigma(5),V("theta"));
        var root = Eqn(R(Sub(ApplySigma(1),V("theta")), Sub(ApplySigma(2),V("theta")),
            Sub(ApplySigma(3),V("theta")), Sub(ApplySigma(4),V("theta"))), D(0));
        var conclusion = Eqn(Q(Sub(ApplySigma(1),V("theta"))),D(0));
        return Disp(All("K", C("Type"), Implies(And(C("Field",V("K")), C("CharP",V("K"),D(19))),
            All("sigma",C("RingHom",V("K"),V("K")),All("theta",V("K"),
                Implies(And(close,root),conclusion))))));
    }
}
