using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class EulerTwoPrimaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/EulerTwoPrimary.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary tangent coefficients have power-of-two divisors and secant coefficients are odd.", H("The two-primary Euler component"), Blocks(
            Paragraph(Text("All indices and powers are natural. Parity projections S and T of the ordinary rational exponential series satisfy S prime equals S times T and T prime equals one plus T squared. The product invariant of U and U at negative X is proved using the existing rational linear ODE uniqueness supplier. Lucas congruence supplies evenness of the odd binomial terms.")),
            Node("tangent_power", "The tangent power-of-two bound", Q("s",Dvd(Pow(D(2),V("s")),E(Add(Mul(D(2),V("s")),D(1))))),
                "Strong induction on s uses the tangent convolution; every odd binomial factor supplies the additional factor two. Zero is included.", DescribeRole.Theorem),
            Node("secant_odd", "Secant coefficients are odd", Q("s",Call("Odd",E(Mul(D(2),V("s"))))),
                "In the secant convolution, all tangent coefficients except E(1) vanish modulo two. The surviving factor is odd.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, Formula f, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("eulertwoprimary-" + name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(f)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string n) => F.Id(n);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Dvd(Formula x, Formula y) => Seq(x, Sp, Mid, Sp, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x,y);
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, P(body));
    private static Formula Q(string names, Formula body)
    {
        foreach (var n in names.Split(' ').Reverse()) body = All(n, Nat(), body);
        return body;
    }
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [..args]);
    private static Formula E(Formula n) => Call("E",n);

}
