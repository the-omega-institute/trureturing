using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class SomosPrimeIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/SomosPrimeIntegrality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2004a091190");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized rational series of the Somos family is integral exactly for prime exponents.", H("Prime exponents characterize Somos integrality"), Blocks(
            Paragraph(Text("PowerSeries.subst takes the inner series first. The geometric series B(x)=x/(1-p*x) is written by its coefficients: coefficient zero is zero and coefficient n>0 is p to the power n-1. Natural subtraction in the exponent is truncated subtraction. Normalization A(0)=1 comes from the offset-zero entries. The proof rewrites the geometric denominator identity, lifts coefficients by Frobenius for prime p, and for composite p obtains a contradiction modulo its least prime factor.")),
            Node("IsGF", "The source functional equation", IsGFFormula(),
                "OEIS A091190 and A091200, COMMENTS (unpaginated): \"More generally, given A(x) satisfies x*A(x)^p = B(x*A(x^p)) where B(x) = x/(1-p*x), then it appears that A(x) is an integer series only when p is prime. This is a special case of sequences with g.f.s that satisfy the more general functional equation x*A(x)^m = B(x*A(x^m)) studied by Michael Somos\". The formula uses the displayed coefficient expression for B and rational coefficients for A.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The integrality conjecture", Disp(Iffn(Named("claim"), ClaimBody())),
                "OEIS A091190 and A091200, COMMENTS (unpaginated): \"More generally, given A(x) satisfies x*A(x)^p = B(x*A(x^p)) where B(x) = x/(1-p*x), then it appears that A(x) is an integer series only when p is prime.\" For each exponent at least two, the proposition asserts a solution and both directions of integrality versus primality. Integer coefficients mean that every rational coefficient equals an integer cast.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Integrality holds exactly at prime exponents", Disp(ClaimBody()),
                "A triangular coefficient construction gives rational existence for every exponent at least two and integer existence for prime exponents. For a composite exponent p, choose its least prime factor q. Below degree p the residual equation implies (n+1) times coefficient n+1 equals (1+pn) times coefficient n. Integral coefficients would therefore give q! times coefficient q equal to one modulo q, contradicting divisibility of q! by q.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("hanna2004a091190-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Rel(Formula a, Formula relation, Formula b) => Seq(a, Sp, relation, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Iffn(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Iff, Sp, Parenthesized(b));

    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));





    private static Formula GeometricBody() => Call("mk", Parenthesized(Seq(V("n"), Colon, Sp, N(), Sp, Mapsto, Sp,
        Named("if"), Sp, Parenthesized(Eqn(V("n"), D(0))), Sp, Named("then"), Sp, D(0), Sp, Named("else"), Sp,
        Pow(Cast(V("p"), Q()), Parenthesized(Sub(V("n"), D(1)))))));
    private static Formula IsGFFormula() => Disp(All("p", N(), All("A", Series(Q()),
        Iffn(Call("IsGF", V("p"), V("A")), And(Eqn(Call("constantCoeff", V("A")), D(1)),
            Eqn(Mul(V("X"), Pow(V("A"), V("p"))), App(Qualified("PowerSeries", "subst"),
                Mul(V("X"), App(Qualified("PowerSeries", "subst"), Pow(Cast(V("X"), Series(Q())), V("p")), V("A"))),
                GeometricBody())))))));
    private static Formula ClaimBody() => All("p", N(), Imp(Rel(D(2), Le, V("p")),
        And(Ex("A", Series(Q()), Call("IsGF", V("p"), V("A"))), All("A", Series(Q()),
            Imp(Call("IsGF", V("p"), V("A")), Iffn(All("n", N(), Ex("m", Z(),
                Eqn(Call("coeff", V("n"), V("A")), Cast(V("m"), Q())))), App(Qualified("Nat", "Prime"), V("p"))))))));
}
