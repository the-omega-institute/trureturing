using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaA377106ParityReversionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaA377106ParityReversion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2024a377106");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every normalized rational solution of Hanna's cubic equation has integer coefficients odd exactly at powers of two.", H("Dyadic parity for Hanna's cubic series"), Blocks(
            Paragraph(Text("PowerSeries.subst takes the inner argument first. The series variable A has rational coefficients. Each coefficient at a positive natural index is shown equal to an integer m; Odd applies to that integer. The integer lift comes from the prime-exponent construction with p=3 and c=9. Reducing it modulo two and using uniqueness identifies it with the existing powerTwoSeries.")),
            Node("IsGF", "The source generating function", IsGFFormula(),
                "OEIS A377106, NAME (unpaginated): \"G.f. A(x) satisfies A(x)^3 = A( x^3 + 9*x*A(x)^3 ), with A(0)=0, A'(0)=1.\" The coefficient ring is rational and the two normalization coefficients are zero and one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The parity conjecture", Disp(Iffn(Named("claim"), ClaimBody())),
                "OEIS A377106, COMMENTS (unpaginated): \"Conjecture: a(n) is odd iff n = 2^k for some k >= 0.\" The offset is one. The proposition asserts existence and the integer parity assertion for every solution and every index at least one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The parity conjecture holds", Disp(ClaimBody()),
                "Existence follows from integer lifting. Uniqueness over the rationals identifies any solution with that lift; uniqueness over ZMod(2) identifies its reduction with the power-of-two series.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("hanna2024a377106-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a377106-hanna-parity-reversion"), ResolutionKind.Proved) : null);

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
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));




    private static Formula IsGFFormula() => Disp(All("A", Series(Q()),
        Iffn(Call("IsGF", V("A")), And(Eqn(Call("constantCoeff", V("A")), D(0)), And(Eqn(Call("coeff", D(1), V("A")), D(1)), Eqn(Pow(V("A"), D(3)),
            App(Qualified("PowerSeries", "subst"), Add(Pow(V("X"), D(3)),
                Mul(Mul(D(9), V("X")), Pow(V("A"), D(3)))), V("A"))))))));
    private static Formula ClaimBody() => And(Ex("A", Series(Q()), Call("IsGF", V("A"))),
        All("A", Series(Q()), Imp(Call("IsGF", V("A")), All("n", N(), Imp(Rel(D(1), Le, V("n")),
            Ex("m", Z(), And(Eqn(Call("coeff", V("n"), V("A")), Cast(V("m"), Q())),
                Iffn(Call("Odd", V("m")), Ex("k", N(), Eqn(V("n"), Pow(D(2), V("k"))))))))))));
}
