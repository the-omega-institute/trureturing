using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class TebniA364822PowerOfTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.";
    private static LibraryNoteRef Source() => LibraryNoteRef.Create("D5/L/RecurrenceComposition/tebni2023a364822");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hyperbolic EGF coefficients have residue one at every power of two.",
        H("Tebni's A364822 congruence at powers of two"),
        Blocks(
            Paragraph(Text("The function D5.S1.Recurrence.Residue.TebniA364822.a is n! times "
                + "the nth ordinary coefficient of cosh(x)/(1-2 sinh(x)). The exponent m is "
                + "natural and includes zero; Int.ModEq uses the integer cast of 2^m. "
                + "The integer z is cast to Q in the coefficient equality.")),
            Node("claim", "The power-of-two conjecture", Seq(Call("claim"), Sp, Iff, Sp, Parenthesized(ClaimBody())),
                "OEIS A364822, Comments (unpaginated): \"For n = 2^m (m natural number), a(n) == 1 (mod n).\" At m=0 the modulus is one. At positive m the index is even.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("pow_two_dvd_choose_odd", "Odd-index dyadic binomial divisibility", OddBinomialBody(),
                "The adjacent binomial identity makes the product of k and choose(2^m,k) divisible by 2^m. Since odd k is coprime to every power of two, the binomial coefficient itself is divisible by 2^m. The exponent and index are arbitrary naturals.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("result", "Residue one at every power of two", ClaimBody(),
                "For odd k, 2^m divides the binomial coefficient choose(2^m,k), by the adjacent binomial identity and coprimality of k and 2^m. At a positive exponent, all nonzero sinh terms in the integer recurrence have odd k and therefore vanish modulo 2^m. The cosh term is one. The zero exponent has modulus one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source()),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("tebni364822-power-of-two-cong"), ResolutionKind.Proved))),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Residue/TebniA364822"))]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("tebni364822-dyadic-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, claim);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Named(name) : new Formula.Apply(Named(name), [.. args]);
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula OddBinomialBody()
    {
        var m = F.Id("m"); var k = F.Id("k");
        var index = new Formula.Power(D(2), m);
        return Seq(Forall, Sp, m, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            Forall, Sp, k, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            Parenthesized(Call("Odd", k)), Sp, Implies, Sp,
            Parenthesized(Seq(index, Sp, Mid, Sp,
                new Formula.Apply(Qualified("Nat", "choose"), [index, k]))));
    }
    private static Formula ClaimBody()
    {
        var m = F.Id("m"); var z = F.Id("z");
        var index = new Formula.Power(D(2), m);
        var coefficient = new Formula.Apply(Seq(Named("D5"), Dot, Named("S1"), Dot, Named("Recurrence"), Dot,
            Named("Residue"), Dot, Named("TebniA364822"), Dot, Named("a")), [index]);
        return Seq(Forall, Sp, m, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            Exists, Sp, z, Colon, Sp, Ints(), Comma, Sp,
            Parenthesized(Seq(Cast(z, Seq(Mathbb, Grp(F.Id("Q")))), Sp, Eq, Sp, coefficient)), Sp, Land, Sp,
            Parenthesized(new Formula.Apply(Qualified("Int", "ModEq"), [Cast(index, Ints()), z, D(1)])));
    }
}
