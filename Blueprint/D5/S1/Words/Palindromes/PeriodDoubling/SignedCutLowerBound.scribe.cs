using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class SignedCutLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/SignedCutLowerBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual period-doubling prefix requires at least the signed weight of its rounded half.", H("Signed-Weight Lower Bound for Period Doubling"), Blocks(
        Describe.Lean(DescribeId.Create("pd-signedcutlowerbound-palindromic-suffix-signed-bound"),
            DeclarationHandle.Create(Prefix + "palindromic_suffix_signed_bound"), H("A lower bound for the true prefix palindromic length"),
            StatementSource.FromAuthor(CutFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For an actual palindrome suffix from cut j to endpoint n, the signed binary weight of the rounded half of n is at most one more than the weight at j. The short-radius and long-radius cases use different dyadic estimates, and the even-palindrome case has length two. Strong induction along optimal suffix cuts gives the second clause for every prefix. Nat.sub is truncated natural subtraction, Nat.div is natural integer division, and cast denotes the natural-to-integer embedding."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);

    private static Formula Upd(Formula n) =>
        new Formula.Apply(new Formula.Subscript(V("u"), Seq(Mathrm, Grp(V("pd")))), [n]);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);


    private static Formula RoundedWeight(Formula n) => Call("signedWeight", Cast(DottedCall("Nat", "div", Add(n, D(1)), D(2)), Z()));
    private static Formula CutFormula()
    {
        var n = V("n"); var j = V("j");
        var window = Call("ofFn", Lam("i", Call("Fin", DottedCall("Nat", "sub", n, j)),
            Upd(Add(j, Call("val", V("i"))))));
        var cut = All("n", N(), All("j", N(), Imp(And(LtF(j, n), Call("Palindrome", window)),
            LeF(RoundedWeight(n), Add(RoundedWeight(j), D(1))))));
        var prefix = Call("ofFn", Lam("i", Call("Fin", n), Upd(Call("val", V("i")))));
        var lower = All("n", N(), LeF(RoundedWeight(n), Call("PL", prefix)));
        return Disp(And(cut, lower));
    }

}
