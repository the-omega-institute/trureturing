using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class SelfPowerQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/SelfPowerQuotient.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/englander2020a081215");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every natural index n, the self-power numerator is divisible by (n+1)^2.", H("The exact self-power quotient"), Blocks(
            Describe.Lean(DescribeId.Create("self-power-selfpowerquotient-numerator"),
                DeclarationHandle.Create(Prefix + "numerator"), H("The source numerator"),
                StatementSource.FromAuthor(Disp(NumeratorFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Englander, definition on physical page 1: the natural index is cast into the integers before taking the power. The sign exponent is natural."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("self-power-selfpowerquotient-a"),
                DeclarationHandle.Create(Prefix + "a"), H("The shared sequence"),
                StatementSource.FromAuthor(Disp(SequenceFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The quotient uses integer Euclidean division. The exact quotient identity below proves that no truncation affects this value at any natural index, including zero. All three modules use this same definition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("self-power-selfpowerquotient-tail"),
                DeclarationHandle.Create(Prefix + "tail"), H("An integrated geometric sum"),
                StatementSource.FromAuthor(Disp(TailFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The auxiliary integer polynomial is the sum of the geometric sums with lengths from zero through j minus one; empty sums are zero. This is a proof device, not an additional source sequence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("self-power-selfpowerquotient-quotient-tail"),
                DeclarationHandle.Create(Prefix + "quotient_tail"), H("A division-free formula"),
                StatementSource.FromAuthor(Disp(QuotientFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Multiplying each inner geometric sum by y minus one applies Mathlib geom_sum_mul directly. Summing gives T(j,y)*(y-1)=S(j,y)-j and then T(j,y)*(y-1)^2=y^j-1-j*(y-1). Substituting j=n+1 and y=-n and using the square of the sign gives the displayed integer formula."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("self-power-selfpowerquotient-exact-quotient"),
                DeclarationHandle.Create(Prefix + "exact_quotient"), H("Exact integrality"),
                StatementSource.FromAuthor(Disp(ExactFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n, the positive nonzero denominator times the integer quotient equals the original numerator. Thus the original rational quotient is this integer, rather than an unverified truncated value. Natural indices above two are exactly the integer indices in XIV; positive k and n greater than k in XVII likewise imply a positive natural index."))), DescribeRole.Theorem))));
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [..args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Cast(Formula a, Formula t) => Par(Seq(a, Colon, Sp, t));
    private static Formula Den(Formula n) => Pow(Seq(Cast(n, Int()), Plus, D(1)), D(2));
    private static Formula Num(Formula n) => Seq(Pow(Cast(n, Int()), Seq(n, Plus, D(1))), Plus, Pow(Seq(Minus, D(1)), n));
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula SumRange(string i, Formula n, Formula body) => Seq(Sum, Underscore, Grp(V(i), F.Lt, n), Sp, body);

    private static Formula NumeratorFormula() => All("n", Nat(), Eqn(Call("numerator", V("n")), Num(V("n"))));
    private static Formula SequenceFormula() => All("n", Nat(), Eqn(Call("a", V("n")), Div(Call("numerator", V("n")), Den(V("n")))));
    private static Formula TailFormula() => All("j", Nat(), All("y", Int(), Eqn(Call("tail", V("j"), V("y")), SumRange("i", V("j"), SumRange("r", V("i"), Pow(V("y"), V("r")))))));

    private static Formula QuotientFormula() => All("n", Nat(), Eqn(Call("a", V("n")), Seq(Pow(Seq(Minus, D(1)), V("n")), Star,
        Par(Seq(D(1), Minus, Call("tail", Seq(V("n"), Plus, D(1)), Seq(Minus, Cast(V("n"), Int()))))))));
    private static Formula ExactFormula() => All("n", Nat(), Eqn(Seq(Den(V("n")), Star, Call("a", V("n"))), Call("numerator", V("n"))));
}
