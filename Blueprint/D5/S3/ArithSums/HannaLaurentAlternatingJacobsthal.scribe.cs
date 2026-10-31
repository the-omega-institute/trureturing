using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class HannaLaurentAlternatingJacobsthalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/HannaLaurentAlternatingJacobsthal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2025a391810");
    private static readonly LibraryNoteRef JacobsthalSource =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/oeis2026a001045");
    private static Formula N => Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Negative(Formula a) => Seq(Minus, a);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), N, body);
    private static Formula Sum(Formula upper, Formula body) => Seq(
        FormulaDsl.Sum, Underscore, new Formula.LatexGroup([
            Seq(D(0), Sp, Leq, Sp, V("k"), Sp, Lt, Sp, upper)]), Sp, body);

    public DocumentDefinition Create()
    {
        var n = V("n");
        var k = V("k");
        var j = Call("jacobsthal", n);
        var bound = Pow(new Formula.Floor(new Formula.Fraction(Add(n, D(1)), D(2))), D(2));
        var entry = Call("rowEntry", n, k);
        var coeff = Call("coeff", Call("series", n), Negative(k));
        var rounded = Call("round", new Formula.Fraction(Pow(D(2), n), D(3)));
        var alternatingSign = Negative(Pow(Seq(Open, Negative(D(1)), Close), k));
        var upper = Add(bound, D(1));
        var full = All("n", Imp(new Formula.Relation(D(1),
            FormulaRelationOperator.LessThanOrEqual, n),
            And(Eqn(Sum(upper, Mul(alternatingSign, entry)), Mul(D(2), rounded)),
            And(Eqn(Mul(D(2), rounded), Mul(D(2), j)),
            And(Eqn(Sum(upper, Mul(alternatingSign, coeff)), Mul(D(2), rounded)),
            And(All("k", Eqn(coeff, Call("rationalCast", entry))),
                All("k", Imp(new Formula.Relation(bound,
                    FormulaRelationOperator.LessThan, k), Eqn(coeff, D(0))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "For every positive row, the signed alternating sum of the original bilateral Laurent coefficients is twice round(2^n/3), and hence twice the offset-zero Jacobsthal number.",
            H("A391810: alternating Laurent rows and Jacobsthal numbers"),
            Blocks(
                Describe.Lean(DescribeId.Create("a391810-f5-jacobsthal"),
                    DeclarationHandle.Create(Prefix + "jacobsthal"),
                    H("The offset-zero Jacobsthal recurrence"),
                    StatementSource.FromAuthor(Disp(And(
                        Eqn(Call("jacobsthal", D(0)), D(0)),
                        And(Eqn(Call("jacobsthal", D(1)), D(1)),
                            All("n", Eqn(Call("jacobsthal", Add(n, D(2))),
                                Add(Call("jacobsthal", Add(n, D(1))), Mul(D(2), j)))))))),
                    AssessedProvenance.FromLiterature(JacobsthalSource),
                    Blocks(Paragraph(Text(
                        "This is A001045 with index zero included, valued in the integers. Two-step induction gives 3 J(n)=2^n-(-1)^n. Its parity term is always 1 or -1, placing 2^n/3 in the nearest-integer interval [J(n)-1/2,J(n)+1/2). The root-namespace round operation uses ties toward positive infinity. These familiar Jacobsthal identities supply the arithmetic interpretation, without a separate novelty claim."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("a391810-f5-full-formula-five"),
                    DeclarationHandle.Create(Prefix + "full_formula_five"),
                    H("The full alternating, rounding and Jacobsthal formula"),
                    StatementSource.FromAuthor(Disp(full)),
                    AssessedProvenance.FromRepo(Source),
                    Blocks(
                        Paragraph(Text(
                            "The imported HannaLaurentRowSums series is the formal expansion at zero of the sum over every integer outer index j of x^j(1-x^j)^(n+j). Negative integer powers use Laurent-field inverses. Its coefficient at -k is the rational cast of the signed integer rowEntry(n,k). Natural-number division gives the published floor bound; the finite range includes k=0 and the upper endpoint.")),
                        Paragraph(Text(
                            "Write P_n(y)=-1+sum from j=1 to n of y^j(1-y^j)^(n-j), with y the inverse Laurent variable. Only this finite polynomial is evaluated at -1. Shifting its finite index by two proves P_(n+2)(-1)=P_n(-1)-2^(n+1) for n>0. A positive-index two-step induction, with rows one and two checked separately, combines this identity with J(n+2)=J(n)+2^n to obtain P_n(-1)=-2 J(n). The imported degree bound and polynomial coefficient evaluation identify the negative of this value with the complete alternating coefficient sum.")),
                        Paragraph(Text(
                            "The displayed five clauses retain both equalities of formula (5), the rational original-series equality, the coefficient identification for every natural k, and vanishing past the inclusive bound. Casting the integer round/Jacobsthal equality yields the rational-series/Jacobsthal equality as well. Neither the bilateral series nor its summands are evaluated at 1 or -1. At n=0 the finite polynomial has value -1, whereas J(0)=0; the alternating-row theorem therefore retains precisely the source range n>=1. No global literature-priority or other A391810 conjecture is asserted."))),
                    DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(
                        ProblemSlugRef.Create("oeis-a391810-alternating-jacobsthal"),
                        ResolutionKind.Proved)))));
    }
}
