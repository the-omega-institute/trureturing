using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class HannaLaurentFirstMomentDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2025a391810");
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Bound => new Formula.Power(new Formula.Floor(
        new Formula.Fraction(new Formula.Binary(V("n"), FormulaBinaryOperator.Add, D(1)), D(2))), D(2));
    private static Formula Moment(Formula coefficient) => Seq(
        Sum, Underscore, new Formula.LatexGroup([
            Seq(D(0), Sp, Leq, Sp, V("k"), Sp, Leq, Sp, Bound)]), Sp,
        Mul(V("k"), coefficient));

    public DocumentDefinition Create()
    {
        var integerMoment = Moment(Call("rowEntry", V("n"), V("k")));
        var laurentMoment = Moment(Call("coeff", Call("series", V("n")), Seq(Minus, V("k"))));
        var statement = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), Seq(Mathbb, new Formula.LatexGroup([V("N")])),
            new Formula.Logic(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, V("n")),
                FormulaLogicOperator.Implies,
                new Formula.Logic(Eqn(integerMoment, D(1)), FormulaLogicOperator.And,
                    Eqn(laurentMoment, D(1)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The first weighted moment of every positive A391810 Laurent row is one.",
            H("The first moment of Hanna's Laurent rows"), Blocks(
                Paragraph(Text("Formula (3) in Paul D. Hanna's OEIS A391810, revision 39, states: (3) Sum_{k=0..floor((n+1)/2)^2} k * T(n,k) = 1 for n >= 1 (conjecture). This is the weighted assertion; the zero row sum in formula (2) is a separate assertion. The shared library note supplies the source locator and Laurent-series convention; its claim quotation concerns formula (2).")),
                Paragraph(Text("The original series is the formal expansion at zero of Sum_{j in Z} x^j*(1-x^j)^(n+j), with all integer outer indices and Laurent-field inverses for negative integer powers. T(n,k) is its signed coefficient of x^(-k), including k=0. The imported coefficient bridge identifies it with the integer rowEntry(n,k). The imported row bound is exactly floor((n+1)/2)^2 and the final index is included.")),
                Describe.Lean(DescribeId.Create("a391810-first-moment-result"),
                    DeclarationHandle.Create("D5/S3/ArithSums/HannaLaurentFirstMoment.result"),
                    H("The integer and literal Laurent weighted sums"),
                    StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(Source),
                    Blocks(
                        Paragraph(Text("The first equality is in the integers; the second is in the rationals, using the literal Laurent coefficients. Both hold for every natural n with 0<n. The coefficient bridge retains the constant term and every nonpositive coefficient, while the existing degree bound identifies the displayed finite sum with the full row moment.")),
                        Paragraph(Text("Differentiate only the finite inverse-variable rowPolynomial. For n=1 its derivative is one. For n>=2, evaluation at one annihilates every differentiated summand except the last two, whose values are n and -(n-1). Their sum is one. The polynomial derivative coefficient identity gives the integer weighted sum, and the exact coefficient bridge transfers it to the original bilateral series. No evaluation of the bilateral series at one is used.")),
                        Paragraph(Text("This is an application of the existing coefficient and support theorems and polynomial differentiation. Its mathematical scope is the published formula (3) with its original range and arithmetic. Global priority and global prior solvedness remain outside the theorem."))),
                    DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(ProblemSlugRef.Create(
                        "oeis-a391810-laurent-first-moment"), ResolutionKind.Proved)))));
    }
}
