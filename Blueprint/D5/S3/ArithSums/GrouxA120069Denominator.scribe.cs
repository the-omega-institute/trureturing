using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class GrouxA120069DenominatorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2010a120069");
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Term(Formula k) => new Formula.Fraction(
        Call("catalan", k), new Formula.Power(D(4), Subtract(k, D(1))));
    private static Formula PartialSum(Formula n) => Seq(F.Sum, Underscore,
        Grp(Seq(D(1), Sp, Leq, Sp, V("k"), Sp, Leq, Sp, n)), Sp, Term(V("k")));
    private static Formula Positive(Formula n) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n);
    private static Formula All(Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
        Seq(Mathbb, Grp(V("N"))), new Formula.Logic(Positive(V("n")),
            FormulaLogicOperator.Implies, body));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original positive-index Catalan partial sum and its final summand have equal reduced denominators.",
        H("Groux's A120069 denominator equality"), Blocks(
            Paragraph(Text("Here catalan(k) is Mathlib's ordinary natural Catalan number, "
                + "characterized by (k+1)catalan(k)=choose(2k,k). Each summand is "
                + "cast to the rationals before division. The finite interval includes "
                + "both one and n; subtraction in the exponent is natural subtraction. "
                + "On this interval k is positive, so k-1 is the source exponent. "
                + "den is Rat.den, the positive reduced denominator, including den(0)=1.")),
            Describe.Lean(DescribeId.Create("groux-a120069-result"),
                DeclarationHandle.Create("D5/S3/ArithSums/GrouxA120069Denominator.result"),
                H("The complete positive-index equality"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    Call("den", PartialSum(V("n"))), Call("den", Term(V("n"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every positive integer source index corresponds "
                    + "uniquely to a natural n with 0<n. There is no upper bound, "
                    + "recurrence-only replacement, convergence assumption or finite-case "
                    + "surrogate. This is the Groux Roland formula in A120069; the "
                    + "separate A283208 conjecture is outside its scope."))),
                DescribeRole.Theorem),
            Paragraph(Text("The proof uses the following Catalan form of Pieter Mostert's "
                + "finite-sum identity from A119951. It is an attributed supplier, "
                + "proved here by induction from the pinned Catalan/central-binomial "
                + "relations; it is retained only as a private consumed helper.")),
            new DocumentBlock.DisplayFormula(Disp(All(Equal(PartialSum(V("n")),
                Subtract(D(4), Multiply(Add(Multiply(D(2), V("n")), D(1)), Term(V("n")))))))),
            Paragraph(Text("Put q=catalan(n)/4^(n-1). Its reduced denominator divides "
                + "4^(n-1). Since 2n+1 is odd, it is coprime to that denominator. "
                + "Mathlib's rational multiplication denominator formula therefore "
                + "gives den((2n+1)q)=den(q). Subtracting from the integer four "
                + "preserves the denominator, proving the exact equality. "
                + "The initial index n=1 is included. The argument uses no "
                + "binary valuation formula for Catalan numbers.")))));
}
