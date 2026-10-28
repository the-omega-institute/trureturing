using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PisanoLegendre;

internal sealed class AndoyoPrimeFiberRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/andoyo2026pisanolegendrecollision");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact odd-prime fiber of the attained balance -1 for seeds (0,3) is {3}.",
        H("An isolated Pisano-Legendre balance refutes Question 5.2"),
        Blocks(
            Describe.Lean(DescribeId.Create("exact-prime-fiber"),
                DeclarationHandle.Create(Prefix + "fiber"), H("Exact odd-prime fibers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For integer seeds a,b and integer k, fiber(a,b,k) "
                    + "contains exactly natural primes p different from two for which K(p,a,b)=k. "
                    + "The imported recurrence F starts at index zero. Its least positive scalar "
                    + "period pi determines the index range 0 through pi-1, with multiplicity. "
                    + "The three Legendre counts partition this range, and K is the integer "
                    + "count at 1 minus the counts at -1 and 0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-question"),
                DeclarationHandle.Create(Prefix + "claim"), H("The original universal assertion"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Question 5.2 asks: Suppose that a and b are integers "
                    + "with (a,b) different from (0,0). For every k in chi(a,b), is the "
                    + "cardinality of the corresponding prime fiber aleph-zero? Here chi is "
                    + "the complete set of attained integer balances over odd primes. An infinite "
                    + "subset of the natural numbers is countably infinite. The source imposes "
                    + "no positivity, coprimality, individual nonzero-seed or nonzero-modulo-p "
                    + "restriction; primes dividing both seeds remain in scope."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("question-refuted"),
                DeclarationHandle.Create(Prefix + "result"), H("The universal assertion is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Seq(Open, ClaimFormula(), Close)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take a=0, b=3 and k=-1. Modulo three the recurrence is "
                        + "identically zero. Its least positive scalar period is one, so the "
                        + "counts are N(1)=N(-1)=0 and N(0)=1. Thus K=-1 is attained at three.")),
                    Paragraph(Text("For arbitrary integer seeds, the recurrence satisfies "
                        + "F(n+1)^2-F(n)F(n+1)-F(n)^2=(-1)^n(b^2-ab-a^2). Finite "
                        + "invertible pair dynamics supplies a positive scalar period. At a "
                        + "period return the left-hand norm returns to its initial value. "
                        + "At an odd prime with nonzero initial norm, cancellation forces the "
                        + "least period to be even. For (0,3) that norm is nine, nonzero at "
                        + "every prime other than three.")),
                    Paragraph(Text("The Legendre trichotomy gives pi=N(1)+N(-1)+N(0), hence "
                        + "K=2N(1)-pi. Every odd prime other than three therefore has even K "
                        + "and cannot realize -1. Combined with attainment, the exact fiber is "
                        + "{3}; its finiteness contradicts the original universal assertion. "
                        + "This is a symbolic obstruction over all primes, with no sampling bound.")),
                    Paragraph(Text("Definitions 2.6 and 2.7, the odd-prime convention in "
                        + "Section 4, the definition of the prime fiber there, and Section 5 "
                        + "Question 5.2 supply the source interpretation. The argument does not "
                        + "settle infinitude for coprime seeds or assert worldwide priority."))),
                DescribeRole.Theorem)))));

    private static Formula ClaimFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var k = F.Id("k");
        var nonzero = new Formula.Relation(Seq(Open, a, Comma, b, Close),
            FormulaRelationOperator.NotEqual, Seq(Open, D(0), Comma, D(0), Close));
        var attained = new Formula.Relation(k, FormulaRelationOperator.MemberOf,
            Seq(F.Id("chi"), Open, a, Comma, b, Close));
        var infinite = Seq(F.Id("Set"), Dot, F.Id("Infinite"), Sp,
            Open, F.Id("fiber"), Open, a, Comma, b, Comma, k, Close, Close);
        return All("a", new Formula.Integers(), All("b", new Formula.Integers(),
            new Formula.Logic(nonzero, FormulaLogicOperator.Implies,
                All("k", new Formula.Integers(),
                    new Formula.Logic(attained, FormulaLogicOperator.Implies, infinite)))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
