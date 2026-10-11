using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class MBonacciMinimumGreedyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum complete Parikh cardinality implies a full periodic greedy expansion in actual m-bonacci weights.",
        H("Actual Weights and Full Greedy Necessity"),
        Blocks(
            Paragraph(Text(
                "Let m be at least five and let the alphabet be Fin m. The literal substitution phi "
                + "sends a below m minus one to the list [zero, a plus one], and the terminal letter "
                + "to [zero]. The actual infinite word is the unbounded limit of iterated images of zero. "
                + "The weight U(j) is the length of the literal list phi iterated j times on zero, "
                + "including U(0) equal to one. The complete Parikh image at length n is the range of "
                + "letter-count vectors of factors starting at every natural q, including zero.")),
            Paragraph(Text(
                "Put S(k) equal to one plus the sum of U(j) over j below k. Expanding an image of a "
                + "letter a gives S(k) when k is below m minus a, and otherwise the sum of the "
                + "preceding m minus a zero-image weights. In particular U(k) equals two to the k "
                + "for k below m, and otherwise the sum of its preceding m terms. This identifies "
                + "U(k) with the integer sequence dbonacci m (k plus two). The real values based on "
                + "inverse Perron powers are a different valuation.")),
            Paragraph(Text(
                "For T(s) equal to phi(s) followed by zero, the length of T iterated k times on the "
                + "empty list, plus one, is S(k). The image-add decomposition proves this using the "
                + "actual function iterate. The resulting recurrence is S(k) equal to U(k) for "
                + "k below m, and S(k) equal to U(k) plus S(k minus m) otherwise. The positive "
                + "weights are strictly increasing and satisfy k plus one at most U(k), so they "
                + "are unbounded. Moreover U(k) is at most S(k), and S(k) is less than U(k plus one).")),
            Paragraph(Text(
                "The top index for a positive natural n is the greatest j with U(j) at most n. "
                + "It is computed by the finite greatest-index search bounded by n; the inequality "
                + "j plus one at most U(j) makes that search exhaustive. The scanner with count "
                + "weights emits the quotient by U(count minus one), passes the remainder to "
                + "the next smaller weight, and ends only after U(0). A zero remainder therefore "
                + "still emits all subsequent zeros. fullGreedy(n) is this complete MSB-first "
                + "list, started at the top index. periodicDigits(k) is the length k plus one "
                + "list whose digit at position i is one exactly when i modulo m is zero.")),
            Describe.Lean(
                DescribeId.Create("minimal-abelian-complexity-greedy"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciMinimumGreedy.minimal_abelian_complexity_greedy"),
                H("Minimum complexity forces the full periodic greedy prefix"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The minimum-cardinality descent supplies a k for which n is the actual "
                        + "sentinel length S(k). Its upper and lower weight bounds identify k as "
                        + "the greatest fitting index. The quotient by U(k) is one. If k is below "
                        + "m its remainder is zero and all k trailing zeros are retained. Otherwise "
                        + "the remainder is S(k minus m). It is below U(k minus m plus one), "
                        + "so the next m minus one quotients are zero; the remaining scan is the "
                        + "same construction at k minus m. Induction gives the entire list.")),
                    Paragraph(Text(
                        "Thus the output is nonempty, has length k plus one and begins with one. "
                        + "It is a finite prefix of the infinite repetition of one followed by "
                        + "m minus one zeros. Every trailing zero and the last partial period is "
                        + "part of the output. The case n equal to one has k equal to zero and "
                        + "the single digit [one]. The argument assumes neither balance nor a "
                        + "palindrome property and never replaces the complete image by finitely "
                        + "many occurrence starts. The converse implication is separate."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var m = F.Id("m"); var n = F.Id("n"); var k = F.Id("k");
        var g = Call("fullGreedy", m, n);
        return All("m", N(), Imp(And(Leq(D(2), m), Leq(D(5), m)),
            All("n", N(), Imp(And(Leq(D(1), n), Eq(Call("ncard", Call("parikhImage", m, n)), m)),
                Ex("k", N(), And(Eq(n, Call("S", m, k)),
                    And(Eq(Call("topIndex", m, n), k),
                        And(Eq(g, Call("periodicDigits", m, k)),
                            And(Eq(Call("length", g), Add(k, D(1))),
                                Eq(Call("headoption", g), Call("some", D(1))))))))))));
    }
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Ex(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
}
