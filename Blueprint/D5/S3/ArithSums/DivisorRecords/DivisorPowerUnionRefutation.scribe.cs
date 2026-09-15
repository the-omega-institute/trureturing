using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums.DivisorRecords;

internal sealed class DivisorPowerUnionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/switkay2026divisorpowerunion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A divisor-power record at exponent minus four refutes "
            + "the highly-composite or deeply-composite union in OEIS A396596.",
        H("The A396596 Divisor-Power Union Refutation"),
        Blocks(
            Paragraph(Text(
                "For N = 32125373280, exponent -4 yields a strict divisor-power record. "
                    + "Neither endpoint class contains N. "
                    + "The formulas preserve the preregistered natural and real domains.")),
            Describe.Lean(
                DescribeId.Create("a396596-divisor-power-sum"),
                DeclarationHandle.Create(Prefix + "DivisorPowerSum"),
                H("Real powers of all positive divisors"),
                StatementSource.FromAuthor(SumFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For positive natural n, divisors(n) is the finite set of all "
                        + "positive natural divisors, including 1 and n. Each divisor "
                        + "is cast to the reals before taking its real power; the sum "
                        + "is real-valued. Lean's Nat.divisors at zero is empty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a396596-strict-divisor-power-record"),
                DeclarationHandle.Create(Prefix + "StrictDivisorPowerRecord"),
                H("Strict records against every positive predecessor"),
                StatementSource.FromAuthor(RecordFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "One fixed real exponent must beat every smaller positive natural "
                        + "simultaneously. The candidate must be positive; for n = 1 "
                        + "the predecessor condition is empty. At exponent zero every "
                        + "divisor contributes one, so a record is highly composite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a396596-divisor-power-union-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The exact universal union conjecture"),
                StatementSource.FromAuthor(Disp(IffFormula(F.Id("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Switkay's selected sentence is: We conjecture that the present "
                        + "sequence can be constructed simply as a union of highly "
                        + "composite numbers and deeply composite numbers. The latter "
                        + "uses A095848's all-sufficiently-low-power definition with "
                        + "real exponents: one negative real threshold, and every real "
                        + "exponent below it. The threshold may depend on n. No "
                        + "lexicographic equivalence is assumed. The complete iff was "
                        + "preregistered in public issue 8081 on September 15, 2026, "
                        + "at 11:22:40 UTC, before numerical or Lean probes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a396596-divisor-power-union-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Negation of the complete union claim"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The result type is closed Not claim. The proof takes "
                            + "N = 32125373280 and exponent -4. Its record proof "
                            + "covers every positive predecessor: nonmultiples of "
                            + "L = 232792560 = lcm(1,...,19) and all smaller multiples.")),
                    Paragraph(Text(
                        "A nonmultiple misses d and 2d for some 1 <= d <= 19. "
                            + "A local telescoping reciprocal-fourth-power estimate "
                            + "bounds every finite positive-divisor sum; inserting "
                            + "those two missing terms puts the nonmultiple below N. "
                            + "The multiples are kL for 1 <= k <= 137. The exact "
                            + "137-row certificate checks prime bases, pairwise "
                            + "coprimality, factorization and the cross-multiplied "
                            + "sigma inequality. Local induction proves certificate "
                            + "soundness and reciprocal divisor pairing connects "
                            + "sigma_4(n)/n^4 to the original real divisor sum.")),
                    Paragraph(Text(
                        "At zero, the smaller predecessor 27935107200 ties N's "
                            + "3072 divisors, excluding a strict record. For every "
                            + "real x <= -1000, predecessor 26771144400 wins: "
                            + "N-only divisors are at least 27, whereas 25 divides "
                            + "the predecessor but not N, and N*27^x < 25^x. "
                            + "For arbitrary real B < 0, min(B,-1000) therefore "
                            + "defeats the eventual-record alternative.")),
                    Paragraph(Text(
                        "Empirical candidate discovery is separate from the exact "
                            + "full-domain argument. No floating-point proof or "
                            + "prime-signature completeness assumption is used. "
                            + "There is no minimality claim or claim that all "
                            + "superabundant numbers fall outside either class.")),
                    Paragraph(Text(
                        "Semantic assessment: proof_shape content; computational "
                            + "kind certified-instance, also bounded-enumeration; "
                            + "utility refutes the displayed claim; admission_basis "
                            + "open-problem-resolution; escape_witness none. The "
                            + "closed refutation preserves the exact original claim. "
                            + "No direct frozen project dependency or atom coverage "
                            + "is asserted. The source note and Problems dossier "
                            + "retain the bounded search and attribution limits."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396596-divisor-power-union"),
                    ResolutionKind.Refuted)))));

    private static Formula SumFormula()
    {
        var n = F.Id("n");
        var x = F.Id("x");
        var d = F.Id("d");
        var sum = Seq(
            new Formula.Subscript(Sum, Seq(d, Sp, InMacro, Sp, Call("divisors", n))),
            Sp, new Formula.Power(Parenthesized(Seq(d, Sp, Colon, Sp, Reals())), x));
        return Disp(ForAll("n", Naturals(), ForAll("x", Reals(),
            Equal(Call("DivisorPowerSum", n, x), sum))));
    }

    private static Formula RecordFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var x = F.Id("x");
        var predecessors = ForAll("m", Naturals(),
            Implication(Less(D(0), m), Implication(Less(m, n),
                Less(Call("DivisorPowerSum", m, x), Call("DivisorPowerSum", n, x)))));
        return Disp(ForAll("n", Naturals(), ForAll("x", Reals(),
            IffFormula(Record(n, x), And(Less(D(0), n), predecessors)))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var x = F.Id("x");
        var b = F.Id("B");
        var recordSomewhere = ExistsReal("x", And(AtMost(x, D(0)), Record(n, x)));
        var deep = ExistsReal("B", And(Less(b, D(0)),
            ForAll("x", Reals(), Implication(AtMost(x, b), Record(n, x)))));
        return ForAll("n", Naturals(), Implication(Less(D(0), n),
            IffFormula(recordSomewhere, Or(Record(n, D(0)), deep))));
    }

    private static Formula Record(Formula n, Formula x) =>
        Call("StrictDivisorPowerRecord", n, x);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula ExistsReal(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Reals(), body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));

    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
