using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class DeeplyCompositeLcmRankDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/DeeplyCompositeLcmRank.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deeply composite numbers contain the lcm prefix forced by their square-root rank.",
        H("The Square-Root-Rank LCM Law for Deeply Composite Numbers"),
        Blocks(
            Definition(
                "deeply-composite-rank",
                "rank",
                "Rank counts deeply composite numbers not exceeding n",
                StatementSource.FromAuthor(Disp(RankFormula())),
                "The rank of n counts the deeply composite integers not exceeding n. "
                    + "In displayed formulas, filter(S,P) denotes the elements of the "
                    + "finite set S satisfying P.",
                AssessedProvenance.FromRepo()),
            Theorem(
                "rank-source-count",
                "rank_eq_card_filter_le",
                "Rank counts deeply composite integers through n",
                StatementSource.FromAuthor(Disp(RankEqCardFilterLeFormula())),
                "Unfolding the definition, rank(n) is the number of deeply composite "
                    + "integers in the initial segment from zero through n. Every deeply "
                    + "composite integer is positive, so this is also the number in the "
                    + "closed interval from one through n.",
                AssessedProvenance.FromRepo()),
            Theorem(
                "rank-positive-interval-count",
                "rank_eq_card_filter_Icc",
                "Rank equals the positive-interval count through n",
                StatementSource.FromAuthor(Disp(RankEqCardFilterIccFormula())),
                "This theorem restates the rank count on the closed interval from one "
                    + "through n. Deeply composite integers are positive, so filtering "
                    + "that interval counts the same terms.",
                AssessedProvenance.FromRepo()),
            Definition(
                "deeply-composite-enumeration",
                "a",
                "The zero-indexed enumeration of deeply composite numbers",
                StatementSource.FromAuthor(Disp(EnumerationFormula())),
                "The sequence a(r) is Nat.nth applied to DC, so r starts at zero. "
                    + "It supplies the sequence-level representation corresponding to OEIS "
                    + "A095848 (Switkay, comments 2023 and 2025).",
                AssessedProvenance.FromRepo()),
            Definition(
                "lcm-prefix",
                "L",
                "The least common multiple prefix",
                StatementSource.FromAuthor(Disp(LFormula())),
                "L(k) is Nat.lcmUpto(k), the least common multiple of the positive "
                    + "integers through k, corresponding to OEIS A003418. The abbreviation "
                    + "keeps these lcm prefixes explicit in later divisibility arguments.",
                AssessedProvenance.FromRepo()),
            Definition(
                "records-below-lcm-prefix",
                "recordsBelowL",
                "Deeply composite records below an lcm prefix",
                StatementSource.FromAuthor(Disp(RecordsBelowFormula())),
                "recordsBelowL(k) filters the half-open interval from one to L(k) by the "
                    + "condition DC, retaining exactly the deeply composite natural numbers.",
                AssessedProvenance.FromRepo()),
            Definition(
                "successive-lcm-record-band",
                "recordBand",
                "Deeply composite records in one lcm band",
                StatementSource.FromAuthor(Disp(RecordBandFormula())),
                "recordBand(k) filters the half-open interval from L(k) to L(k+1) by DC.",
                AssessedProvenance.FromRepo()),
            Theorem(
                "lcm-prefix-growth-bound",
                "L_succ_le_mul",
                "The next lcm prefix is bounded by endpoint multiplication",
                StatementSource.FromAuthor(Disp(LSuccLeMulFormula())),
                "The bound follows by expanding the next lcm prefix and using that a least "
                    + "common multiple divides the corresponding product.",
                AssessedProvenance.FromRepo()),
            Theorem(
                "prefix-locking",
                "prefix_locking",
                "Every reached lcm prefix divides a deeply composite number",
                StatementSource.FromAuthor(Disp(PrefixLockingFormula())),
                "If n is deeply composite and L(j) <= n, then L(j) divides n. Otherwise "
                    + "the first divisor "
                    + "through j missing from n makes the smaller number L(j) precede n, "
                    + "contradicting the record condition.",
                AssessedProvenance.FromRepo()),
            Theorem(
                "counting-bound",
                "counting_bound",
                "Few deeply composite records lie below an lcm prefix",
                StatementSource.FromAuthor(Disp(CountingBoundFormula())),
                "Below L(k), at most NatDiv(k*(k-1),2) deeply composite numbers occur. "
                    + "Here NatDiv is natural-number Euclidean division, not rational "
                    + "division. The proof partitions records into successive lcm bands and "
                    + "injects the k-th band into the positive integers below k+1. Summing "
                    + "the band bounds gives the stated triangular bound.",
                AssessedProvenance.FromRepo()),
            Theorem(
                "positive-rank",
                "rank_pos",
                "A deeply composite number has positive rank",
                StatementSource.FromAuthor(Disp(RankPositiveFormula())),
                "A deeply composite n belongs to its own filtered closed interval, so the "
                    + "cardinality defining rank(n) is positive.",
                AssessedProvenance.FromRepo()),
            Theorem(
                "deeply-composite-lcm-square-root-rank",
                "deeply_composite_lcm_sqrt_rank",
                "The square-root-rank lcm divides every deeply composite number",
                StatementSource.FromAuthor(Disp(MainFormula())),
                "For every deeply composite n, L(Nat.sqrt(2*rank(n))) divides n, where "
                    + "Nat.sqrt is the natural-number square root, hence floor(sqrt(-)). "
                    + "Prefix locking "
                    + "and the counting bound force this divisibility: failure would place n "
                    + "below the lcm prefix while making twice its rank simultaneously no "
                    + "larger and strictly larger than the same square. This proves the "
                    + "DC/rank specialization of Switkay's A095848 comment of "
                    + "2025-09-07.",
                AssessedProvenance.FromRepo()),
            Theorem(
                "enumerated-terms-are-deeply-composite",
                "dc_nth",
                "Every enumerated term is deeply composite",
                StatementSource.FromAuthor(Disp(DcNthFormula())),
                "Infinitude of DC and Nat.nth membership show that "
                    + "every zero-indexed term a(r) satisfies DC.",
                AssessedProvenance.FromRepo()),
            Theorem(
                "enumerated-term-rank",
                "rank_nth",
                "Enumeration index and deeply composite rank agree",
                StatementSource.FromAuthor(Disp(RankNthFormula())),
                "The rank counts through its endpoint, while Nat.nth is "
                    + "zero-indexed, so rank(a(r)) equals r+1.",
                AssessedProvenance.FromRepo()),
            Theorem(
                "oeis-a095848-lcm-square-root-rank",
                "oeis_a095848_lcm_sqrt_rank",
                "The square-root-rank lcm law for the enumerated sequence",
                StatementSource.FromAuthor(Disp(SequenceMainFormula())),
                "Using DC(a(r)) and rank(a(r)) = r+1 in the divisibility law gives "
                    + "the zero-indexed sequence form of Switkay's OEIS A095848 conjecture "
                    + "from the comment of 2025-09-07.",
                AssessedProvenance.FromRepo()))));

    private static DocumentBlock Definition(
        string id, string declaration, string title, StatementSource statementSource,
        string explanation,
        AssessedProvenance provenance) =>
        Describe(
            id, declaration, title, statementSource, explanation, provenance,
            DescribeRole.Definition);

    private static DocumentBlock Theorem(
        string id, string declaration, string title, StatementSource statementSource,
        string explanation,
        AssessedProvenance provenance) =>
        Describe(
            id, declaration, title, statementSource, explanation, provenance,
            DescribeRole.Theorem);

    private static DocumentBlock.Describe Describe(
        string id,
        string declaration,
        string title,
        StatementSource statementSource,
        string explanation,
        AssessedProvenance provenance,
        DescribeRole role) =>
        StrataLint.Scribe.Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            statementSource,
            provenance,
            Blocks(Paragraph(Text(explanation))),
            role);

    private static Formula RankFormula()
    {
        Formula n = F.Id("n");
        Formula records = Call("filter", Call("Iic", n), F.Id("DC"));
        return ForAll(
            [Bound("n", Naturals())],
            Equal(Call("rank", n), Call("card", records)));
    }

    private static Formula RankEqCardFilterLeFormula()
    {
        Formula n = F.Id("n");
        Formula records = Call("filter", Call("Iic", n), F.Id("DC"));
        return ForAll(
            [Bound("n", Naturals())],
            Equal(Call("rank", n), Call("card", records)));
    }

    private static Formula RankEqCardFilterIccFormula()
    {
        Formula n = F.Id("n");
        Formula records = Call("filter", Call("Icc", Num(1), n), F.Id("DC"));
        return ForAll(
            [Bound("n", Naturals())],
            Equal(Call("rank", n), Call("card", records)));
    }

    private static Formula EnumerationFormula()
    {
        Formula r = F.Id("r");
        return ForAll(
            [Bound("r", Naturals())],
            Equal(Call("a", r), Apply(Qualified("Nat", "nth"), F.Id("DC"), r)));
    }

    private static Formula LFormula()
    {
        Formula k = F.Id("k");
        return ForAll(
            [Bound("k", Naturals())],
            Equal(Call("L", k), Apply(Qualified("Nat", "lcmUpto"), k)));
    }

    private static Formula RecordsBelowFormula()
    {
        Formula k = F.Id("k");
        Formula records = Call("filter", Call("Ico", Num(1), Call("L", k)), F.Id("DC"));
        return ForAll(
            [Bound("k", Naturals())],
            Equal(Call("recordsBelowL", k), records));
    }

    private static Formula RecordBandFormula()
    {
        Formula k = F.Id("k");
        Formula next = Add(k, Num(1));
        Formula records = Call(
            "filter", Call("Ico", Call("L", k), Call("L", next)), F.Id("DC"));
        return ForAll(
            [Bound("k", Naturals())],
            Equal(Call("recordBand", k), records));
    }

    private static Formula PrefixLockingFormula()
    {
        Formula n = F.Id("n");
        Formula j = F.Id("j");
        return ForAll(
            [Bound("n", Naturals()), Bound("j", Naturals())],
            Implies(
                Call("DC", n),
                Implies(LessEqual(Call("L", j), n), Divides(Call("L", j), n))));
    }

    private static Formula LSuccLeMulFormula()
    {
        Formula k = F.Id("k");
        Formula next = Add(k, Num(1));
        return ForAll(
            [Bound("k", Naturals())],
            LessEqual(Call("L", next), Multiply(Call("L", k), next)));
    }

    private static Formula CountingBoundFormula()
    {
        Formula k = F.Id("k");
        Formula records = Call(
            "filter", Call("Ico", Num(1), Call("L", k)), F.Id("DC"));
        Formula numerator = Multiply(k, Parenthesized(Subtract(k, Num(1))));
        return ForAll(
            [Bound("k", Naturals())],
            LessEqual(Call("card", records), Call("NatDiv", numerator, Num(2))));
    }

    private static Formula RankPositiveFormula()
    {
        Formula n = F.Id("n");
        return ForAll(
            [Bound("n", Naturals())],
            Implies(Call("DC", n), Less(Num(0), Call("rank", n))));
    }

    private static Formula MainFormula()
    {
        Formula n = F.Id("n");
        Formula twiceRank = Multiply(Num(2), Call("rank", n));
        Formula divisor = Call("L", Apply(Qualified("Nat", "sqrt"), twiceRank));
        return ForAll(
            [Bound("n", Naturals())],
            Implies(Call("DC", n), Divides(divisor, n)));
    }

    private static Formula DcNthFormula()
    {
        Formula r = F.Id("r");
        return ForAll(
            [Bound("r", Naturals())],
            Call("DC", Call("a", r)));
    }

    private static Formula RankNthFormula()
    {
        Formula r = F.Id("r");
        return ForAll(
            [Bound("r", Naturals())],
            Equal(Call("rank", Call("a", r)), Add(r, Num(1))));
    }

    private static Formula SequenceMainFormula()
    {
        Formula r = F.Id("r");
        Formula oneIndexedRank = Add(r, Num(1));
        Formula divisor = Call(
            "L", Apply(Qualified("Nat", "sqrt"), Multiply(Num(2), oneIndexedRank)));
        return ForAll(
            [Bound("r", Naturals())],
            Divides(divisor, Call("a", r)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(F.Id(name), arguments);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Qualified(string owner, string member) =>
        Seq(F.Id(owner), Dot, F.Id(member));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Relation(
        Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);

    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
