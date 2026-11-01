using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class TensorHighTemperatureLeadingClassesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/oconnorramgoolam2025gaugedtensor");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n at least two and every positive rank, the all-ones and transposition classes have the two largest tensor high-temperature degrees.",
        H("The two leading tensor high-temperature classes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tensor-high-temperature-degree"),
                DeclarationHandle.Create(Prefix + "degree"),
                H("The degree of a partition"),
                StatementSource.FromAuthor(Disp(DegreeFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a partition p of n, each tuple t chooses s entries from the set of distinct part values; "
                    + "the entries of t may repeat. Its weight is the product of each chosen value and its multiplicity. "
                    + "The degree sums this weight divided by the least common multiple of the chosen values. "
                    + "This is the degree function of Section 7.2, equation (7.21), in the v2 TeX, lines 1079-1087. "
                    + "Each subtype value and each multiplicity is cast separately from the natural numbers to the rationals before multiplication. "
                    + "The least common multiple is computed in the natural numbers and then cast to the rationals. "
                    + "The definition is total for all natural s and n, including zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tensor-high-temperature-transposition-class"),
                DeclarationHandle.Create(Prefix + "transpositionClass"),
                H("The transposition class"),
                StatementSource.FromAuthor(Disp(TranspositionFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n at least two, the transposition class has one part equal to two and n minus two parts equal to one. "
                    + "This is [2,1^(n-2)] in the v2 TeX, lines 1099-1116. "
                    + "The positive branch is the published partition126 n 1 0 constructor; its proof argument converts 2 ≤ n to the required 2·1 + 6·0 ≤ n. "
                    + "The subtraction n minus two is natural subtraction. Below that range the total definition returns Nat.Partition.indiscrete n, "
                    + "the partition obtained from the singleton multiset containing n by removing zeros. "
                    + "This last branch is a convention extending the class notation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tensor-high-temperature-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The leading-class assertion"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every n at least two and every positive rank s, the assertion gives the two exact degrees, "
                    + "places the transposition degree strictly below the all-ones degree, and places every other partition strictly below the transposition degree. "
                    + "It expresses the leading-class conjecture in the v2 TeX, line 1068, and the request for a proof in lines 1320-1322 as an ordering of rational pole orders. "
                    + "In the second exact value, n minus two is formed in the natural numbers before being cast to the rationals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tensor-high-temperature-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Strict dominance of the two leading classes"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix n at least two, a positive rank s, and a partition p of n. "
                        + "First sum the tuple weights without their least-common-multiple denominators. "
                        + "The sum of a part value times its multiplicity is n, because the parts sum to n. "
                        + "Distributing the product over the s coordinates therefore gives total weight n^s.")),
                    Paragraph(Text(
                        "For positive s, let f be the number of parts of p equal to one. "
                        + "Split the tuples into those whose entries are all one and the remaining tuples. "
                        + "The first group has total weight f^s and denominator one: it consists of the single constant tuple when one is a part, "
                        + "and is empty otherwise, when f is zero. Every tuple in the second group has a positive entry at least two. "
                        + "That entry divides its positive least common multiple, so the denominator is at least two. "
                        + "The weights are nonnegative; hence this group contributes at most (n^s - f^s)/2. "
                        + "Consequently the degree of p is at most (n^s + f^s)/2.")),
                    Paragraph(Text(
                        "For the all-ones partition with n at least two, the only distinct part value is one, with multiplicity n. "
                        + "The unique tuple has denominator one and weight n^s, giving the first exact value. "
                        + "For the transposition class every available value is one or two, with respective multiplicities n minus two and one. "
                        + "Every all-ones tuple has denominator one. Any other tuple contains two, so its least common multiple is divisible by two; "
                        + "since every entry divides two, that least common multiple also divides two and is exactly two. "
                        + "The split is therefore an equality, giving degree (n^s + (n-2)^s)/2. "
                        + "When n is two the all-ones group is empty and its weight is zero, so the same formula applies.")),
                    Paragraph(Text(
                        "Natural subtraction gives n minus two strictly less than n. "
                        + "Raising to the positive power s preserves that strict inequality, and casting to the rationals preserves it again. "
                        + "The two exact values then put the transposition degree strictly below the all-ones degree.")),
                    Paragraph(Text(
                        "Next split the multiset of parts into its ones and its parts different from one. "
                        + "The ones form a replicate multiset with cardinality f. If p differs from the all-ones partition, the other multiset is nonempty; "
                        + "each of its parts is at least two, so its sum is at least two. Since the two sums add to n, this proves f at most n minus two.")),
                    Paragraph(Text(
                        "Equality f = n minus two characterizes the transposition class. "
                        + "Indeed, equality forces the sum of the parts different from one to be two. "
                        + "Each such part is at least two, so twice their cardinality is at most two. "
                        + "Their sum is nonzero, so the cardinality is one and the sole part is two. "
                        + "Together with the f ones this recovers exactly the transposition partition. "
                        + "Conversely, counting the ones in that partition gives n minus two.")),
                    Paragraph(Text(
                        "Thus a partition different from both displayed classes has f strictly less than n minus two. "
                        + "Strict monotonicity of a positive natural power, followed by the rational cast, gives f^s strictly less than (n-2)^s. "
                        + "Combining this with the half-weight bound puts its degree strictly below the exact transposition degree. "
                        + "The two exact values and the two strict comparisons give all four clauses for every n at least two and every s at least one."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oconnor-ramgoolam-2025-tensor-high-temperature-leading-classes"),
                    ResolutionKind.Proved)))));

    private static Formula DegreeFormula()
    {
        Formula entry = Typed(At(Qualified("Subtype", "val"), At(X("t"), X("j"))), Naturals());
        Formula count = At(Qualified("Multiset", "count"), entry, Parts());
        Formula weight = ProductOver("j", FinOf(X("s")), Multiply(NatToRat(entry), NatToRat(count)));
        Formula image = At(Qualified("Finset", "image"),
            LambdaOf("j", FinOf(X("s")), entry),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), FinOf(X("s")))));
        Formula lcm = At(Qualified("Finset", "lcm"), image,
            Typed(Qualified("id"), Arrow(Naturals(), Naturals())));
        Formula tuples = Arrow(FinOf(X("s")), DistinctParts());
        return All("s", Naturals(), All("n", Naturals(), All("p", PartitionOf(X("n")),
            Equal(Typed(LocalCall("degree", X("s"), X("p")), Rationals()),
                SumOver("t", tuples, new Formula.Fraction(weight, NatToRat(lcm)))))));
    }

    private static Formula TranspositionFormula()
    {
        Formula condition = LE(Typed(D(2), Naturals()), X("n"));
        Formula value = Typed(LocalCall("transpositionClass", X("n")), PartitionOf(X("n")));
        Formula positive = At(Partition126(), X("n"), D(1), D(0), X("h"));
        Formula negative = At(Qualified("Nat", "Partition", "indiscrete"), X("n"));
        Formula branch = Call("dite", condition,
            Parenthesized(LambdaOf("h", condition, positive)),
            Parenthesized(At(Qualified("Function", "const"), new Formula.Not(Parenthesized(condition)), negative)));
        return All("n", Naturals(), Equal(value, branch));
    }

    private static Formula ClaimBody()
    {
        Formula ones = At(OnesPartition(), X("n"));
        Formula transposition = LocalCall("transpositionClass", X("n"));
        Formula onesDegree = LocalCall("degree", X("s"), ones);
        Formula transpositionDegree = LocalCall("degree", X("s"), transposition);
        Formula first = Equal(onesDegree, Pow(NatToRat(X("n")), X("s")));
        Formula second = Equal(transpositionDegree,
            new Formula.Fraction(Add(Pow(NatToRat(X("n")), X("s")),
                Pow(NatToRat(NatSubTwo()), X("s"))), Typed(D(2), Rationals())));
        Formula others = All("p", PartitionOf(X("n")),
            Implication(NotEqual(X("p"), ones), Implication(NotEqual(X("p"), transposition),
                Less(LocalCall("degree", X("s"), X("p")), transpositionDegree))));
        return All("n", Naturals(), Implication(LE(Typed(D(2), Naturals()), X("n")),
            All("s", Naturals(), Implication(LE(Typed(D(1), Naturals()), X("s")),
                Conjunction(first, Conjunction(second, Conjunction(Less(transpositionDegree, onesDegree), others)))))));
    }

    private static Formula Parts() => At(Qualified("Nat", "Partition", "parts"), X("p"));
    private static Formula DistinctParts() => Seq(OpenBrace, Typed(X("x"), Naturals()), Sp,
        Slash, Slash, Sp, new Formula.Relation(X("x"), FormulaRelationOperator.MemberOf,
            At(Qualified("Multiset", "toFinset"), Parts())), CloseBrace);
    private static Formula NatSubTwo() => Typed(Subtract(X("n"), Typed(D(2), Naturals())), Naturals());
    private static Formula NatToRat(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Rationals());
    private static Formula PartitionOf(Formula n) => At(Qualified("Nat", "Partition"), n);
    private static Formula OnesPartition() => Qualified("D5", "S3", "Combinatorics", "Partitions",
        "ColouredOddMultiplicity", "onesPartition");
    private static Formula Partition126() => Qualified("D5", "S1", "Recurrence", "Partitions",
        "GawronUlasFactorialSignConjecture", "partition126");
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(X("Q")));
    private static Formula Local(string name) => Qualified("D5", "S3", "StatisticalMechanics",
        "TensorHighTemperatureLeadingClasses", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula ProductOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
