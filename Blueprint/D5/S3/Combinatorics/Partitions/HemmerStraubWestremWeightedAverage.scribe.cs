using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class HemmerStraubWestremWeightedAverageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.";
    private static LibraryNoteRef Source() => LibraryNoteRef.Create("D5/L/FiniteGroups/hemmerstraubwestrem2025riordan");
    private const string SourceClaim = "Conjecture 6.1, equation (6.1), page 12 (journal Conjecture 17, page 15), states: “For any integer n≥1,”. The displayed proposition encodes both equalities of (6.1). The domain is n : Nat with 1 ≤ n. Ev retains each independent replacement, including repeated cycle types; R3 pads even partitions by zeros, and ![n,n,0] pads the rectangle. Character sums are integers cast to Rat. Nat.div denotes integer division, so Nat.div n 2 equals the source’s n/2 on the even branch. The inherited frobChar is the Frobenius coefficient model; its representation-theoretic interpretation is the literature input of Lemma 3.1.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted Ev character averages equal the even binomial value and vanish in odd degrees.",
        H("The weighted Hemmer–Straub–Westrem character average"),
        Blocks(
            Node("hsww-weight", "The reciprocal centralizer weight", "weight", WeightFormula(),
                "Section 2, page 4, states: “For a partition λ with part frequencies (1^{m₁}, 2^{m₂}, …, n^{mₙ}), we denote with z_λ = ∏_{j=1}^n j^{mⱼ} mⱼ! the size of the centralizer of a permutation with cycle type λ.” The existing zPartition is this multiplicity product; weight is its reciprocal in Rat.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hsww-left-average", "The signed even-row average", "leftAverage", AverageFormula(true),
                "The first expression in equation (6.1), page 12, sums the signed Ev character sum over all partitions with reciprocal centralizer weights. No restriction on repeated or mixed part sizes is imposed.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hsww-right-average", "The rectangular-character average", "rightAverage", AverageFormula(false),
                "The middle expression in equation (6.1), page 12, averages the Ev sum of the rectangular character with the same weights.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hsww-claim", "Conjecture 6.1", "claim", Disp(IffFormula(Call("claim"), ClaimBody())),
                SourceClaim, DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hsww-result", "The weighted identity and closed form", "result", Disp(ClaimBody()),
                "The per-partition equality gives the equality of averages. Removing a marked part of size k multiplies the centralizer factor by k times its new multiplicity, which gives the cycle-index recurrence over any commutative Rat-algebra. Coefficient induction determines the solution of its first-order formal differential equation. For part input 2 times (z^k+1+z^(−k)), the solution is the product of the squares of three geometric series. Subtracting the adjacent Laurent coefficient cancels the (1−t)^2 factor and leaves (1−t²)^(−3). Its even coefficients are the stated binomial values, and its odd coefficients vanish.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source()),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hsw17"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(X(name))) : App(Seq(Operatorname, Grp(X(name))), args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffFormula(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Fun(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Call("fun"), Parenthesized(Seq(X(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula NatType() => Call("Nat");
    private static Formula IntType() => Call("Int");
    private static Formula RatType() => Call("Rat");
    private static Formula ListNat() => Call("List", NatType());
    private static Formula Partition(Formula n) => App(Qualified("Nat", "Partition"), n);
    private static Formula SumList(Formula list) => App(Qualified("List", "sum"), list);
    private static Formula Map(Formula fn, Formula list) => App(Qualified("List", "map"), fn, list);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Multiply(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Centralizer(Formula lam) => App(Qualified("DeformedJucysMurphyC2", "zPartition"), lam);

    private static Formula WeightFormula()
    {
        Formula n = X("n"), lam = X("lam");
        return Disp(All("n", NatType(), All("lam", Partition(n), Equal(Call("weight", lam),
            Power(Cast(Centralizer(lam), RatType()), Seq(Minus, D(1)))))));
    }

    private static Formula AverageFormula(bool signed)
    {
        Formula n = X("n"), lam = X("lam"), tau = X("tau"), mu = X("mu");
        Formula parts = Seq(lam, Dot, Call("parts"), Dot, Call("toList"));
        Formula ev = Call("evTypes", parts);
        Formula triple = Seq(Bang, OpenBracket, n, Comma, n, Comma, D(0), CloseBracket);
        Formula summand = signed
            ? Seq(new Formula.Subscript(Sum, Seq(mu, Sp, InMacro, Sp, Call("R3", Multiply(D(2), n)))),
                Sp, Parenthesized(Multiply(Power(Cast(Seq(Minus, D(1)), IntType()),
                    App(Qualified("List", "length"), tau)), Call("frobChar", mu, tau))))
            : Call("frobChar", triple, tau);
        Formula chars = Cast(Cast(SumList(Map(Fun("tau", ListNat(), summand), ev)), IntType()), RatType());
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(lam, Colon, Sp, Partition(n))), Sp,
            Parenthesized(Multiply(Call("weight", lam), chars)));
        return Disp(All("n", NatType(), Equal(Call(signed ? "leftAverage" : "rightAverage", n), sum)));
    }

    private static Formula ClaimBody()
    {
        Formula n = X("n");
        Formula half = App(Qualified("Nat", "div"), n, D(2));
        Formula choose = App(Qualified("Nat", "choose"), Parenthesized(Seq(half, Plus, D(2))), D(2));
        Formula value = Call("ite", Call("Even", n), Cast(Cast(choose, NatType()), RatType()), Cast(D(0), RatType()));
        return All("n", NatType(), Imp(AtMost(D(1), n), And(
            Equal(Call("leftAverage", n), Call("rightAverage", n)), Equal(Call("rightAverage", n), value))));
    }
}
