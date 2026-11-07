using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class EldarAntiharmonicAdjacencyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/EldarAntiharmonicAdjacency.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/eldar2021a179875");
    private static readonly LibraryNoteRef Moments =
        LibraryNoteRef.Create("D5/L/ArithUnits/petridi2016eulersums");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent totative antiharmonic means agree exactly at consecutive Moebius signs one and minus one.",
        H("Eldar's antiharmonic adjacency conjecture"),
        Blocks(
            Paragraph(Text("The sums use natural indices and rational means. Positive totatives "
                + "are taken up to and including the modulus. At modulus one the single "
                + "totative is one, so its antiharmonic mean is one. For larger moduli, "
                + "coprimality excludes the upper endpoint.")),
            Node("totativeMoment", "Positive totative moments", MomentFormula(),
                "OEIS A053818, NAME: \"a(n) = Sum_{k=1..n, gcd(n,k) = 1} k^2.\" "
                + "OEIS A023896, NAME: \"Sum of positive integers in smallest positive "
                + "reduced residue system modulo n. a(1) = 1 by convention.\" "
                + "These web entries have no page numbers. The exponent j is natural; "
                + "j=2 and j=1 give these two sequences. The inclusive sum gives one "
                + "at n=1 for every j. Petridi, Section 1, page 1, writes the general "
                + "power sum over the Euler set for moduli greater than one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("antiharmonicMean", "The rational antiharmonic mean", MeanFormula(),
                "OEIS A179875, COMMENT: \"Antiharmonic mean B(h) of numbers k such "
                + "that gcd(k, h) = 1 for numbers h >= 1 and k < h = A053818(n) / "
                + "A023896(n) = A175505(h) / A175506(h).\" This web entry has no "
                + "page number. Here n is h, and division takes place in Rat after "
                + "both natural sums are cast to Rat. The term k=1 makes the first "
                + "moment positive whenever n is positive.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete adjacency criterion", ClaimFormula(),
                "OEIS A179875, COMMENT, revision 13: \"Conjecture: also numbers k "
                + "such that mu(k) = 1 and mu(k+1) = -1, where mu is the Möbius "
                + "function (tested on the first 10^4 terms).\" The NAME is: "
                + "\"Numbers h such that h and h+1 have same antiharmonic mean of "
                + "the numbers k < h such that gcd(k, h) = 1.\" This web entry has "
                + "no page number. The index n is the source's h and the COMMENT's "
                + "k. ArithmeticFunction.moebius is integer-valued. The assertion "
                + "quantifies over every n at least one and includes both directions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Equal adjacent means and Moebius signs", Disp(ClaimBody()),
                "Möbius inversion expresses each literal totative moment as a divisor "
                + "sum of ordinary power sums. The classical first and second moments "
                + "give three times the mean as twice the modulus plus the signed "
                + "radical divided by the modulus. Its absolute value is at most one. "
                + "Equality at either endpoint occurs precisely at the corresponding "
                + "Möbius sign. Equal adjacent means force the two opposite endpoints; "
                + "the same endpoint identities prove the converse. Direct evaluation "
                + "includes n=1. The argument makes no assertion about infinitely many "
                + "equal pairs, integral means, or higher moments.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Moments),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("a179875-antiharmonic-adjacency"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("eldar-a179875-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula MomentFormula()
    {
        var j = F.Id("j");
        var n = F.Id("n");
        var k = F.Id("k");
        var summand = App(Qualified("ite"),
            App(Qualified("Nat", "Coprime"), k, n), new Formula.Power(k, j), D(0));
        var sum = Seq(new Formula.Subscript(Sum,
            Seq(k, Sp, InMacro, Sp, App(Qualified("Finset", "Icc"), D(1), n))),
            Sp, summand);
        return Disp(All("j", NatType(), All("n", NatType(),
            Equal(App(Qualified("totativeMoment"), j, n), sum))));
    }

    private static Formula MeanFormula()
    {
        var n = F.Id("n");
        var numerator = CastRat(App(Qualified("totativeMoment"), D(2), n));
        var denominator = CastRat(App(Qualified("totativeMoment"), D(1), n));
        return Disp(All("n", NatType(), Equal(
            App(Qualified("antiharmonicMean"), n),
            new Formula.Fraction(numerator, denominator))));
    }

    private static Formula ClaimFormula() => Disp(Equal(Qualified("claim"), ClaimBody()));

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var successor = new Formula.Binary(n, FormulaBinaryOperator.Add, D(1));
        var equality = Equal(App(Qualified("antiharmonicMean"), n),
            App(Qualified("antiharmonicMean"), Parenthesized(successor)));
        var signs = new Formula.Logic(
            Parenthesized(Equal(App(Qualified("ArithmeticFunction", "moebius"), n), D(1))),
            FormulaLogicOperator.And,
            Parenthesized(Equal(App(Qualified("ArithmeticFunction", "moebius"),
                Parenthesized(successor)), new Formula.Negate(D(1)))));
        var iff = new Formula.Logic(Parenthesized(equality), FormulaLogicOperator.Iff,
            Parenthesized(signs));
        return All("n", NatType(), new Formula.Logic(
            Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n)),
            FormulaLogicOperator.Implies, Parenthesized(iff)));
    }

    private static Formula NatType() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula CastRat(Formula value) => Parenthesized(
        Seq(value, Colon, Sp, new Formula.NamedConstant(FormulaIdentifier.Create("Rat"))));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
