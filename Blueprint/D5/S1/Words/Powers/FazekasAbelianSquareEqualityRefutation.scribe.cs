using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class FazekasAbelianSquareEqualityRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/fazekas2026binary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary word abab refutes the equality conclusion in Conjecture 4 on abelian squares.",
        H("A Four-Letter Refutation of the Abelian-Square Equality Claim"),
        Blocks(
            Node(
                "abelian-square",
                "Binary abelian squares",
                "IsAbelianSquare",
                IsAbelianSquareFormula(),
                "The binary alphabet is encoded by a=false and b=true. NatDiv is floor division "
                    + "on natural numbers. The midpoint p is NatDiv(length(u),2), and both letter "
                    + "counts are equal across take(p,u) and drop(p,u).",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "abelian-square-factors",
                "Distinct abelian-square factors",
                "abelianSquares",
                AbelianSquaresFormula(),
                "The factors are prefixes of suffixes, formed by inits and tails. Converting them "
                    + "to a finite set removes repeated occurrences before filtering for abelian squares.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "trivial-abelian-square",
                "Trivial abelian squares",
                "IsTrivial",
                IsTrivialFormula(),
                "A trivial abelian square is a positive even power of exactly one binary letter.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "fazekas-conjecture-four",
                "Conjecture 4",
                "claim",
                ClaimFormula(),
                "Conjecture 4 (printed page 1) reads verbatim: “A binary word of length n contains at "
                    + "least ⌊n/4⌋ abelian squares and if it contains exactly ⌊n/4⌋ abelian squares then all "
                    + "the abelian squares are trivial.” The word is a list over the letters a ↦ false and "
                    + "b ↦ true; the number of abelian squares is the number of distinct abelian-square "
                    + "factors, as in the paper's example abaababa with six such factors. For every binary "
                    + "word w, NatDiv(length(w),4) is at most that number, and if equality holds, every such "
                    + "factor is asserted to be trivial.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "fazekas-conjecture-four-refuted",
                "The equality conclusion fails",
                "result",
                ResultFormula(),
                "For abab the distinct abelian-square factor set is the singleton containing abab, "
                    + "so its cardinality is NatDiv(4,4)=1. The factor abab contains both letters "
                    + "and is not a positive even power of either one. This refutes the conjunction "
                    + "through its equality conclusion and does not refute the lower bound.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "fazekas-abelian-square-equality-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula IsAbelianSquareFormula()
    {
        var u = F.Id("u");
        var p = F.Id("p");
        var midpoint = NatDiv(Length(u), D(2));
        var left = Call("take", p, u);
        var right = Call("drop", p, u);
        var definition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, p, Sp, Colon, Eq, Sp, midpoint, Comma, Sp,
            Conjoin(
                Less(D(0), p),
                Equal(Length(u), Multiply(D(2), p)),
                Equal(Count(F.Id("false"), left), Count(F.Id("false"), right)),
                Equal(Count(F.Id("true"), left), Count(F.Id("true"), right))));
        return Disp(ForAll(
            "u",
            ListBool(),
            IffFormula(Call("IsAbelianSquare", u), definition)));
    }

    private static Formula AbelianSquaresFormula()
    {
        var w = F.Id("w");
        var factors = Call("flatMap", F.Id("inits"), Call("tails", w));
        var distinctFactors = Call("toFinset", factors);
        var filtered = Call("filter", F.Id("IsAbelianSquare"), distinctFactors);
        return Disp(ForAll(
            "w",
            ListBool(),
            Equal(Call("abelianSquares", w), filtered)));
    }

    private static Formula IsTrivialFormula()
    {
        var u = F.Id("u");
        var m = F.Id("m");
        var evenPower = Multiply(D(2), m);
        var constantFalse = Call("replicate", evenPower, F.Id("false"));
        var constantTrue = Call("replicate", evenPower, F.Id("true"));
        var existential = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("m"),
            Naturals(),
            And(
                Less(D(0), m),
                Or(Equal(u, constantFalse), Equal(u, constantTrue))));
        return Disp(ForAll(
            "u",
            ListBool(),
            IffFormula(Call("IsTrivial", u), existential)));
    }

    private static Formula ClaimFormula()
    {
        var w = F.Id("w");
        var u = F.Id("u");
        var factors = Call("abelianSquares", w);
        var count = Cardinality(factors);
        var lowerBound = NatDiv(Length(w), D(4));
        var allTrivial = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("u"),
            factors,
            Call("IsTrivial", u));
        var quantified = ForAll(
            "w",
            ListBool(),
            And(
                LessOrEqual(lowerBound, count),
                Implies(Equal(count, lowerBound), allTrivial)));
        return Disp(IffFormula(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula ForAll(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula ListBool() => Call("List", F.Id("Bool"));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Length(Formula value) => Call("length", value);

    private static Formula Count(Formula letter, Formula word) =>
        Call("count", letter, word);

    private static Formula Cardinality(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula NatDiv(Formula value, Formula divisor) =>
        Call("NatDiv", value, divisor);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.And,
            Parenthesized(right));

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.Or,
            Parenthesized(right));

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(
            Parenthesized(hypothesis),
            FormulaLogicOperator.Implies,
            Parenthesized(conclusion));

    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
}
