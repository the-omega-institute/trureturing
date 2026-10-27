using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Games;

internal sealed class ManabeRestrictedAmalgamationNimDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/manabe2024restrictedamalgamation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Manabe's restricted three-pile amalgamation Nim satisfies Conjecture 1.",
        H("Manabe's restricted amalgamation Nim"),
        Blocks(
            Node("move", "The six kinds of options", MoveFormula(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "Definition 4, page 2: “Two players take turns to do one of the following (i) and (ii). "
                + "(i) A player chooses a pile and removes any number of stones from the pile. "
                + "(ii) A player can replace two piles with a single pile containing the total number of stones "
                + "in the original two piles when the numbers of stones in two piles are equal to or more than 2.” "
                + "Definition 5, pages 2–3: “For x, y, z ∈ Z≥0, we define” move(x, y, z) by sets (1)–(6). "
                + "The printed equality signs between those sets denote their union. Naturals include zero; "
                + "each merger includes both placements of the sum and zero."),
            Node("size", "A decreasing measure", SizeFormula(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "The measure is the stone total plus the number of nonempty piles. Removing stones "
                + "decreases it, and a legal merger preserves the stone total while decreasing the latter count."),
            Node("grundy", "The Grundy recursion", GrundyFormula(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "The Grundy number is the least excluded option value. The existing mex is "
                + "D5.S0.Certificates.Games.AbukuEnforceNimberDomination.mex. Every option has smaller size, "
                + "so the displayed recursion always takes the recursive branch on options. "
                + "The product Nat × Nat × Nat is associated to the right; q.1, q.2.1 and q.2.2 are its entries."),
            Node("claim", "Conjecture 1", Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Section 3, Conjecture 1, page 14: “For n ∈ Z≥0, we have the following (i) and (ii). "
                + "(i) If the Grundy number of a position (x, y, z) is 2n, then x ⊕ y ⊕ z = 2n or "
                + "x ⊕ y ⊕ z = 2n + 1. (ii) If the Grundy number of a position (x, y, z) is 2n + 1, "
                + "then x ⊕ y ⊕ z = 2n or x ⊕ y ⊕ z = 2n + 1.” Here Nat.xor is bitwise XOR, "
                + "the three pile sizes and n range over all naturals, and grundy uses exactly the six option sets."),
            Node("result", "Both parts of the conjecture", ClaimBody(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Strong induction on size determines the exact Grundy value. Write each pile as 2a + e, "
                + "with e equal to zero or one. Let h be the XOR of the three quotients, p the XOR of the "
                + "three remainders, B the existence of a positive bitwise-disjoint pair of quotients, "
                + "and E positivity and pairwise bitwise disjointness of all three quotients. "
                + "Put δ = 1 exactly when B holds and E fails. The value is 2h + (p XOR δ). "
                + "Ordinary reductions reach both values in every smaller quotient block. A legal merger "
                + "preserving h reverses the corrected low bit; if that bit is one, a reduction of an odd "
                + "pile or a merger of an even disjoint pair reaches 2h. Thus mex gives the formula and "
                + "both asserted implications.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("manabe-2024-restricted-amalgamation-nim-conjecture-1"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("manabe-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula MoveFormula()
    {
        var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z"); var q = F.Id("q");
        var xy = And(Leq(Num(2), x), And(Leq(Num(2), y),
            Or(Equal(q, Triple(Add(x, y), Num(0), z)), Equal(q, Triple(Num(0), Add(x, y), z)))));
        var yz = And(Leq(Num(2), y), And(Leq(Num(2), z),
            Or(Equal(q, Triple(x, Add(y, z), Num(0))), Equal(q, Triple(x, Num(0), Add(y, z))))));
        var xz = And(Leq(Num(2), x), And(Leq(Num(2), z),
            Or(Equal(q, Triple(Add(x, z), y, Num(0))), Equal(q, Triple(Num(0), y, Add(x, z))))));
        // The outer three ordinary alternatives precede the three merger alternatives.
        var body = Or(Ex("u", Nat(), And(Less(F.Id("u"), x), Equal(q, Triple(F.Id("u"), y, z)))),
            Or(Ex("v", Nat(), And(Less(F.Id("v"), y), Equal(q, Triple(x, F.Id("v"), z)))),
                Or(Ex("w", Nat(), And(Less(F.Id("w"), z), Equal(q, Triple(x, y, F.Id("w"))))),
                    Or(xy, Or(yz, xz)))));
        return AllThree(Equal(Call("move", x, y, z),
            Seq(OpenBrace, q, Sp, Colon, Sp, TripleType(), Sp, Bar, Sp, body, CloseBrace)));
    }

    private static Formula SizeFormula()
    {
        var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z");
        Formula Nonempty(Formula a) => Conditional(Equal(a, Num(0)), Num(0), Num(1));
        return AllThree(Equal(Call("size", x, y, z),
            Add(Add(Add(Add(Add(x, y), z), Nonempty(x)), Nonempty(y)), Nonempty(z))));
    }

    private static Formula GrundyFormula()
    {
        var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z"); var q = F.Id("q"); var g = F.Id("g");
        var a = Seq(q, Dot, Num(1)); var b = Seq(q, Dot, Num(2), Dot, Num(1));
        var c = Seq(q, Dot, Num(2), Dot, Num(2));
        var guarded = Conditional(Less(Call("size", a, b, c), Call("size", x, y, z)),
            Call("grundy", a, b, c), Num(0));
        var values = Ex("q", TripleType(), And(Member(q, Call("move", x, y, z)), Equal(g, guarded)));
        return AllThree(Equal(Call("grundy", x, y, z),
            Call("mex", Seq(OpenBrace, g, Sp, Colon, Sp, Nat(), Sp, Bar, Sp, values, CloseBrace))));
    }

    private static Formula ClaimBody()
    {
        var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z"); var n = F.Id("n");
        var twice = Multiply(Num(2), n); var odd = Add(twice, Num(1));
        var xor = App(Qualified("Nat", "xor"), App(Qualified("Nat", "xor"), x, y), z);
        var alternatives = Or(Equal(xor, twice), Equal(xor, odd));
        return AllThree(All("n", Nat(), And(
            Implies(Equal(Call("grundy", x, y, z), twice), alternatives),
            Implies(Equal(Call("grundy", x, y, z), odd), alternatives))));
    }

    private static Formula Nat() => F.Id("Nat");
    private static Formula TripleType() => Seq(Nat(), Sp, Times, Sp, Parenthesized(Seq(Nat(), Sp, Times, Sp, Nat())));
    private static Formula Triple(Formula x, Formula y, Formula z) => Parenthesized(Seq(x, Comma, Sp, y, Comma, Sp, z));
    private static Formula AllThree(Formula body) => All("x", Nat(), All("y", Nat(), All("z", Nat(), body)));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, F.Id(name));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(F.Id("if"), Sp, Parenthesized(condition), Sp, F.Id("then"), Sp, yes,
            Sp, F.Id("else"), Sp, no));
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
