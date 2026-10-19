using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Games;

internal sealed class AbukuEnforceNimberDominationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Games/AbukuEnforceNimberDomination.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/abuku2024enforce");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal outcomes under the enforce operator do not imply equal nimbers.",
        H("Ruleset domination does not imply nimber domination"),
        Blocks(
            Definition("Short", "Short rulesets", ShortFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Definition 4, page 6: “The ruleset A = (X, f) is short if for any x ∈ X, "
                + "there exists a non-negative integer T_A(x) such that every play sequence, "
                + "even ignoring the alternating play condition, starting in x, terminates in "
                + "at most T_A(x) moves.” X is a type and f assigns a set of options. "
                + "The sequence s must fail to follow an option at some index i ≤ T."),
            Definition("JointlyShort", "Joint shortness", JointlyShortFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Definition 10, page 10: “Let A = (X, f_A) and B = (X, f_B) be short "
                + "rulesets on a set X. Then A and B are jointly short if the ruleset (X, f) "
                + "given by, for all x ∈ X, f(x) = f_A(x) ∪ f_B(x), is short.” "
                + "The two option maps are fA and fB."),
            Definition("Outcome", "The two perfect-play outcomes",
                Seq(F.Id("inductive"), Sp, F.Id("Outcome"), Colon, F.Id("Type"), Sp,
                    Bar, Sp, Qualified("Outcome", "P"), Sp,
                    Bar, Sp, Qualified("Outcome", "N")),
                AssessedProvenance.FromLiterature(Source),
                "Definition 5, page 6: “Consider a short impartial ruleset A = (X, f). "
                + "Then O(x) = O_A(x) ∈ {P, N} is the perfect play outcome of the position "
                + "x ∈ X, under ruleset A.” The inductive type Outcome has constructors "
                + "P and N, for a win by the previous and current player respectively; "
                + "equality of its constructors is decidable."),
            Definition("IsOutcome", "The ordinary outcome recursion", OutcomeFormula(false),
                AssessedProvenance.FromLiterature(Source),
                "Definition 5, page 6: “Consider a short impartial ruleset A = (X, f). "
                + "Then O(x) = O_A(x) ∈ {P, N} is the perfect play outcome of the position "
                + "x ∈ X, under ruleset A.” Normal play gives P exactly when all options "
                + "are N; the formula specifies this recursion for the function O."),
            Definition("IsEnforceOutcome", "The enforce outcome recursion", OutcomeFormula(true),
                AssessedProvenance.FromLiterature(Source),
                "Definition 13, page 11: “The enforce operator on these rulesets is the "
                + "combined ruleset A ⊙ B, where on each turn, before a play, the opponent "
                + "enforces one of these two rulesets, and the current player plays according "
                + "to that ruleset.” Thus P means that at least one of fA and fB has only "
                + "N options. The choice is made anew at every position."),
            Definition("mex", "The least excluded natural", MexFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Definition 28, page 17: “Let S denote a finite set of non-negative integers. "
                + "Then the minimal excludant mex(S) is the least non-negative integer "
                + "not in S.” For a set s of naturals this is sInf of the complement. The finite option-value sets "
                + "in the three-position example have nonempty complements."),
            Definition("IsNimValue", "Ordinary nimbers", NimFormula(false),
                AssessedProvenance.FromLiterature(Source),
                "Definition 29, page 18: “For any game position x, the nim-value function "
                + "G(x) is G(x) = mex({G(x′) | x′ ∈ f(x)}).” The image of f(x) under G "
                + "is represented by Set.image."),
            Definition("IsEnforceNimValue", "Enforce nimbers", NimFormula(true),
                AssessedProvenance.FromLiterature(Source),
                "Definition 33, page 18: “Let A and B be jointly short rulesets on X, "
                + "and consider the game A ⊙ B. Then, the enforce nimber of x ∈ X is "
                + "Gᴱ(x) = Gᴱ_A⊙B(x) where Gᴱ(x) = mex({Gᴱ(x′) | x′ ∈ f_A(x)} ∩ "
                + "{Gᴱ(x′) | x′ ∈ f_B(x)}).” The formula takes the intersection of the "
                + "two option-value images."),
            Definition("claim", "The implication asked about in Problem 42",
                Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                "Problem 42, page 23: “If a ruleset dominates another, does it also "
                + "‘nimber dominate’ that ruleset? That is, does it follow that all nimbers "
                + "of the combined ruleset are the same as those of the dominating ruleset?” "
                + "X is arbitrary; fA and fB are jointly short. OA and OE satisfy the "
                + "ordinary and enforce outcome recursions, and GA and GE satisfy the "
                + "ordinary and enforce nimber recursions. Domination means equality of "
                + "OE and OA at every position. The proposed conclusion is equality of "
                + "GE and GA at every position."),
            Describe.Lean(DescribeId.Create("enforce-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A three-position refutation"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "On Fin 3, the option sets for A are ∅, {0}, {0,1}, while those "
                    + "for B are ∅, {0}, {0}. Every move strictly decreases the position, "
                    + "so the union is short. Both outcomes are (P,N,N). The ordinary "
                    + "nimbers are (0,1,2), and the enforce nimbers are (0,1,1). At "
                    + "position 2 the ordinary option values are {0,1}, whereas the "
                    + "intersection for the enforce operator is {0}. Their least excluded "
                    + "values are 2 and 1. Equality of outcomes therefore leaves a "
                    + "positive nimber distinction undetermined."))), DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("enforce-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ShortFormula()
    {
        var x = F.Id("x");
        var f = F.Id("f");
        var s = F.Id("s");
        var i = F.Id("i");
        var body = All("x", F.Id("X"), Ex("T", Nat(),
            All("s", Arrow(Nat(), F.Id("X")), Implies(Equal(App(s, Num(0)), x),
                Ex("i", Nat(), And(Leq(i, F.Id("T")),
                    new Formula.Not(Parenthesized(Member(App(s, Add(i, Num(1))), App(f, App(s, i)))))))))));
        return All("X", F.Id("Type"), All("f", OptionMap(),
            Equal(Call("Short", f), Parenthesized(body))));
    }

    private static Formula JointlyShortFormula() => All("X", F.Id("Type"),
        All("fA", OptionMap(), All("fB", OptionMap(),
            Equal(Call("JointlyShort", F.Id("fA"), F.Id("fB")),
                Call("Short", Lam("x", Union(Call("fA", F.Id("x")), Call("fB", F.Id("x")))))))));

    private static Formula OutcomeFormula(bool enforce)
    {
        var x = F.Id("x");
        var y = F.Id("y");
        Formula Options(string f) => All("y", F.Id("X"),
            Implies(Member(y, Call(f, x)), Equal(Call("O", y), Qualified("Outcome", "N"))));
        var body = All("x", F.Id("X"), Iff(Equal(Call("O", x), Qualified("Outcome", "P")),
            enforce ? Or(Options("fA"), Options("fB")) : Options("f")));
        var equation = Equal(enforce
            ? Call("IsEnforceOutcome", F.Id("fA"), F.Id("fB"), F.Id("O"))
            : Call("IsOutcome", F.Id("f"), F.Id("O")), Parenthesized(body));
        var withO = All("O", Arrow(F.Id("X"), F.Id("Outcome")), equation);
        return All("X", F.Id("Type"), enforce
            ? All("fA", OptionMap(), All("fB", OptionMap(), withO))
            : All("f", OptionMap(), withO));
    }

    private static Formula MexFormula() => All("s", Call("Set", Nat()),
        Equal(Call("mex", F.Id("s")), Call("sInf", App(Qualified("Set", "compl"), F.Id("s")))));

    private static Formula NimFormula(bool enforce)
    {
        Formula Image(string f) => App(Qualified("Set", "image"), F.Id("G"), Call(f, F.Id("x")));
        var body = All("x", F.Id("X"), Equal(Call("G", F.Id("x")),
            Call("mex", enforce ? Intersection(Image("fA"), Image("fB")) : Image("f"))));
        var equation = Equal(enforce
            ? Call("IsEnforceNimValue", F.Id("fA"), F.Id("fB"), F.Id("G"))
            : Call("IsNimValue", F.Id("f"), F.Id("G")), Parenthesized(body));
        var withG = All("G", Arrow(F.Id("X"), Nat()), equation);
        return All("X", F.Id("Type"), enforce
            ? All("fA", OptionMap(), All("fB", OptionMap(), withG))
            : All("f", OptionMap(), withG));
    }

    private static Formula ClaimBody() => All("X", F.Id("Type"),
        All("fA", OptionMap(), All("fB", OptionMap(),
            Implies(Call("JointlyShort", F.Id("fA"), F.Id("fB")),
                All("OA", Arrow(F.Id("X"), F.Id("Outcome")),
                    All("OE", Arrow(F.Id("X"), F.Id("Outcome")),
                        All("GA", Arrow(F.Id("X"), Nat()), All("GE", Arrow(F.Id("X"), Nat()),
                            Implies(Call("IsOutcome", F.Id("fA"), F.Id("OA")),
                                Implies(Call("IsEnforceOutcome", F.Id("fA"), F.Id("fB"), F.Id("OE")),
                                    Implies(Call("IsNimValue", F.Id("fA"), F.Id("GA")),
                                        Implies(Call("IsEnforceNimValue", F.Id("fA"), F.Id("fB"), F.Id("GE")),
                                            Implies(All("x", F.Id("X"), Equal(Call("OE", F.Id("x")), Call("OA", F.Id("x")))),
                                                All("x", F.Id("X"), Equal(Call("GE", F.Id("x")), Call("GA", F.Id("x")))))))))))))))));

    private static Formula Nat() => F.Id("Nat");
    private static Formula OptionMap() => Arrow(F.Id("X"), Call("Set", F.Id("X")));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Lam(string name, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, F.Id(name), Sp, Mapsto, Sp, body));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, F.Id(name));
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Union(Formula left, Formula right) => Seq(left, Sp, Cup, Sp, right);
    private static Formula Intersection(Formula left, Formula right) => App(Qualified("Set", "inter"), left, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
