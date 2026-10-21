using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Games;

internal sealed class EllisThanatipanondaCutFamilyADocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/ellis2022cutfamilya");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every Family A cut-set has nim-sequence (0, 1)^c (+2).",
        H("Ellis–Thanatipanonda Conjecture 1: Family A"),
        Blocks(
            Node("et-nim", "The nim-sequence of cut", "G", GFormula(),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 2: “Fixing a cut-set C, we write G(n) to denote the nim-value of the "
                + "position of cut with a single pile of size n. Then G(n) is called the "
                + "nim-sequence of the game with cut-set C.” Definition 1, page 2: “Given "
                + "a pile of size n, an option O_n is a sequence of piles obtainable via "
                + "a single legal move on that pile. In other words, O_n is a particular "
                + "partition of n with d + 1 parts for some d ∈ C. Formally, O_n = "
                + "(h_0, h_1, ..., h_d) where 1 ≤ h_i and h_0 + h_1 + · · · + h_d = n.” "
                + "Here o : Fin (d + 1) → Nat lists the positive parts. List.ofFn lists "
                + "their recursively computed values and List.foldr Nat.xor 0 forms "
                + "their nim-sum. The existing mex is sInf of the complement. For d ≥ 1 "
                + "each part is smaller than n, so the recursion guard is inactive on "
                + "legal Family A options. The guarded formula also defines G at zero "
                + "and for arbitrary cut-sets."),
            Node("et-claim", "The Family A conjecture", "claim",
                Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Section 7, page 18: “Let X to be a non-empty set of even numbers, each "
                + "of which is at least 4. Let Y to be a non-empty set of odd numbers, "
                + "each of which is at least 5. Let x = 2c and y be the smallest elements "
                + "of X and Y, respectively.” “Family A: C = {1, 3} ∪ X, or C = {1, 3} ∪ X ∪ Y.” "
                + "Conjecture 1, page 18: “The nim-sequence for all games of cut in this "
                + "family are all precisely (0, 1)^c (+2).” The first alternative uses "
                + "Y = ∅; the second uses nonempty Y. The least element of X is sInf X = 2c. "
                + "Page 3: “The notation (0, 1)^3 (+2), for example, denotes the sequence "
                + "0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 4, 5, 4, 5, 4, 5, . . ..” "
                + "Thus n starts at 1, subtraction is truncated natural subtraction, "
                + "Nat.div is integer division and Nat.mod is remainder. Arbitrary "
                + "sets X and Y are allowed; only cuts smaller than n produce options."),
            Node("et-result", "The conjectured sequence for every Family A cut-set", "result",
                ClaimBody(), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                "Strong induction on the pile size replaces the values of all option "
                + "parts by the stated formula. An odd cut gives an even number of parts: "
                + "the low bit of their nim-sum is opposite to the low bit of G(n). "
                + "An even cut is at least 2c; the sum of the parts' quotient terms is "
                + "strictly below the quotient term of n. The xor of natural numbers "
                + "is at most their sum, so this also excludes the proposed value. "
                + "Every smaller value is attained using only cuts 1, 3 and 2c: two "
                + "parts, four parts with an equal pair, or a leading part followed by "
                + "2c equal parts. The minimum excluded value is therefore the proposed "
                + "one. Proposition 8 of Dailly–Duchêne–Larsson–Paris already gives "
                + "C = {1, 3, 2c}; this proof allows every extra cut in Family A."))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        DescribeRole role, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula GFormula()
    {
        var c = F.Id("C"); var n = F.Id("n"); var d = F.Id("d");
        var o = F.Id("o"); var i = F.Id("i"); var g = F.Id("g");
        var partType = Call("Fin", Add(d, Num(1)));
        var part = App(o, i);
        var guarded = Parenthesized(Seq(F.Id("if"), Sp, Parenthesized(Less(part, n)),
            Sp, F.Id("then"), Sp, Call("G", c, part), Sp, F.Id("else"), Sp, Num(0)));
        var values = App(Qualified("List", "ofFn"), Lam("i", partType, guarded));
        var nimSum = App(Qualified("List", "foldr"), Qualified("Nat", "xor"), Num(0), values);
        var sum = Seq(new Formula.Subscript(Sum, F.Id("i")), Sp, App(o, F.Id("i")));
        var options = Ex("d", Nat(), And(Member(d, c),
            Ex("o", Arrow(partType, Nat()), And(All("i", partType, Leq(Num(1), part)),
                And(Equal(sum, n), Equal(g, nimSum))))));
        var set = Seq(OpenBrace, g, Sp, Bar, Sp, options, CloseBrace);
        return All("C", Call("Set", Nat()), All("n", Nat(),
            Equal(Call("G", c, n), Call("mex", set))));
    }

    private static Formula ClaimBody()
    {
        var xSet = F.Id("X"); var ySet = F.Id("Y");
        var x = F.Id("x"); var y = F.Id("y"); var c = F.Id("c"); var n = F.Id("n");
        var evens = All("x", Nat(), Implies(Member(x, xSet),
            And(Call("Even", x), Leq(Num(4), x))));
        var odds = All("y", Nat(), Implies(Member(y, ySet),
            And(Call("Odd", y), Leq(Num(5), y))));
        var yCase = Or(Equal(ySet, Emptyset), And(App(Qualified("Set", "Nonempty"), ySet), odds));
        var cutSet = Seq(Parenthesized(Seq(new Formula.SetLiteral([Num(1), Num(3)]),
            Sp, Cup, Sp, xSet)), Sp, Cup, Sp, ySet);
        var predecessor = Subtract(n, Num(1));
        var sequence = Add(Multiply(Num(2), App(Qualified("Nat", "div"), predecessor,
            Multiply(Num(2), c))), App(Qualified("Nat", "mod"), predecessor, Num(2)));
        return All("X", Call("Set", Nat()), All("Y", Call("Set", Nat()),
            Implies(App(Qualified("Set", "Nonempty"), xSet), Implies(evens, Implies(yCase,
                All("c", Nat(), Implies(Equal(Multiply(Num(2), c), Call("sInf", xSet)),
                    All("n", Nat(), Implies(Leq(Num(1), n),
                        Equal(Call("G", cutSet, n), sequence))))))))));
    }

    private static Formula Nat() => F.Id("Nat");
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Lam(string name, Formula domain, Formula body) =>
        Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, domain)), Sp, Mapsto, Sp, body));
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
