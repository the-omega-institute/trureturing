using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class IsingUniquenessSetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/IsingUniquenessSets.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/skalski2025level");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On the cube of sign vectors, the Walsh functions of degree at most two span the Ising space. A set of points is a set of uniqueness for the nonnegative cone of this space when the only nonnegative function of the space vanishing there is zero; the smallest such set has k + 1 points for every k at least three.",
        H("The smallest set of uniqueness for the Ising cone"),
        Blocks(
            DefinitionNode("sgn", "The sign of a Boolean coordinate", SgnFormula(),
                "A point of the cube is a function from Fin k to Bool; the value true stands for +1 and false for -1."),
            DefinitionNode("walsh", "Walsh functions", WalshFormula(),
                "For a finite set L of coordinates, the Walsh function is the product of the coordinate signs over L; the empty product is the constant function one."),
            DefinitionNode("walshSpace", "The space spanned by Walsh functions of bounded degree", WalshSpaceFormula(),
                "The real linear span of the Walsh functions indexed by sets of at most q coordinates; for q = 2 it is the Ising space of constants, fields and pair couplings."),
            DefinitionNode("IsSetOfUniqueness", "Sets of uniqueness for the nonnegative cone", UniquenessFormula(),
                "A finite set U of points is a set of uniqueness for the nonnegative cone of the Walsh space when every nonnegative function of the space that vanishes on U is the zero function."),
            DefinitionNode("minUniqueness", "The smallest size of a set of uniqueness", MinUniquenessFormula(),
                "The infimum of the sizes of the sets of uniqueness; the whole cube is always one, so the infimum is attained."),
            DefinitionNode("claim", "The conjecture u(k, 2) = k + 1", ClaimDefinitionFormula(),
                "The first conjunct is the clause that no set of uniqueness has at most k points, for every k. The second is the equality u(k, 2) = k + 1 for every k at least three. The third records u(2, 2) = 4: for k = 2 the Walsh space of degree two is the whole function space, so only the whole square is a set of uniqueness."),
            TheoremNode("result", "No set of uniqueness has at most k points", ClaimFormula(),
                "Lower bound: if U has at most k points, the evaluation map sending v in R^(k+1) to the values v_0 + sum_i v_i x_i at the points x of U has a nonzero kernel vector. The square of the affine function v_0 + sum_i v_i x_i lies in the Walsh space of degree two because every coordinate squares to one; it is nonnegative, vanishes on U, and is not identically zero, since comparing the all-plus point with the point where coordinate i is flipped forces v_i = 0 and then v_0 = 0. Upper bound for k at least three: on the Walsh space of degree two the sums over the points e_m with one plus sign, the points f_m with one minus sign, and the two constant points satisfy sum_m phi(f_m) - sum_m phi(e_m) + (k - 2)(phi(-1) - phi(1)) = 0 and sum_m phi(e_m) + sum_m phi(f_m) - (k - 4)(phi(1) + phi(-1)) = 8 2^(-k) sum_x phi(x), as each Walsh function of degree at most two checks directly. If phi is nonnegative and vanishes at the points e_m and at the all-plus point, the first identity forces phi(-1) = 0 and phi(f_m) = 0, the second then gives a zero total sum, and nonnegativity gives phi = 0; these k + 1 points form a set of uniqueness. For k = 2 the indicator of any missing point lies in the space, so only the whole square works.")),
        []));

    private static DocumentBlock DefinitionNode(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("ising-uniqueness-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static DocumentBlock TheoremNode(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("ising-uniqueness-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Negative(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Bools() => Named("Bool");
    private static Formula Point(Formula k) => new Formula.TypeArrow(Fin(k), Bools());
    private static Formula FinsetOf(Formula t) => Call("Finset", t);
    private static Formula Card(Formula s) => Call("card", s);

    private static Formula SgnFormula()
    {
        Formula b = F.Id("b");
        return Disp(All("b", Bools(), Equal(Call("sgn", b), Call("ite", b, D(1), Negative(D(1))))));
    }

    private static Formula WalshFormula()
    {
        Formula k = F.Id("k"), l = F.Id("L"), x = F.Id("x"), j = F.Id("j");
        Formula product = Seq(new Formula.Subscript(Prod, Seq(j, Sp, InMacro, Sp, l)),
            Sp, Parenthesized(Call("sgn", new Formula.Apply(x, [j]))));
        Formula body = Equal(Call("walsh", l, x), product);
        return Disp(All("k", Naturals(), All("L", FinsetOf(Fin(k)), All("x", Point(k), body))));
    }

    private static Formula WalshSpaceFormula()
    {
        Formula k = F.Id("k"), q = F.Id("q"), l = F.Id("L");
        Formula generators = Seq(OpenBrace, Call("walsh", l), Sp, Mid, Sp,
            Member(l, FinsetOf(Fin(k))), Comma, Sp, AtMost(Card(l), q), CloseBrace);
        Formula body = Equal(Call("walshSpace", k, q), Call("Submodule.span", Reals(), generators));
        return Disp(All("k", Naturals(), All("q", Naturals(), body)));
    }

    private static Formula UniquenessBody(Formula k, Formula q, Formula u)
    {
        Formula phi = F.Id("phi"), x = F.Id("x");
        Formula nonnegative = All("x", Point(k), AtMost(D(0), new Formula.Apply(phi, [x])));
        Formula vanishes = All("x", u, Equal(new Formula.Apply(phi, [x]), D(0)));
        return All("phi", Call("walshSpace", k, q), Implies(nonnegative, Implies(vanishes, Equal(phi, D(0)))));
    }

    private static Formula UniquenessFormula()
    {
        Formula k = F.Id("k"), q = F.Id("q"), u = F.Id("U");
        Formula body = new Formula.Logic(Call("IsSetOfUniqueness", k, q, u), FormulaLogicOperator.Iff,
            Parenthesized(UniquenessBody(k, q, u)));
        return Disp(All("k", Naturals(), All("q", Naturals(), All("U", FinsetOf(Point(k)), body))));
    }

    private static Formula MinUniquenessFormula()
    {
        Formula k = F.Id("k"), q = F.Id("q"), n = F.Id("n"), u = F.Id("U");
        Formula witness = Some("U", FinsetOf(Point(k)),
            And(Equal(Card(u), n), Call("IsSetOfUniqueness", k, q, u)));
        Formula sizes = Seq(OpenBrace, Member(n, Naturals()), Sp, Mid, Sp, witness, CloseBrace);
        Formula body = Equal(Call("minUniqueness", k, q), Call("sInf", sizes));
        return Disp(All("k", Naturals(), All("q", Naturals(), body)));
    }

    private static Formula ClaimBody()
    {
        Formula k = F.Id("k"), u = F.Id("U");
        Formula noSmall = All("k", Naturals(), All("U", FinsetOf(Point(k)),
            Implies(Call("IsSetOfUniqueness", k, D(2), u), AtMost(Add(k, D(1)), Card(u)))));
        Formula exact = All("k", Naturals(), Implies(AtMost(D(3), k),
            Equal(Call("minUniqueness", k, D(2)), Add(k, D(1)))));
        Formula edge = Equal(Call("minUniqueness", D(2), D(2)), D(4));
        return And(noSmall, And(exact, edge));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ClaimFormula() => Disp(ClaimBody());
}
