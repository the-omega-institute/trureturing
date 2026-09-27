using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LatticeWalkNearMaximalAreaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LatticeWalkNearMaximalArea.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/zabolotskii2025a385672");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For k < n, the 2n-step walks on the square lattice with algebraic area n^2 - k number twice the coefficient of x^k in phi(x)/f(-x), and the (2n+1)-step walks with area n^2 + n - k number four times the coefficient of x^k in psi(x^2)/f(-x).",
        H("Walks of near-maximal algebraic area on the square lattice"),
        Blocks(
            Node("step", "Steps", StepFormula(),
                "A walk on the square lattice moves right, left, up or down by one unit at each step.",
                "Step", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("areafrom", "Area from a starting height", AreaFromFormula(),
                "The integral of y dx along a walk that starts at height y: a right step adds the current height, a left step subtracts it, and an up or down step changes the height by one.",
                "areaFrom", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("area", "Algebraic area", Disp(Equal(Call("area", F.Id("w")), Call("areaFrom", D(0), F.Id("w")))),
                "The algebraic area of a walk from the origin: the sum of the heights at its right steps minus the sum of the heights at its left steps.",
                "area", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "The triangle A385672", WalkCountFormula(),
                "The number of n-step walks, read as maps from the n positions to the four steps and turned into the list of their values in order (ofFn), whose algebraic area is k.",
                "walkCount", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("partitions", "Partition numbers", PartitionFormula(),
                "A000041: the number of partitions of m, the coefficients of the reciprocal of f(-x) = the product of (1 - x^i) over i > 0.",
                "partitionCount", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("phi", "The coefficients A029552", PhiFormula(),
                "The coefficient of x^k in (1 + 2 times the sum of x^(j^2) over j > 0) divided by the product of (1 - x^i) over i > 0.",
                "a029552", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("psi", "The coefficients A098613", PsiFormula(),
                "The coefficient of x^k in the sum of x^(j^2 - j) over j > 0 divided by the product of (1 - x^i) over i > 0.",
                "a098613", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture of A385672", ClaimFormula(),
                "For every k < n the walks of length 2n with area n^2 - k number 2 A029552(k), and the walks of length 2n + 1 with area n^2 + n - k number 4 A098613(k).",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Let r, l, u, d count the right, left, up and down steps. At a right step the height is at most u and at a left step at least -d, so the area is at most r u + l d. If the walk uses both a right or up step and a left or down step, then 4(r u + l d) is at most (r + u)^2 + (l + d)^2, which is at most 1 + (L - 1)^2 for the length L, so the area is at most n^2 - n when L = 2n and at most n^2 when L = 2n + 1. Every walk in the stated range therefore uses only right and up steps or only left and down steps, and exchanging right with left and up with down maps the second kind onto the first without changing the area. A word of u up steps and r right steps has area u r minus the number of pairs of a right step followed later by an up step. Splitting at the first step, the words with u up steps and m such pairs satisfy the recurrence N(u, r, m) = N(u - 1, r, m) + N(u, r - 1, m - u), which is also the recurrence of the partitions of m into parts at most u, split by whether the part u occurs; so for r at least m they are the partitions of m into parts at most u, and for u at least m all partitions of m. With u = n + j and r = n - j the number of pairs is k - j^2, at most the smaller of u and r because k < n, and summing over j gives p(k) + 2 times the sum of p(k - j^2) over j > 0. With u = n + 1 + j and r = n - j it is k - j(j + 1), the substitution j to -1 - j pairs the terms, and the sum is twice the sum of p(k - j(j + 1)) over j at least 0.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zabolotskii-2025-a385672-near-maximal-area-walks"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("nearmaxarea-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Count(Formula variable, Formula condition) =>
        new Formula.Absolute(Seq(OpenBrace, variable, Sp, Mid, Sp, condition, CloseBrace));
    private static Formula Cons(Formula head, Formula tail) => Call("cons", head, tail);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula SumOver(Formula index, Formula lower, Formula upper, Formula condition, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(AtMost(lower, index), Comma, Sp, AtMost(index, upper), Comma, Sp, condition)),
            Sp, body);

    private static Formula StepFormula() =>
        Disp(Equal(Named("Step"),
            new Formula.SetLiteral([F.Id("right"), F.Id("left"), F.Id("up"), F.Id("down")])));

    private static Formula AreaFromFormula()
    {
        Formula y = F.Id("y"), w = F.Id("w");
        return Disp(Seq(
            Equal(Call("areaFrom", y, Named("nil")), D(0)), Comma, Quad,
            Equal(Call("areaFrom", y, Cons(F.Id("right"), w)), Add(y, Call("areaFrom", y, w))), Comma, Quad,
            Equal(Call("areaFrom", y, Cons(F.Id("left"), w)), Add(new Formula.Negate(y), Call("areaFrom", y, w))), Comma, Quad,
            Equal(Call("areaFrom", y, Cons(F.Id("up"), w)), Call("areaFrom", Add(y, D(1)), w)), Comma, Quad,
            Equal(Call("areaFrom", y, Cons(F.Id("down"), w)), Call("areaFrom", Subtract(y, D(1)), w))));
    }

    private static Formula WalkCountFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), w = F.Id("w");
        Formula walks = new Formula.TypeArrow(Call("Fin", n), Named("Step"));
        return Disp(Equal(Call("walkCount", n, k), Count(Member(w, walks), Equal(Call("area", Call("ofFn", w)), k))));
    }

    private static Formula PartitionFormula()
    {
        Formula m = F.Id("m");
        return Disp(Equal(Call("partitionCount", m), new Formula.Absolute(Call("Partition", m))));
    }

    private static Formula PhiFormula()
    {
        Formula k = F.Id("k"), j = F.Id("j");
        Formula sum = SumOver(j, D(1), k, AtMost(Square(j), k), Call("partitionCount", Subtract(k, Square(j))));
        return Disp(Equal(Call("a029552", k), Add(Call("partitionCount", k), Times(D(2), sum))));
    }

    private static Formula PsiFormula()
    {
        Formula k = F.Id("k"), j = F.Id("j");
        Formula e = Subtract(Square(j), j);
        Formula sum = SumOver(j, D(1), Add(k, D(1)), AtMost(e, k),
            Call("partitionCount", Subtract(k, Parenthesized(e))));
        return Disp(Equal(Call("a098613", k), sum));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula even = Equal(Call("walkCount", Times(D(2), n), Subtract(Square(n), k)),
            Times(D(2), Call("a029552", k)));
        Formula odd = Equal(Call("walkCount", Add(Times(D(2), n), D(1)), Subtract(Add(Square(n), n), k)),
            Times(D(4), Call("a098613", k)));
        Formula body = All("n", Naturals(), All("k", Naturals(), Implies(Less(k, n), And(even, odd))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
