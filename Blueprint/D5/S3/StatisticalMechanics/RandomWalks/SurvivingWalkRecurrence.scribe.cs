using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.RandomWalks;

internal sealed class SurvivingWalkRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/mathar2012a026023");
    private static readonly LibraryNoteRef Walks =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/jianu2025dycktype");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The number a(n) of walks s(0), ..., s(n) on the nonnegative integers with steps of size 1 and s(0) = 3 satisfies (n + 4)(n - 1) a(n) + (n - 1)(n + 1) a(n - 1) - 2(n + 1)(2n + 1) a(n - 2) - 4(n - 1)(n + 1) a(n - 3) = 0 for every n at least 3, as conjectured by R. J. Mathar for OEIS A026023. These walks are the paths of a random walker started at x = 4 that have not been adsorbed at x = 0 by time n.",
        H("Mathar's recurrence for surviving walks from height 3"),
        Blocks(
            Node("walks", "Walks on the nonnegative integers", WalksFormula(),
                "walks(n, x) is the set of sequences s(0), ..., s(n) of nonnegative integers, indexed by Fin (n + 1), with s(0) = x and |s(i + 1) - s(i)| = 1 for every i < n; in Lean the index i ranges over Fin n and s(i + 1), s(i) are s at i.succ and i.castSucc.",
                "walks", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The sequence A026023", AFormula(),
                "a(n) is the number of such walks of length n starting at 3, the name of the entry.",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Mathar's conjecture", ClaimFormula(),
                "For every n at least 3 the four-term recurrence with quadratic coefficients holds, evaluated in the integers.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the recurrence", Disp(F.Id("claim")),
                "Let W(n, x) be the number of walks of length n from x. Splitting a walk of length n + 1 by its first step gives W(n + 1, x) = W(n, x + 1) + W(n, x - 1), the second term present only for x at least 1, and W(0, x) = 1. The reflection count R(n, x), the sum of binomial(n, d) over the d with n < 2d + x + 2 and 2d at most n + x, satisfies the same recursion by Pascal's rule, so W = R; this is Theorem 2.1 of Jianu and Daus, whose range of d is floor((n - x)/2) to floor((n + x)/2). At x = 3 the sum has four consecutive terms once n is at least 3, and one, two and three terms for n = 0, 1, 2. Pascal's rule with the symmetry of binomial coefficients gives a(2m) = c(m) and a(2m + 1) = 2 c(m) with c(m) = binomial(2m + 2, m); the proof uses this for n at least 4 and evaluates a(0), ..., a(3) = 1, 2, 4, 8 directly, which fit the same formulas. These satisfy (m + 1)(m + 3) c(m + 1) = 2(m + 2)(2m + 3) c(m). For odd n = 2j + 3 the left side of the recurrence is 12 times this relation at j; for even n = 2j + 4 it is, after multiplication by j + 2, a combination with coefficients 2(2j + 3) and 4(2j + 5) of the relations at j + 1 and j.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Walks),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathar-2012-a026023-recurrence"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("survwalk-" + id), DeclarationHandle.Create(Prefix + declaration),
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
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula WalksFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x"), s = F.Id("s"), i = F.Id("i");
        Formula next = new Formula.Apply(s, [Add(i, D(1))]);
        Formula here = new Formula.Apply(s, [i]);
        Formula step = Parenthesized(Or(Equal(next, Add(here, D(1))), Equal(Add(next, D(1)), here)));
        Formula condition = And(Equal(new Formula.Apply(s, [D(0)]), x),
            All("i", Call("Fin", n), step));
        Formula domain = new Formula.TypeArrow(Call("Fin", Add(n, D(1))), Naturals());
        return Disp(Equal(Call("walks", n, x),
            Seq(OpenBrace, s, Sp, InMacro, Sp, domain, Sp, Mid, Sp, condition, CloseBrace)));
    }

    private static Formula AFormula()
    {
        Formula n = F.Id("n");
        return Disp(Equal(Call("a", n), Call("ncard", Call("walks", n, D(3)))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula nm1 = Parenthesized(Subtract(n, D(1)));
        Formula np1 = Parenthesized(Add(n, D(1)));
        Formula t1 = Times(Times(Parenthesized(Add(n, D(4))), nm1), Call("a", n));
        Formula t2 = Times(Times(nm1, np1), Call("a", Subtract(n, D(1))));
        Formula t3 = Times(Times(Times(D(2), np1), Parenthesized(Add(Times(D(2), n), D(1)))),
            Call("a", Subtract(n, D(2))));
        Formula t4 = Times(Times(Times(D(4), nm1), np1), Call("a", Subtract(n, D(3))));
        Formula sum = Subtract(Subtract(Add(t1, t2), t3), t4);
        return Disp(Iff(F.Id("claim"), All("n", Naturals(), Implies(AtMost(D(3), n),
            Equal(sum, D(0))))));
    }
}
