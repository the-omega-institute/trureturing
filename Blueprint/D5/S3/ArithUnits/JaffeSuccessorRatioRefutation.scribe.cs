using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class JaffeSuccessorRatioRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/jaffe2026denominators");
    private static Formula Z => Seq(Mathbb, Grp(F.Id("Z")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The primitive Frobenius successor ratio exceeds five for an admissible pair of integers.",
        H("Jaffe's unrestricted successor-ratio conjecture is false"),
        Blocks(
            Node("Represented", "Primitive nonnegative integer coefficients", RepresentedFormula(),
                "Represented(a,b,n) means that n = ax + by for nonnegative integers x and y "
                    + "with gcd(x,y)=1. The gcd is the natural gcd of their absolute values. "
                    + "Both coordinate axes are included. Passing between nonnegative integers "
                    + "and natural coefficients preserves the equality and coprimality.",
                DescribeRole.Definition),
            Node("missing", "The full integer complement", MissingFormula(),
                "The set missing(a,b) consists of all integers without a primitive nonnegative "
                    + "representation. Its domain is the whole integer line, including the "
                    + "negative integers.", DescribeRole.Definition),
            Node("sourceG", "Greatest missing integer or infinity", SourceGFormula(),
                "sourceG(a,b) takes values in the extended real numbers. When the integer "
                    + "complement has a greatest element m, its value is the real embedding of m. "
                    + "When there is no greatest element, its value is positive infinity. "
                    + "For positive coprime A and B at least three, the counting argument below "
                    + "proves an actual greatest missing integer at least one.",
                DescribeRole.Definition),
            Node("successor", "The next integer coprime to the first argument", SuccessorFormula(),
                "successor(a,b) is the integer infimum of the integers c strictly greater than b "
                    + "and coprime to a. For a,b at least three this set is nonempty: "
                    + "a(b+1)+1 is greater than b and coprime to a. It is bounded below by b, "
                    + "so the integer infimum belongs to the set and is its least element.",
                DescribeRole.Definition),
            Node("fullClaim", "The whole unrestricted Conjecture 7.3", ClaimFormula(),
                "For every pair of coprime integers a,b at least three, the claim bounds "
                    + "sourceG(a,successor(a,b))/sourceG(a,b) by five. No relation a<b is assumed. "
                    + "The coefficients, complement and successor have exactly the meanings "
                    + "given above. The same assertion is Conjecture 8.3 in the earlier thesis.",
                DescribeRole.Definition),
            Node("result", "The full conjecture has a counterexample", new Formula.Not(F.Id("fullClaim")),
                "Take a=87841397512641630 and b=7. The integer a is coprime to 7 and 49, "
                    + "and each integer from 8 through 48 is noncoprime to a. Hence successor(a,7)=49. "
                    + "Let H(n) count all nonnegative solutions of Ax+By=n, and let P(n) count "
                    + "the primitive ones. Residues modulo B place H(n) between floor(n/(AB)) "
                    + "and floor(n/(AB))+1. Partitioning by gcd(x,y) and applying Mobius inversion "
                    + "gives AB P(n) >= phi(n)-AB tau(n), where tau(n) is the positive-divisor "
                    + "count. Factoring phi and tau over prime powers gives n tau(n)^2 <= "
                    + "16^7 phi(n)^2. For primes at least seven the corresponding factor has "
                    + "constant one; a factor sixteen suffices for each smaller prime, of which "
                    + "there are at most seven. Therefore every n>16^7(AB)^2 has a primitive "
                    + "representation. Since 1 is missing when A,B>=3, the entire integer "
                    + "complement has a greatest element at least one. Apply this to (a,7) "
                    + "and (a,49), obtaining actual finite positive maxima m and M. A primitive "
                    + "representation of 7m for (a,49) would force its first coefficient to be "
                    + "divisible by 7. Dividing that coefficient preserves coprimality and "
                    + "would represent m for (a,7), a contradiction. Thus M>=7m and M/m>=7>5. "
                    + "The quotient uses these actual maxima; their numerical values are unnecessary. "
                    + "Finiteness and scaling are prior ingredients of the source's Theorems 4.3 "
                    + "and 7.1. The added condition a<b would define a different assertion, "
                    + "whose truth is not established by this counterexample.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("jaffe-primitive-frobenius-successor-ratio"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("jaffe-successor-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            role == DescribeRole.Theorem ? AssessedProvenance.FromRepo(Source)
                : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula RepresentedFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var n = F.Id("n");
        var x = F.Id("x"); var y = F.Id("y");
        var equation = Eq(Add(Mul(a, x), Mul(b, y)), n);
        var coefficients = And(Le(F.D(0), x),
            And(Le(F.D(0), y), And(Coprime(x, y), equation)));
        return All("a", Z, All("b", Z, All("n", Z,
            Iff(Call("Represented", a, b, n), Ex("x", Z, Ex("y", Z, coefficients))))));
    }

    private static Formula MissingFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var n = F.Id("n");
        return All("a", Z, All("b", Z, All("n", Z,
            Iff(In(n, Call("missing", a, b)), new Formula.Not(Call("Represented", a, b, n))))));
    }

    private static Formula SourceGFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var m = F.Id("m");
        var greatest = Call("IsGreatest", Call("missing", a, b), m);
        return All("a", Z, All("b", Z,
            And(All("m", Z, Implies(greatest, Eq(Call("sourceG", a, b), m))),
                Implies(new Formula.Not(Ex("m", Z, greatest)),
                    Eq(Call("sourceG", a, b), Infty)))));
    }

    private static Formula SuccessorFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var c = F.Id("c");
        var set = Seq(OpenBrace, c, InMacro, Z, Colon, Sp,
            And(Lt(b, c), Coprime(a, c)), CloseBrace);
        return All("a", Z, All("b", Z,
            Eq(Call("successor", a, b), Call("sInf", set))));
    }

    private static Formula ClaimFormula()
    {
        var a = F.Id("a"); var b = F.Id("b");
        var quotient = new Formula.Fraction(
            Call("sourceG", a, Call("successor", a, b)), Call("sourceG", a, b));
        return Iff(F.Id("fullClaim"), All("a", Z, All("b", Z,
            Implies(Le(F.D(3), a), Implies(Le(F.D(3), b),
                Implies(Coprime(a, b), Le(quotient, F.D(5))))))));
    }

    private static Formula Coprime(Formula a, Formula b) =>
        Eq(Call("gcd", Call("natAbs", a), Call("natAbs", b)), F.D(1));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula In(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
