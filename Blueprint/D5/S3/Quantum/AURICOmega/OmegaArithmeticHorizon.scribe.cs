using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaArithmeticHorizonDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon";

    private static readonly Formula Naturals = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Integers = Seq(Mathbb, Grp(F.Id("Z")));
    private static readonly Formula Lists = F.Id("NatList");

    public DocumentDefinition Create()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), d = F.Id("d");
        Formula p = F.Id("p"), q = F.Id("q"), n = F.Id("N"), s = F.Id("S");
        Formula x = F.Id("x"), y = F.Id("y"), zero = D(0), one = D(1);
        Formula product = Call("prod", s), plusOne = Add(product, one);
        Formula length = Call("length", s), determinant = Call("determinant", s);
        Formula numerator = Call("numerator", s), denominator = Call("denominator", s);
        Formula depth = Call("quarterDepth", c, d, p, q);
        Formula nextPower = new Formula.Power(D(4), Add(n, one));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Zero-axiom arithmetic for Chapter 32, sections 32.7 and 32.8, and Appendix Q.",
            H("The computable arithmetic horizon"),
            Blocks(
                Law("euclid-prime-escape", "euclid_prime_escape", "Prime escape from a finite list",
                    Bind(FormulaQuantifier.ForAll, Lists, If(Lt(zero, product),
                        Bind(FormulaQuantifier.Exists, Naturals, And(Call("IsPrime", p),
                            And(Divides(p, plusOne), new Formula.Not(Rel(p, FormulaRelationOperator.MemberOf, s)))), "p")), "S"),
                    "Every list member greater than one leaves remainder one on dividing the successor of the product. A positive product makes that successor at least two, so a prime divisor exists and is outside the list. The empty list has product one."),
                Law("bezout-identity", "bezout_identity", "Signed Bézout coefficients",
                    Bind(FormulaQuantifier.ForAll, Naturals,
                        Bind(FormulaQuantifier.Exists, Integers,
                            Eq(Add(Mul(a, x), Mul(b, y)), Call("gcd", a, b)), "x", "y"), "a", "b"),
                    "The Euclidean algorithm updates the coefficients when replacing the inputs by the divisor and remainder. The identity includes both zero inputs."),
                Law("cf-convergent-determinant", "cf_convergent_determinant", "Alternating determinant of successive continuants",
                    Bind(FormulaQuantifier.ForAll, Lists,
                        Eq(determinant, new Formula.Power(Grp(new Formula.Negate(one)), length)), "S"),
                    "The determinant is the current numerator times the preceding denominator minus the preceding numerator times the current denominator. Appending a coefficient reverses its sign. Adjacent convergents at indices n and n+1 use n+2 coefficients, so this is the Euler–Wallis sign at index n."),
                Law("cf-convergent-coprime", "cf_convergent_coprime", "Every convergent has coprime coordinates",
                    Bind(FormulaQuantifier.ForAll, Lists,
                        Bind(FormulaQuantifier.ForAll, Naturals,
                            If(And(Divides(d, numerator), Divides(d, denominator)), Eq(d, one)), "d"), "S"),
                    "The coordinates refer to the current continuant of the list. A common divisor divides the magnitude of its unit determinant with the preceding continuant, including at the first convergent."),
                Law("machin-rational-chain", "machin_rational_chain", "Machin's exact rational tangent chain",
                    Rel(F.Id("machinChain"), FormulaRelationOperator.Equivalent, one),
                    "Double 1/5 using tangent addition to obtain 5/12, then double again to obtain 120/119. Subtract 1/239 using tangent subtraction. Using the reduced 120/119 intermediate, the final homogeneous product has numerator and denominator 28561 before reduction."),
                Law("quarter-depth-integer-sound", "quarterDepth_integer_sound", "Integer quarter-depth soundness",
                    Bind(FormulaQuantifier.ForAll, Naturals, If(And(Lt(zero, d), And(Lt(zero, p),
                        Rel(depth, FormulaRelationOperator.LessThanOrEqual, n))),
                        Lt(Mul(c, q), Mul(Mul(d, p), nextPower))), "c", "d", "p", "q", "N"),
                    "The search finds the least depth whose next power of four, multiplied by dp, strictly exceeds cq. When q is positive the library also gives the strict comparison of the corresponding exact ratios."))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Bind(FormulaQuantifier quantifier, Formula domain, Formula body, params string[] variables) =>
        new Formula.BindMany(quantifier,
            [.. variables.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Eq(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) => Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula Divides(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Divides, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula If(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement, string commentary) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create($"{Module}.{selector}"),
            H(title),
            StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))),
            DescribeRole.Theorem);
}
