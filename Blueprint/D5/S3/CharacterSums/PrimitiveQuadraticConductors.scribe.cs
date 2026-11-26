using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class PrimitiveQuadraticConductorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/PrimitiveQuadraticConductors.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive levels and all coefficients of six quadratic characters",
        H("Primitive conductors for quadratic products"),
        Blocks(
            Paragraph(Text("Let q and d be distinct odd primes. For natural n, write Jₚ(n) = (n/p) for "
                + "the Jacobi symbol, and E(n) for the standard character χ₈ evaluated at n modulo eight. "
                + "Products below are pointwise, with integer values cast to the complex numbers. "
                + "Write R(a,f) if a primitive character of level a takes the value f(n) at every natural n.")),
            Describe.Lean(DescribeId.Create("six-levels"), DeclarationHandle.Create(Module + "six_quadratic_levels"),
                H("Native levels for the six quadratic coefficient functions"),
                StatementSource.FromAuthor(Six()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The primitive quadratic character of an odd prime gives Jₚ. At level eight, "
                        + "χ₈(5) = −1 rules out a lift from four, where 5 represents the identity. "
                        + "Multiplying characters with coprime conductors multiplies their conductors. "
                        + "The coefficient identity holds on units by change of level, and on nonunits "
                        + "because a local factor and the character on the product level both vanish."))), DescribeRole.Theorem),
            Paragraph(Text("For the next statement the coefficient values may lie in any commutative monoid "
                + "with zero. Fix positive levels r and a and a positive test modulus M. Let χ be primitive "
                + "of level r and suppose f has a primitive representative of level a. Write C(n) for the "
                + "value of χ at n modulo r. Assume C(n) = f(n) for every n coprime to M.")),
            Describe.Lean(DescribeId.Create("inducing-level"), DeclarationHandle.Create(Module + "inducing_level_and_values"),
                H("Agreement on natural inputs coprime to a test modulus recovers every value"),
                StatementSource.FromAuthor(F.Disp(And(Eq(F.Id("r"),F.Id("a")),
                    new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
                        F.Seq(F.Mathbb,F.Grp(F.Id("N"))), Eq(At("C",F.Id("n")), At("f",F.Id("n"))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Lift both primitive characters to level raM. Every unit there has a natural "
                        + "representative coprime to M, so the lifted characters agree. Taking conductors "
                        + "identifies r with a. Injectivity of the change of level then identifies the characters "
                        + "on their common native level, including their values at natural inputs sharing factors with M."))),
                DescribeRole.Theorem))));

    private static Formula Six()
    {
        var q = F.Id("q");
        var d = F.Id("d");
        var jq = F.Id("Jq");
        var jd = F.Id("Jd");
        var e = F.Id("E");
        var qd = Mul(q, d);
        var product = Mul(jq, jd);
        return F.Disp(And(
            At("R", q, jq), At("R", Mul(F.D(8), q), Mul(e, jq)),
            At("R", d, jd), At("R", Mul(F.D(8), d), Mul(e, jd)),
            At("R", qd, product), At("R", Mul(F.D(8), qd), Mul(e, product))));
    }

    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Mul(Formula a, Formula b) => F.Seq(a, F.Sp, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(params Formula[] terms) =>
        terms.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
}
