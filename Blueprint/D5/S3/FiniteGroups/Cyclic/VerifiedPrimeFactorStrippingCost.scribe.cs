using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Cyclic;

internal sealed class VerifiedPrimeFactorStrippingCostDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var x = X("x"); var m = X("m"); var g = X("G");
        var p = X("p"); var ps = X("P");
        var cost = C("stripFactorsCost", x, ps, m);
        var output = C("stripFactors", x, ps, m);
        var result = And(
            Equal(C("fst", cost), output),
            Rel(C("snd", cost), FormulaRelationOperator.LessThanOrEqual,
                Add(C("length", ps), C("log", Num(2), m))));
        var statement = All("G", X("Typeu"),
            Instances(C("Monoid", g), Instances(C("DecidableEq", g),
            All("x", g, All("P", C("List", X("Nat")), All("m", X("Nat"), result))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The actual stripping program has an exact power-test cost and a logarithmic division budget.",
            H("Verified prime-factor stripping cost"), Blocks(
                Paragraph(Text("The cost instrument returns a pair: its first component is the exact numeric output of the existing stripFactors program, and its second component counts calls to the power-equality test in the guard. The arithmetic guard 1<p, 0<m, and p∣m is checked first; when it fails, no power test is counted. When it passes, exactly one power test is counted, whether that test succeeds or stops the factor run. A successful test recurses on m/p, preserving the original list order and all original guards.")),
                Describe.Lean(DescribeId.Create("prime-stripping-cost-bound"),
                    DeclarationHandle.Create("D5/S3/FiniteGroups/Cyclic/VerifiedPrimeFactorStrippingCost.stripFactorsCost_spec"),
                    H("Exact output and logarithmic power-test bound"),
                    StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("For every monoid with decidable equality, element x, finite natural list P, and natural input m, the first component of stripFactorsCost x P m equals stripFactors x P m. Its second component is at most P.length + Nat.log 2 m. The theorem imposes no positivity, order, group, finiteness, factor-coverage, primality, duplicate-freedom, or input-returning hypothesis.")),
                        Paragraph(Text("The proof uses a telescoping potential. Every successful recursive division has p≥2 and lowers m to m/p; Nat.log 2 (m/p) is no larger than Nat.log 2 (m/2), while Nat.log 2 (m/2)+1=Nat.log 2 m. A factor pass therefore consumes at most one list-entry unit plus the decrease in the logarithmic potential. Summing this inequality through the left-to-right fold gives the displayed bound. The output projection is proved equal to the original well-founded recursion by strong induction on m.")),
                        Paragraph(Text("The count is only for calls to the equality test x^(m/p)=1 in the executable guard. It is not a bit complexity, a count of modular multiplications inside exponentiation, a quantum gate count, or a complete Shor complexity claim. The result is repository-derived; the classical repeated-division algorithm remains literature-attested in the neighboring source."))),
                    DescribeRole.Theorem))));
    }

            private static Formula X(string s) => DefinitionDsl.Id(s);
    private static Formula C(string s, params Formula[] xs) => DefinitionDsl.Call(s, xs);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Instances(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula And(params Formula[] xs)
    {
        var result = xs[^1];
        for (var i = xs.Length - 2; i >= 0; --i)
            result = new Formula.Logic(xs[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) =>
        new Formula.Relation(x, op, y);
}
