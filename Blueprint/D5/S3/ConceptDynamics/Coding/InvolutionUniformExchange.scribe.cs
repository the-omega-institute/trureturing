using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class InvolutionUniformExchangeDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-group involution supplies nonnegative exchange factors for a nonuniform perturbation of the uniform element.",
        H("Involution uniform exchange"), Blocks(
            Describe.Lean(DescribeId.Create("reverse-involution-exchange"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/InvolutionUniformExchange.factors_reverse"),
                H("Reverse the factors to the uniform target"), StatementSource.FromAuthor(Disp(Claim())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Write u for the sum of all group elements and b(g) for a group-ring basis element. The explicit integral factors are U=u+(1-b(s))b(t) and V=1+b(s). Every coefficient of U is 1 plus one indicator minus one indicator, so both factors are nonnegative.")),
                    Paragraph(Text("The forward product is 2u+(1-b(s))b(t)(1+b(s)). Reversing the factors gives 2u because s squared is the identity. Converting the nonnegative coefficients to natural numbers provides genuine natural-coefficient group-ring factors.")),
                    Paragraph(Text("When s and t do not commute, the coefficient at t distinguishes the two endpoints. The counted companion module performs the coefficientwise conversion and constructs the exact one-step exchange."))),
                DescribeRole.Theorem))));

    private static Formula Claim()
    {
        Formula h = F.Id("H"), s = F.Id("s"), t = F.Id("t");
        Formula product = new Formula.Binary(Call("rightFactor", s),
            FormulaBinaryOperator.Multiply, Call("leftFactor", s, t));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("H", F.Id("Type")), B("group", Call("Group", h)), B("finite", Call("Fintype", h)),
             B("s", h), B("t", h), B("involution", Equal(new Formula.Binary(s, FormulaBinaryOperator.Multiply, s), F.D(1)))],
            Equal(product, Call("target", h)));
    }
}
