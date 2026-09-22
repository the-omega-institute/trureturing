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
            Describe.Lean(DescribeId.Create("construct-nonnegative-involution-exchange"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/InvolutionUniformExchange.nonnegative_involution_certificate"),
                H("Construct actual natural-coefficient factors"), StatementSource.FromAuthor(Disp(Claim())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Write u for the sum of all group elements and b(g) for a group-ring basis element. The explicit integral factors are U=u+(1-b(s))b(t) and V=1+b(s). Every coefficient of U is 1 plus one indicator minus one indicator, so both factors are nonnegative.")),
                    Paragraph(Text("The forward product is 2u+(1-b(s))b(t)(1+b(s)). Reversing the factors gives 2u because s squared is the identity. Converting the nonnegative coefficients to natural numbers provides genuine natural-coefficient group-ring factors.")),
                    Paragraph(Text("When s and t do not commute, the coefficient at t distinguishes the two endpoints. This rules out a zero-step exchange without identifying all isomorphisms of the associated dynamical systems."))),
                DescribeRole.Theorem))));

    private static Formula Claim()
    {
        Formula h = F.Id("H"), s = F.Id("s"), t = F.Id("t"), u = F.Id("U"), v = F.Id("V");
        Formula Exists = new Formula.BindMany(FormulaQuantifier.Exists,
            [B("U", Call("NAlg", h)), B("V", Call("NAlg", h))],
            new Formula.Logic(Equal(Call("liftNat", h, Call("HMul.hMul", u, v)), Call("source", s, t)),
                FormulaLogicOperator.And,
                Equal(Call("liftNat", h, Call("HMul.hMul", v, u)), Call("target", h))));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("H", F.Id("Type")), B("group", Call("Group", h)), B("finite", Call("Fintype", h)),
             B("s", h), B("t", h), B("involution", Equal(Call("HMul.hMul", s, s), F.D(1)))], Exists);
    }
}
