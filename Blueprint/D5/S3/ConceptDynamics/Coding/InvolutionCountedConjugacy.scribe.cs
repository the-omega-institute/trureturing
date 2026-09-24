using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class InvolutionCountedConjugacyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/InvolutionCountedConjugacy.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula S => F.Id("s");
    private static Formula T => F.Id("t");
    private static Formula Source => Call("sourceMatrix", S, T);
    private static Formula Target => Call("targetMatrix", F.Id("H"));
    private static Formula Chain(Formula a, Formula b, Formula length, Formula group) =>
        Call("ExchangeChain", Call("MonoidAlgebra", F.Id("Nat"), group), a, b, length);
    private static Formula All(Formula body, bool topology,
        params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("H", F.Id("Type")), B("group", Call("Group", F.Id("H"))),
             B("finite", Call("Fintype", F.Id("H"))),
             .. (topology ? new Formula.BoundVariable[] {
                 B("topology", Call("TopologicalSpace", F.Id("H"))),
                 B("continuousGroup", Call("IsTopologicalGroup", F.Id("H"))) } : []),
             B("s", F.Id("H")), B("t", F.Id("H")),
             B("hs", Equal(Call("product", S, S), F.D(1))), .. extra], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An involution supplies explicit nonnegative factors and an exact one-step exchange chain with a proved lower bound.",
        H("The involution factorization as an exact exchange"),
        Blocks(
            Describe.Lean(DescribeId.Create("involution-natural-products"),
                DeclarationHandle.Create(Prefix + "natural_factor_products"), H("Natural coefficients satisfy both products"),
                StatementSource.FromAuthor(Disp(All(Products(), false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegative integer factors are converted coefficientwise to natural coefficients. Lifting back is injective, so the two actual products equal the original source and target formulas."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("involution-counted-exchange"),
                DeclarationHandle.Create(Prefix + "involution_exchange"), H("Construct the one-step matrix chain"),
                StatementSource.FromAuthor(Disp(All(Chain(Source, Target, F.D(1), F.Id("H")), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The one-vertex matrices contain the constructed natural factors. A single rectangular exchange yields the given endpoints without a chain-existence assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("involution-counted-minimum-one"),
                DeclarationHandle.Create(Prefix + "involution_minimum_one"), H("The chain cannot have length zero"),
                StatementSource.FromAuthor(Disp(All(new Formula.Logic(
                    Chain(Source, Target, F.D(1), F.Id("H")), FormulaLogicOperator.And,
                    new Formula.Not(Chain(Source, Target, F.D(0), F.Id("H")))), false,
                    B("hst", new Formula.Not(Equal(Call("product", S, T), Call("product", T, S))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Noncommuting elements make the source and target coefficients different. A zero-length exchange chain has equal endpoints, while the explicit factors already give a length-one chain."))),
                DescribeRole.Theorem))));

    private static Formula Products()
    {
        Formula u = Call("toNat", Call("leftFactor", S, T));
        Formula v = Call("toNat", Call("rightFactor", S));
        return new Formula.Logic(Equal(Call("product", u, v), Call("sourceNat", S, T)),
            FormulaLogicOperator.And, Equal(Call("product", v, u), Call("targetNat", F.Id("H"))));
    }
}
