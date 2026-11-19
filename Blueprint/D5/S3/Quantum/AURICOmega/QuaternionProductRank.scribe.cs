using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class QuaternionProductRankDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/QuaternionProductRank.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The product of the quaternion comparison model with itself is noncommutative, chain connected and touches zero, but its reading is not the Gram kernel of a map into Euclidean five-space.",
        H("The product of two quaternion comparison models"),
        Blocks(
            Describe.Lean(DescribeId.Create("quaternion-product-rank-not-feature-rank-five"),
                DeclarationHandle.Create(Prefix + "prod_quaternionModel_not_hasFeatureRank_five"),
                H("The product of two quaternion models does not have feature rank five"),
                StatementSource.FromAuthor(ProductFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The product structure prod C D on pairs has the componentwise transfer and the product of the two readings. "
                        + "Since the quaternion model is noncommutative, chain connected and touches zero, the product with a second copy is noncommutative, chain connected and touches zero, by the corresponding statements for products. "
                        + "Suppose its reading had feature rank five. Then there is an injective map u from pairs of unit quaternions into the unit quaternions with u (tri x y z) = u x * (u y)^-1 * u z for all x, y, z. "
                        + "With o = (1, 1), the map w p = (u o)^-1 * u p satisfies w p * w p = (u o)^-1 * u (tri p o p), so every pair p with tri p o p = o and p different from o has w p * w p = 1 and w p different from 1. "
                        + "In the quaternions q * q = 1 forces q = 1 or q = -1, so w p = -1 for every such p. "
                        + "The two different pairs (-1, 1) and (1, -1) both satisfy tri p o p = o, since (-1) * 1^-1 * (-1) = 1. "
                        + "Hence they have the same image under w, and therefore under u, which contradicts injectivity."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);

    private static Formula ProductFormula()
    {
        Formula model = Seq(Operatorname, Grp(F.Id("quaternionModel")));
        Formula product = Call("prod", model, model);
        return Disp(And(Call("Noncommutative", product),
            And(Call("ChainConnected", product),
                And(Call("TouchesZero", product),
                    new Formula.Not(Call("HasFeatureRank", product, D(5)))))));
    }
}
