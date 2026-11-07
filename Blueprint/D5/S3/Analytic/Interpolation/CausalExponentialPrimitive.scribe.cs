using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;
internal sealed class CausalExponentialPrimitiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite causal primitives and square identities.",
        H("Exact causal primitive calculus"), Blocks(
            Describe.Lean(DescribeId.Create("causal-square-ftc"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/CausalExponentialPrimitive.square_FTC"),
                H("The right-FTC square identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact finite causal ramp and resolvent primitives supply the right derivatives and endpoint cancellations used by MomentExponentialCoercivity. The square FTC identity integrates the real part of conjugate(f) times its actual right derivative. Only helpers consumed by the existing Gamma, causal-Gram and growing-primitive proof paths are public. The original declaration namespaces and all theorem surfaces remain available by importing MomentExponentialCoercivity."))),
                DescribeRole.Theorem))));
}
