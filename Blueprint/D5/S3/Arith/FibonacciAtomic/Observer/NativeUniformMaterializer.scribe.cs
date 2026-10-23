using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeUniformMaterializerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformMaterializer.";
    private static DocumentBlock Entry(string n, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeuniformmaterializer-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(n), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeUniformMaterializer", H("NativeUniformMaterializer"), Blocks(
            Paragraph(Text("The complete analysis is computed on a fixed first-order, infinite type of finite input codes. Primitive syntax, tree, history, ordering and budget operations are composed with the existing computable native solver. The exact theorem concerns the original native definitions for all rows, cuts, histories and epochs. Malformed codes return none; contradictory histories remain computational inputs. The complete four-way service criterion and joint online-controller evaluator remain separate obligations.")),
            Entry("uniform_native_materializer", "One computable map is quantified before all literal rows C, cut sets Q, finite histories H and epochs N. On codeCommon C Q H N it returns the exact nativeAnalysisCode C Q H, including all raw cells, pair branches, ordered ground bindings, native summary and original K0. Every old disequality is checked under the fully composed native action. The epoch N has no effect on the returned reference bundle. This closes uniform effectiveness of native analysis and K0; it does not establish the four whole-service equivalences or online controller effectiveness.", DescribeRole.Theorem))));
}
