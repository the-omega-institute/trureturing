using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.NativeReader;

internal sealed class OriginalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original finite words use the same unique ready extension.", H("Original finite words use the same unique ready extension"),
        Blocks(Describe.Lean(
            DescribeId.Create("native-reader-original"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeReader/Original.original_preparation_bridge"),
            H("Original finite words use the same unique ready extension"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The old source is every legal path b0 through b6 with fixed zero endpoints, of cardinality thirteen. sourceJ inserts b7=1,b8=0,b9=i,b10=0 and retains all old bits. Its code has 26 paths; all 63 complementary paths remain in Source. oldReady has b3=1 and is the literal old word 00100; its sourceJ image at i=false is readySource. Padding reinserts exactly the fixed exterior bits b(-1)=1 and b11=1, or b15=1 in the extended carrier. Every original projection is the existing weighted local path projection in these coordinates, including addresses zero and ten. The ready extension is the one source-defined tail, without column preparation, postselection, resampling or normalization. The matrix proof first derives that original addresses cannot leave this ready image, then identifies their entries with the original source coefficients. Every full forward pulse therefore intertwines, and induction proves the preparation identity for every finite eleven-address word from the unique original ready vector. The identity is an equality of complete vectors. It does not construct a Bell probability law or guarantee the current configuration has positive support; those remain required source obligations. Coordinate and algebra helpers earn no content; the live consumer is the source-specific no-jump statement at original preparation entrances."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement() => Disp(Seq(Forall, Sp, F.Id("a"), Colon, Sp, Call("List", Call("Fin", D(11))), Comma, Sp, Call("extendedPreparation", F.Id("a")), Sp, Eq, Sp, Call("readyExtension", Call("originalPreparation", F.Id("a")))));
}
