using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class SerreG2MatrixImageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/SerreG2MatrixImage.";
    private static Formula K => X("k");
    private static Formula Image => Call("matrixImage", K);
    private static Formula G2 => new Formula.Apply(Seq(Qualified("LieAlgebra"), Dot,
        new Formula.Subscript(Seq(Operatorname, Grp(X("g"))), D(2))), [K]);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual matrix image of the standard Serre G2 algebra.", H("Serre G2 and its seven-dimensional representation"),
        Blocks(
            Entry("basisMatrix", "Fourteen explicit matrices", Context(All(X("i"), Call("Fin", D(1,4)),
                Call("Matrix", Call("Fin", D(7)), Call("Fin", D(7)), K))),
                "The matrices are two coroots, six positive and six negative root vectors in dimension seven. This is concrete matrix data; it does not define a dimension-tagged replacement for G2.", DescribeRole.Definition),
            Entry("matrixImage", "An actual matrix Lie subalgebra", Context(Call("LieSubalgebra", K,
                Call("Matrix", Call("Fin", D(7)), Call("Fin", D(7)), K))),
                "The linear span of the fourteen matrices is proved closed under the actual matrix commutator. Every entry of its complete bracket table is a universal identity over the stated field. The kernel checks the matrix identities; an external finite checker is not a proof premise.", DescribeRole.Definition),
            Entry("matrixImage_finrank", "Dimension of the actual matrix image", Context(Eq(Call("Module.finrank", K, Image), D(1,4))),
                "Explicit coordinate extraction is a left inverse to assembly. It gives a linear equivalence from k to the power fourteen onto the matrix image and proves its dimension fourteen.", DescribeRole.Theorem),
            Entry("serreMap", "Map from mathlib's actual Serre G2", Context(Call("LieHom", K, G2, Image)),
                "The six Chevalley generators satisfy the actual CartanMatrix.G₂ Serre relations in the matrix image. The universal free Lie map therefore descends through exactly mathlib's Serre quotient, producing a genuine Lie homomorphism from LieAlgebra.g₂ k.", DescribeRole.Definition),
            Entry("serreMap_surjective", "Surjectivity from actual Serre words", Context(Call("Function.Surjective", Call("serreMap", K))),
                "Fourteen explicit Lie words in the actual Serre generators map to the fourteen spanning matrices. Their linear combinations prove surjectivity onto the whole matrix image.", DescribeRole.Theorem),
            Entry("correspondence_of_isSimple", "Proved correspondence under simplicity", Context(
                Instance(Call("LieAlgebra.IsSimple", K, G2), Call("LieEquiv", K, G2, Image))),
                "If the actual Serre G2 algebra is simple, the nonzero surjection has zero kernel and is an actual Lie equivalence to the fourteen-dimensional matrix image. A hypothetical isomorphism from a nonabelian simple ideal supplies this hypothesis in the KMV exclusion. No unconditional normal-form theorem or unconditional dimension computation for the Serre presentation is assumed. This correspondence suffices for that exclusion. Classical Serre and G2 matrix facts receive prior credit; the evolution-algebra application retains Haobo Ma then Wenlin Zhang attribution.", DescribeRole.Definition))));
    private static DocumentBlock.Describe Entry(string name,string title,Formula formula,string text,DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),
            H(title),StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);
    private static Formula X(string s) => F.Id(s);
    private static Formula Qualified(string s) => Seq(s.Split('.').SelectMany((part,i) =>
        i == 0 ? new Formula[] { Seq(Operatorname, Grp(X(part))) } :
            new Formula[] { Dot, Seq(Operatorname, Grp(X(part))) }).ToArray());
    private static Formula Call(string s,params Formula[] xs) => new Formula.Apply(Qualified(s),[..xs]);
    private static Formula All(Formula x,Formula t,Formula b) => Seq(Forall,Sp,Open,x,Sp,Colon,Sp,t,Close,Comma,Sp,Open,b,Close);
    private static Formula Instance(Formula t,Formula b) => Seq(OpenBracket,t,CloseBracket,Sp,b);
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Context(Formula b) => All(K,Call("Type"),Instance(Call("Field",K),Instance(Call("CharZero",K),b)));
}
