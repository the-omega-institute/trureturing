using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphSmallIsoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Isomorphism forms for cubic graphs on four and six vertices.",
        H("Standard small cubic graph forms"),
        Blocks(
            Describe.Lean(DescribeId.Create("four-model"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.modelFour"),
                H("The four-vertex model"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("modelFour"), Sp, Eq, Sp, Call("CompleteGraph", Call("Fin", D(4)))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The modelFour graph is the complete simple graph on Fin 4."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("triangles-model"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.modelSixTriangles"),
                H("The complement of two triangles"),
                StatementSource.FromAuthor(Disp(Call("CompleteBipartite", Call("Fin", D(3)), Call("Fin", D(3))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The graph modelSixTriangles has vertex type Fin 6. Two vertices are adjacent "
                    + "precisely when one has value less than three and the other has value at least three."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cycle-model"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.modelSixCycle"),
                H("The complement of a six-cycle"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("modelSixCycle"), Sp, Eq, Sp, Call("Complement", Call("CycleGraph", D(6)))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The graph modelSixCycle is the complement of Mathlib's cycleGraph 6, "
                    + "whose cycle follows the vertex order 0,1,2,3,4,5."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("four-isomorphism"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.cubic_four_iso"),
                H("The four-vertex isomorphism"),
                StatementSource.FromAuthor(Disp(Seq(Call("Cubic", F.Id("G")), Sp, Land, Sp,
                    Call("VertexCount", F.Id("G")), Sp, Eq, Sp, D(4), Sp, Implies, Sp,
                    Call("Isomorphic", F.Id("G"), F.Id("modelFour"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Every simple cubic graph on a finite vertex type of cardinality four is "
                    + "isomorphic to modelFour. Cardinality supplies a vertex equivalence and "
                    + "the degree condition makes adjacency equivalent to vertex inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("six-isomorphism"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.cubic_six_iso"),
                H("The six-vertex isomorphism alternatives"),
                StatementSource.FromAuthor(Disp(Seq(Call("Cubic", F.Id("G")), Sp, Land, Sp,
                    Call("VertexCount", F.Id("G")), Sp, Eq, Sp, D(6), Sp, Implies, Sp,
                    Call("Isomorphic", F.Id("G"), F.Id("modelSixTriangles")), Sp, Lor, Sp,
                    Call("Isomorphic", F.Id("G"), F.Id("modelSixCycle"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Every simple cubic graph on a finite vertex type of cardinality six is "
                    + "isomorphic either to modelSixTriangles or to modelSixCycle. Its complement "
                    + "has degree two. A structural vertex listing identifies that complement "
                    + "with two disjoint triangles or a six-cycle, and the same equivalence "
                    + "identifies the original graph with the corresponding complement model."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall"))]));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
