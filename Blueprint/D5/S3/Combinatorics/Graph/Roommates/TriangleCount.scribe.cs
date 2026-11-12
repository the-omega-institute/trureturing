using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class TriangleCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Roommates/TriangleCount.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact exclusive-triangle profile removal", H("Exact exclusive-triangle profile removal"), Blocks(
            Describe.Lean(DescribeId.Create("reflection"), DeclarationHandle.Create(Prefix + "reflectWord"),
                H("Interval reflection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reflection reverses the three interval positions and negates every signed offset. The certificate transport retains all integer-target injectivity constraints, including exterior targets, reciprocity and nonblocking. Zero remains single with rank four."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("words"), DeclarationHandle.Create(Prefix + "forbiddenWord"),
                H("Sixteen ranking words"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The index is one orientation bit and three independent Boolean choices. In the forward orientation, positions zero, one and two respectively prefer signed offsets (1,2), (1,-1) and (-2,-1), in that order, to both exterior offsets. Each Boolean chooses the order of the bottom two offsets. Reflection gives the other orientation. The sixteen ranking words are distinct."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("impossible"), DeclarationHandle.Create(Prefix + "forbidden_not_certified"),
                H("Every listed profile is impossible"), StatementSource.FromAuthor(Disp(
                    All("s", Call("TriangleIndex"), Seq(Neg, Sp, Some("d", Call("Assignments"),
                        Call("Certificate", Call("forbiddenWord", F.Id("s")), F.Id("d"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("TriangleIndex abbreviates Bool times (Fin 3 to Bool), and Assignments abbreviates Fin 3 to the integers. The forward case directly applies the saved exclusive_triangle_not_certified theorem. The reverse case transports a hypothetical certificate through reflection and applies the same theorem. No matching witness is enumerated; exterior partners and singles remain allowed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("profiles"), DeclarationHandle.Create(Prefix + "forbiddenProfiles"),
                H("Removed profiles"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite set is the image of forbiddenWord over its complete sixteen-element index type."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cardinality"), DeclarationHandle.Create(Prefix + "forbidden_card"),
                H("Exact removal cardinality"), StatementSource.FromAuthor(Disp(new Formula.Relation(
                    Call("card", Call("forbiddenProfiles")), FormulaRelationOperator.Equal, D(1,6)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The rank of offset 1 at the middle position recovers the orientation: it is zero forward and one after reflection. After undoing reflection, ranks at coordinates 2, 1 and 0 of positions 0, 1 and 2 respectively recover the three exterior-order bits. This word-level injection proves that precisely sixteen ranking profiles are removed, without enumerating all pairs of profiles."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("count"), DeclarationHandle.Create(Prefix + "count_three_bound"),
                H("Three-site count bound"), StatementSource.FromAuthor(Disp(new Formula.Relation(
                    Call("count", D(3)), FormulaRelationOperator.LessThanOrEqual, D(1,3,8,0,8)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The map sends each existentially certified word to its underlying ranking word in the complement of the sixteen forbidden profiles. It is injective on words. The whole space has 24 cubed = 13824 elements; complement cardinality gives 13824 minus 16 = 13808. This bind-only numeric reduction is consumed by GrowthTransfer.result to obtain strict exponential growth below 24. It has no standalone first-freeze or external-problem credit. Supplier model credit remains The Formal Conjectures Authors under Apache-2.0; this module imports the saved certificate development without changing the supplier model."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Open, F.Id(name), Colon, type, Close, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Open, F.Id(name), Colon, type, Close, Comma, Sp, body);
}
