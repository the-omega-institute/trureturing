using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class RowmotionMatchingDecoderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/RowmotionMatchingDecoder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cut noncrossing matching is determined by which endpoints open its pairs.",
        H("Recovery of actual noncrossing partners"),
        Blocks(
            Paragraph(Text("NCMatching(m) is the existing fixed-point-free involutive permutation of Fin m, with no alternating pairs. An opening is an endpoint k strictly smaller than its actual partner. The domain includes m=0; no existence or nonemptiness assumption is added.")),
            Node("IsOpening", "An opening at a fixed cut", DescribeRole.Definition,
                All("m", Id("Nat"), All("M", Call("NCMatching", Id("m")), All("k", Call("Fin", Id("m")),
                    Iff(Call("IsOpening", Id("M"), Id("k")),
                        Less(Id("k"), Call("partner", Id("M"), Id("k"))))))),
                "The smaller endpoint opens its pair. This is a property of the actual partner permutation."),
            Node("partner_eq_of_openings", "Opening data recover every matched pair", DescribeRole.Theorem,
                All("m", Id("Nat"), All("M", Call("NCMatching", Id("m")), All("Q", Call("NCMatching", Id("m")),
                    Imp(All("k", Call("Fin", Id("m")), Iff(Call("IsOpening", Id("M"), Id("k")), Call("IsOpening", Id("Q"), Id("k")))),
                        Equal(Call("partner", Id("M")), Call("partner", Id("Q"))))))),
                "For every frontier size and both noncrossing matchings on that same ordered frontier, agreement of the opening predicate forces equality of the full partner permutations. The proof uses the existing interior_closed theorem and induction on closing indices. If two partners of a closing differed, the intermediate opening would have closed earlier in one matching, contradicting agreement already established there. This is the pair-recovery fact used in the repository's rowmotion decoder argument. It does not assert a literal toggle transition or any return-time conclusion.")))));

    private static DocumentBlock Node(string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("rowmotion-matching-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Call(string name, params Formula[] arguments) => Seq(F.Id(name), Open,
        Seq(arguments.SelectMany((value, index) => index == 0 ? new[] { value } : new[] { Comma, Sp, value }).ToArray()), Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
