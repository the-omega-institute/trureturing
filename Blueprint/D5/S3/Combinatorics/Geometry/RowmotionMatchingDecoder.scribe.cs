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
                All("m", F.Id("Nat"), All("M", Call("NCMatching", F.Id("m")), All("k", Call("Fin", F.Id("m")),
                    Iff(Call("IsOpening", F.Id("M"), F.Id("k")),
                        Less(F.Id("k"), Call("partner", F.Id("M"), F.Id("k"))))))),
                "The smaller endpoint opens its pair. This is a property of the actual partner permutation."),
            Node("partner_eq_of_openings", "Opening data recover every matched pair", DescribeRole.Theorem,
                All("m", F.Id("Nat"), All("M", Call("NCMatching", F.Id("m")), All("Q", Call("NCMatching", F.Id("m")),
                    Imp(All("k", Call("Fin", F.Id("m")), Iff(Call("IsOpening", F.Id("M"), F.Id("k")), Call("IsOpening", F.Id("Q"), F.Id("k")))),
                        Equal(Call("partner", F.Id("M")), Call("partner", F.Id("Q"))))))),
                "For every frontier size and both noncrossing matchings on that same ordered frontier, agreement of the opening predicate forces equality of the full partner permutations. The proof uses the existing interior_closed theorem and induction on closing indices. If two partners of a closing differed, the intermediate opening would have closed earlier in one matching, contradicting agreement already established there. This is the pair-recovery fact used in the repository's rowmotion decoder argument."),
            Paragraph(Text("For each n, CircularMatching(n) consists of an increasing embedding of six ranks into Fin(n+4), the existing NCMatching(6) partner permutation, and pairwise circular separation at least eight. Native site q is source site q+1. Ordinary means that every site has native value below n+2, excluding source sites n+3 and n+4. In endpoint data, a and b take values in Fin n, both are strictly decreasing, a(r) is at most b(r), and the indexed sites are a(0),a(1),a(2),b(0)+2,b(1)+2,b(2)+2. Every indexed pair must pass the circular distance test. Equality of occurrences fails it.")),
            Paragraph(Text("openingRanks and closingRanks sort the smaller and larger actual partners separately. start and finish transport those ranks to selected sites. The native decoder puts p in the decoded state exactly when start(M,reverse(row(p))) is at most column(p) and column(p)+2 is at most finish(M,reverse(row(p))). This is source row 4-j equal to [s_j,t_j-2], under the coordinate translation. The rank-paired endpoints are not required to be partners. endpointState is the actual union of its three intervals, and Separated(I) means existence of separated endpoint data with that exact actual set. No assumption that either family is nonempty is made.")),
            Node("ordinary_decoder", "The ordinary decoder bijection", DescribeRole.Theorem,
                All("n", F.Id("Nat"), And(Call("Injective", Call("decode", F.Id("n"))),
                    And(All("M", Call("OrdinaryMatching", F.Id("n")),
                            And(Call("Separated", Call("decode", F.Id("M"))), Call("OrdConnected", Call("decode", F.Id("M"))))),
                        All("I", Call("Set", Call("Product", Call("Fin", D(3)), Call("Fin", F.Id("n")))),
                            Imp(Call("Separated", F.Id("I")), Call("ExistsDecoder", F.Id("n"), F.Id("I"))))))),
                "For every n, including the small parameters with empty families, decode is injective on the whole ordinary matching carrier, its values are separated interval-closed states, and every separated actual state is decoded by an ordinary matching. ExistsDecoder(n,I) means there exists M in OrdinaryMatching(n) with decode(M)=I. Injectivity recovers both the ordered site embedding and the complete actual partner permutation. The constructive inverse covers all five parenthesis orders while retaining independently sorted openings and closings. The result is the ordinary-bijection clause of the repository source's Theorem 2.5. It does not assert the decoder at nonordinary cuts, the literal toggle transition, or return reflection."))));

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
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
