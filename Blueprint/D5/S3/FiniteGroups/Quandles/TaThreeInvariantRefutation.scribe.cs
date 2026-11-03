using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Quandles;

internal sealed class TaThreeInvariantRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/ta2025goodinvolutions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two finite nonabelian groups have equal order, center order and class number, but different complete counts of good involutions.",
        H("The three invariants do not determine the good-involution count"),
        Blocks(
            Node("Gr", "Two native semidirect products",
                "Gr(false) and Gr(true) are Mathlib semidirect products (Z/16) ⋊ (Z/4). "
                + "The action generator multiplies the additive first coordinate by 5 or 7, "
                + "respectively. Multiplication is (i,j)(k,l)=(i+r^j k,j+l). "
                + "The native group structure proves the group laws; no multiplication-table "
                + "axioms are introduced.", DescribeRole.Definition),
            Node("goodCount", "Counts of all whole-group good maps",
                "goodCount(G) is the cardinality of the existing repository Good subtype on "
                + "Finset.univ. Its maps are involutions commuting with each s_x, and "
                + "s_(rho(x)) is both a left and right inverse of s_x. "
                + "Here s_x(y)=xyx^-1. Counts are of functions, without quotienting by "
                + "quandle isomorphism.", DescribeRole.Definition),
            Node("good_counts", "Both complete counts",
                "The complete central-label bijection and independent-block product prove "
                + "goodCount(Gr(false))=8847360 and goodCount(Gr(true))=2160000. "
                + "For r=5 the blocks are one all-one 4-by-4 block, six forced paired "
                + "2-by-2 blocks of off-diagonal weight four, and three all-two 2-by-2 blocks. "
                + "Their factors are 10, 4 and 6, yielding 10*4^6*6^3. For r=7 the blocks "
                + "are four all-one 4-by-4 blocks and three all-two 2-by-2 blocks, yielding "
                + "10^4*6^3. Every conjugacy class and central destination is checked against "
                + "the actual native groups. Each local factor enumerates at most 4^4 labels; "
                + "the bijection supplies completeness for all good maps.", DescribeRole.Theorem),
            Node("claim", "Ta's exact three-invariant determination question",
                "Ta, Problem 11.6: Let G be a finite nonabelian group of order n. Is the "
                + "number of good involutions of Conj G completely determined by n, the "
                + "order of the center Z(G), and the class number k(G) of G? If so, is there "
                + "an exact formula to compute this number? The formal claim quantifies "
                + "over two finite groups, explicitly requires each to be nonabelian, and "
                + "asserts equality of their whole-group good-map counts whenever their "
                + "three invariant cardinalities agree. This is the determination part of "
                + "the original question. Refuting it also rules out a formula depending "
                + "only on those three numbers.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ta116-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The determination fails"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Both native groups are nonabelian and have invariant triple (64,4,22). "
                    + "The center enumerations cover every central element. The complete "
                    + "partitions are equivalent to Mathlib ConjClasses, so 22 is the actual "
                    + "class number. Their complete good-map counts differ. The proof "
                    + "therefore negates the original universal determination assertion. "
                    + "Ta Theorem 6.7 supplies the attributed central-function characterization; "
                    + "our label z is the inverse of Ta's zeta. The result concerns whole "
                    + "conjugation quandles, not a knot classification. The inspected versioned "
                    + "primary literature did not identify a prior answer to 11.6; this bounded "
                    + "check establishes neither worldwide priority nor uniqueness."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ta-2025-problem-11-6-three-invariant-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("ta116-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            Statement(declaration), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
    private static StatementSource Statement(string name) => name == "good_counts"
        ? StatementSource.FromAuthor(F.Disp(new Formula.Logic(
            new Formula.Relation(Call("goodCount", Call("Gr", F.Id("false"))),
                FormulaRelationOperator.Equal, new Formula.Number(8847360)),
            FormulaLogicOperator.And,
            new Formula.Relation(Call("goodCount", Call("Gr", F.Id("true"))),
                FormulaRelationOperator.Equal, new Formula.Number(2160000)))))
        : StatementSource.WithoutFormula();

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Seq(F.Operatorname, F.Grp(F.Id(name))), [.. arguments]);
}
