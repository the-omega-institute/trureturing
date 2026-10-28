using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class BourasA363102PrimeMultiplicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/bouras2023continuedfractionmultiplicity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every occurring prime has two or three indices in Bouras A363102.",
        H("Two or Three Prime Occurrences in Bouras A363102"),
        Blocks(
            Paragraph(Text("The continued fraction is rational, and Rat.den gives its positive reduced denominator. "
                + "Indices are natural numbers, and occurrences are counted only for n at least three. "
                + "Set.ncard is zero on infinite sets; the proof constructs either a pair or a triple.")),
            Node("a", "The continued-fraction denominator", SequenceFormula(),
                "OEIS A363102, NAME (unpaginated): \"Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-2))))).\" "
                + "The sequence is Rat.den of K n (-2), where K is the reciprocal right-folded fraction. Its offset is n = 3.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Bouras's Conjecture 2", Disp(Equal(Q("BourasA363102", "claim"), Parenthesized(ClaimBody()))),
                "OEIS A363102, COMMENTS, Conjecture 2 (unpaginated): \"Conjecture 2: All prime numbers appear either twice (same as A356247 and A357127) or three times.\" "
                + "The quantifier ranges over prime values that occur in the sequence. This reading follows the comparison with the other sequences; "
                + "it does not assert that every prime occurs. The set includes every index at least three giving the chosen prime.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Two or three occurrences", Disp(ClaimBody()),
                "The roots of n squared equal to two in ZMod p give exactly two indices below p, paired by n mapping to p-n. "
                + "Every further index must satisfy n squared equal to twice p squared plus two, which permits at most one natural index. "
                + "Thus the full occurrence set is a pair or a triple. The converse from a solution of that equation to a further occurrence is not asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bouras-a363102"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("bouras102-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula A(Formula n) => App(Q("BourasA363102", "a"), n);
    private static Formula AtLeastThree(Formula n) => new Formula.Relation(D(3), FormulaRelationOperator.LessThanOrEqual, n);
    private static Formula SequenceFormula() => Disp(All("n", NatType(), Equal(A(V("n")),
        App(Q("Rat", "den"), App(Q("BourasA356360", "K"), V("n"), Seq(Minus, D(2)))))));
    private static Formula Occurrences() => Seq(OpenBrace, V("n"), Colon, Sp, NatType(), Sp, Mid, Sp,
        And(AtLeastThree(V("n")), Equal(A(V("n")), V("p"))), CloseBrace);
    private static Formula ClaimBody()
    {
        var p = V("p");
        var cardinality = App(Q("Set", "ncard"), Occurrences());
        return All("p", NatType(), Imp(App(Q("Nat", "Prime"), p),
            Imp(Some("n", NatType(), And(AtLeastThree(V("n")), Equal(A(V("n")), p))),
                new Formula.Logic(Equal(cardinality, D(2)), FormulaLogicOperator.Or, Equal(cardinality, D(3))))));
    }
}
