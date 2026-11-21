using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class ShlykConvexityIndexDocument : IScribeDocumentDefinition
{
    private const string Theorem =
        "D5/S3/Combinatorics/Partitions/ShlykConvexityIndex.shlyk_eventual_convexity_index";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Convexity/shlyk2026partitionconvexity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every integer index at least two occurs at every sufficiently large partition total.",
        H("Eventual existence of every partition convexity index"), Blocks(
            Describe.Lean(DescribeId.Create("shlyk-eventual-convexity-index"), DeclarationHandle.Create(Theorem),
                H("Exact convexity index at all sufficiently large totals"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Shlyk's 2026 paper formulates eventual existence in Section 1.2 and restates it in Section 3.1. The first sentence of Conjecture 1 in the 2018 preprint gives the strict threshold. An index s in Fin n denotes the positive part size s.val + 1. The lower bound ranges over all finite families of distinct other partitions with arbitrary positive real weights. Repeated summands can be combined by adding their weights.")),
                    Paragraph(Text("The construction starts with nonnegative integer equations in paired coordinates. The a-coordinates sum to k and have a common residue modulo k. A nonzero residue forces them all to equal one. In residue zero, exactly one equals k and the others vanish. The paired and congruence equations determine all remaining coordinates. Distinct matrix columns give distinct positive part sizes. A common leading radix digit first bounds the total multiplicity in a putative partition. That bound puts every row sum below the radix, so digit uniqueness recovers the full system without assuming its equations.")),
                    Paragraph(Text("Positivity confines each summand to the center's part sizes. On those sizes the integer solutions are the center and the k alternatives. For each a-coordinate, only its own alternative can contribute positively, so all k alternatives are required. Their equal-weight average gives the center. If the encoded center has total m and n exceeds 2m, adjoining the part n minus m preserves the index. Every partition of n has at most one copy of this part. Its center coordinate is one, so every positively weighted summand has one copy, and deleting it recovers a representation of the same cardinality and weights."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("shlyk-convexity-index-eventual-existence"), ResolutionKind.Proved))
        ), []));

    private static Formula Statement()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var threshold = F.Id("N");
        var x = F.Id("x");

        var attained = RepresentationFamily(k, n, x, "y", "w", null);
        var lowerBound = All("r", Natural(),
            RepresentationFamily(F.Id("r"), n, x, "z", "v", Le(k, F.Id("r"))));

        return All("k", Natural(), Imp(Le(D(2), k),
            Some("N", Natural(), All("n", Natural(), Imp(Lt(threshold, n),
                Some("x", Arrow(Fin(n), Natural()), And(Partition(x, n), And(attained, lowerBound))))))));
    }

    private static Formula RepresentationFamily(
        Formula length, Formula n, Formula x, string familyName, string weightName, Formula? conclusion)
    {
        var y = F.Id(familyName);
        var weights = F.Id(weightName);
        var fin = Fin(length);
        var j = F.Id("j");
        var s = F.Id("s");
        var part = Apply(y, j);
        var coefficient = Apply(weights, j);
        Formula[] clauses =
        [
            All("i", fin, All("j", fin, Imp(Equal(Apply(y, F.Id("i")), part), Equal(F.Id("i"), j)))),
            All("j", fin, NotEqual(part, x)),
            All("j", fin, Partition(part, n)),
            All("j", fin, Lt(D(0), coefficient)),
            Equal(SumOver("j", fin, coefficient), D(1)),
            All("s", Fin(n), Equal(RealCast(Apply(x, s)),
                SumOver("j", fin, Mul(coefficient, RealCast(Apply(part, s))))))
        ];

        var binder = conclusion is null ? FormulaQuantifier.Exists : FormulaQuantifier.ForAll;
        var body = conclusion ?? clauses[^1];
        for (var index = clauses.Length - (conclusion is null ? 2 : 1); index >= 0; index--)
            body = conclusion is null ? And(clauses[index], body) : Imp(clauses[index], body);

        return Bind(binder, familyName, Arrow(fin, Arrow(Fin(n), Natural())),
            Bind(binder, weightName, Arrow(fin, Real()), body));
    }

    private static Formula Partition(Formula partition, Formula n)
    {
        var s = F.Id("s");
        var size = new Formula.Binary(Apply(Named("val"), s), FormulaBinaryOperator.Add, D(1));
        return Equal(SumOver("s", Fin(n), Mul(Par(size), Apply(partition, s))), n);
    }

    private static Formula SumOver(string name, Formula type, Formula value) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id(name), Colon, Sp, type)), Sp, Par(value));
    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, Par(body));
    private static Formula All(string name, Formula type, Formula body) => Bind(FormulaQuantifier.ForAll, name, type, body);
    private static Formula Some(string name, Formula type, Formula body) => Bind(FormulaQuantifier.Exists, name, type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Apply(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Fin(Formula n) => Apply(Named("Fin"), n);
    private static Formula Natural() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula RealCast(Formula value) => Par(Seq(value, Colon, Sp, Real()));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
}
