using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class LeePositiveLatinSquareTypeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType.";
    private static readonly LibraryNoteRef Lee =
        LibraryNoteRef.Create("D5/L/GraphInvariants/lee2026assignmentpolytopes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary symmetric rank-threshold graph in dimension seven fails the positive Latin-square-type valency.",
        H("Lee’s symmetric rank-threshold fusion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("leepositivelatinsquaretype-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The positive Latin-square-type claim"), StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Lee),
                Blocks(Paragraph(Text(
                    "Lee’s §6.3 ends with “whether the relation ‘rank at least d’ is of Latin-square type for all such m we leave open.” "
                    + "The field K ranges over all finite fields, including both characteristics and nonprime prime powers. "
                    + "The vertex type V consists of all symmetric m by m matrices over K. In the rank graph G, distinct A and B "
                    + "are adjacent exactly when the rank over K of A − B is at least d. This fuses every rank/type class above "
                    + "or at the threshold. The neighbor set is taken in this full graph. "
                    + "The real sum of f over V vanishes exactly when f is orthogonal to the all-ones vector. "
                    + "The biconditional gives the exact set of restricted eigenvalues from §2.3. Both n − t and −t are evaluated over the reals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("leepositivelatinsquaretype-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation at q = 2, m = 7, d = 5"), StatementSource.FromAuthor(Disp(new Formula.Not(Name("claim")))),
                AssessedProvenance.FromRepo(Lee),
                Blocks(Paragraph(Text(
                    "The 28 upper-triangular entries give 2²⁸ vertices, so n must be 16,384. "
                    + "Simultaneous reindexing by (0 1 2)(3 4 5) acts on the actual zero-neighbor set with order three. "
                    + "The ten classes of ordered index pairs under reindexing and transpose give exactly 1,024 fixed symmetric matrices. "
                    + "Decoding all 128 binary vectors identifies the parity test with actual kernel membership. "
                    + "Rank-nullity identifies rank at least five with kernel cardinality at most four. "
                    + "The kernel checks 32 chunks of 32 masks, and the equivalence with accepted masks gives 770 fixed neighbors. "
                    + "The orbit congruence gives degree 2 modulo 3, whereas every t(16,384 − 1) is divisible by 3."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula App(string name, params Formula[] args) => new Formula.Apply(Name(name), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(V("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula If(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Exactly(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Positive(Formula n) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n);
    private static Formula Instance(Formula type) => Seq(OpenBracket, type, CloseBracket);
    private static Formula Congruent(Formula m, byte r) => Seq(m, Sp, Equiv, Sp, D(r), Sp, Pmod, Grp(D(4)));
    private static Formula SumOver(Formula index, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(index, Sp, InMacro, Sp, domain)), Sp, body);
    private static Formula Let(Formula variable, Formula value, Formula body) =>
        Seq(Name("let"), Sp, variable, Sp, Colon, Eq, Sp, value, Sp, Name("in"), Sp, body);

    private static Formula ClaimFormula()
    {
        Formula field = V("K"), m = V("m"), d = V("d"), vertices = V("V"), graph = V("G");
        Formula a = V("A"), b = V("B"), n = V("n"), t = V("t"), e = V("lambda"), f = V("f");
        var cases = Or(
            And(Congruent(m, 3), Equal(d, new Formula.Fraction(Add(m, D(3)), D(2)))),
            And(Congruent(m, 0), Equal(d, new Formula.Fraction(Add(m, D(2)), D(2)))));
        var evalA = new Formula.Apply(f, [a]);
        var evalB = new Formula.Apply(f, [b]);
        var nReal = Par(Seq(n, Colon, Sp, RealType()));
        var tReal = Par(Seq(t, Colon, Sp, RealType()));
        var restricted = All("lambda", RealType(), Exactly(
            Or(Equal(e, Subtract(nReal, tReal)), Equal(e, Seq(Minus, tReal))),
            Some("f", new Formula.TypeArrow(vertices, RealType()), And(
                NotEqual(f, D(0)), And(Equal(SumOver(a, vertices, evalA), D(0)),
                    All("A", vertices, Equal(SumOver(b, App("neighborFinset", graph, a), evalB),
                        Multiply(e, evalA))))))));
        var degrees = All("A", vertices, Equal(App("degree", graph, a), Multiply(t, Par(Subtract(n, D(1))))));
        var positiveType = Some("n", NatType(), Some("t", NatType(), And(Positive(n), And(Positive(t),
            And(Equal(App("card", vertices), new Formula.Power(n, D(2))), And(degrees, restricted))))));
        var graphType = Let(vertices, App("SymmetricMatrix", field, m),
            Let(graph, App("rankGraph", field, m, d), positiveType));
        var body = All("K", Name("Type"), Seq(Instance(App("Field", field)), Sp,
            Instance(App("Finite", field)), Sp, All("m", NatType(), All("d", NatType(),
                If(Positive(m), If(cases, graphType))))));
        return Exactly(Name("claim"), body);
    }
}
