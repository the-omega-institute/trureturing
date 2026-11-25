using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Dice;

internal sealed class RankingProfileRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Dice/RankingProfileRealization.";
    private const string Slug = "bozoki-csato-temesi-2026-ranking-profile";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/bozokicsatotemesi2026dice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite cubic criterion for the six strict ranking probabilities of three independent real variables.",
        H("Realization of a complete ranking profile"),
        Blocks(
            Describe.Lean(DescribeId.Create("ranking-profile-order"),
                DeclarationHandle.Create(Prefix + "rankOrder"), H("Order of the six coordinates"),
                StatementSource.FromAuthor(F.Disp(OrderFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Roles 0, 1 and 2 denote X, Y and Z. Each row lists the roles from largest to smallest. The six rows follow Equation (7) in the order XYZ, XZY, YXZ, YZX, ZXY, ZYX."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ranking-profile-real"),
                DeclarationHandle.Create(Prefix + "realRankProfile"), H("Strict ranking probabilities"),
                StatementSource.FromAuthor(F.Disp(RealProfileFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The coordinate is the real value of the measure of the corresponding strict ordering event. The two strict inequalities exclude all ties. In the theorem the measure is a probability measure and the coordinate functions are measurable."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ranking-profile-cubic-test"),
                DeclarationHandle.Create(Prefix + "finiteTest15"), H("The fifteen-label cubic test"),
                StatementSource.FromAuthor(F.Disp(FiniteTestFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("There are three weight vectors, each on the same fifteen ordered labels. For each role the weights are nonnegative, sum to one, and have at most five positive entries. All six equations are unconditional strict ranking probabilities."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ranking-profile-problem-five"),
                DeclarationHandle.Create(Prefix + "problem_five"), H("Exact criterion for Problem 5"),
                StatementSource.FromAuthor(F.Disp(ProblemFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every simplex profile, including the boundary, necessity applies on every measurable probability space. Sum one makes the three real values pairwise distinct almost surely. Separately quantize the variables with role-specific offsets. Measurability preserves independence, the offsets give disjoint finite ranges, and bounded convergence gives convergence of the six strict ranking probabilities.")),
                    Paragraph(Text("For finite disjoint supports, hold two marginal laws fixed. Their two strict comparison probabilities are the sums of two complementary blocks of three coordinates as the third variable varies. Four coordinates therefore determine the other two. Carathéodory compresses the varying marginal to at most five original support values. Apply this to each role in turn and relabel the union in increasing order. The sparse marginal simplexes are finite unions of compact faces, so the continuous cubic image is closed and contains the limiting profile.")),
                    Paragraph(Text("For sufficiency take the product law on triples of ordered labels. Evaluating its three coordinates as reals gives independent measurable variables, and summing the product masses of all strictly ordered triples gives exactly the six cubic sums."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create(Slug), ResolutionKind.Proved))),
        []));

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Roles => Fin(3);
    private static Formula Labels => Fin(15);
    private static Formula Profile => Arrow(Fin(6), Real);
    private static Formula Fin(int n) => Call("Fin", Num(n));
    private static Formula Arrow(Formula a, Formula b) =>
        F.Seq(F.Open, a, F.Sp, F.To, F.Sp, b, F.Close);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula And(params Formula[] formulas) =>
        formulas.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Test(Formula v) =>
        new Formula.Relation(v, FormulaRelationOperator.MemberOf, Id("finiteTest15"));
    private static Formula Sum(Formula index, Formula body) =>
        F.Seq(new Formula.Subscript(F.Sum, index), F.Sp, F.Open, body, F.Close);
    private static Formula Index(string name, Formula domain) => F.Seq(Id(name), F.Colon, domain);
    private static Formula Role(Formula t, int position) => Call("rankOrder", t, Num(position));
    private static Formula Values(Formula space) => Arrow(Roles, Arrow(space, Real));
    private static Formula IsMeasurable(Formula x) => All(Call("Measurable", At(x, Id("i"))), B("i", Roles));

    private static Formula Triple(int a, int b, int c) =>
        F.Seq(F.Open, Num(a), F.Comma, Num(b), F.Comma, Num(c), F.Close);

    private static Formula OrderFormula() =>
        Equal(F.Seq(Call("rankOrder", Num(0)), F.Comma, F.Sp, Call("rankOrder", Num(1)), F.Comma, F.Sp,
            Call("rankOrder", Num(2)), F.Comma, F.Sp, Call("rankOrder", Num(3)), F.Comma, F.Sp,
            Call("rankOrder", Num(4)), F.Comma, F.Sp, Call("rankOrder", Num(5))),
            F.Seq(Triple(0, 1, 2), F.Comma, F.Sp, Triple(0, 2, 1), F.Comma, F.Sp, Triple(1, 0, 2),
                F.Comma, F.Sp, Triple(1, 2, 0), F.Comma, F.Sp, Triple(2, 0, 1), F.Comma, F.Sp, Triple(2, 1, 0)));

    private static Formula RealProfileFormula()
    {
        Formula space = Id("Omega"), x = Id("X"), mu = Id("mu"), t = Id("t"), omega = Id("omega");
        Formula Value(int position) => At(x, Role(t, position), omega);
        Formula order = And(Lt(Value(1), Value(0)), Lt(Value(2), Value(1)));
        Formula rankEvent = F.Seq(F.OpenBrace, omega, F.Sp, F.Mid, F.Sp, order, F.CloseBrace);
        return All(Equal(Call("realRankProfile", mu, x, t), Call("measureReal", mu, rankEvent)),
            B("Omega", Id("Type")), B("m", Call("MeasurableSpace", space)),
            B("mu", Call("Measure", space)), B("X", Values(space)), B("t", Fin(6)));
    }

    private static Formula FiniteTestFormula()
    {
        Formula v = Id("v"), p = Id("p"), r = Id("r"), t = Id("t");
        Formula i = Id("i"), j = Id("j"), k = Id("k");
        Formula positive = F.Seq(F.OpenBrace, i, F.Sp, F.Mid, F.Sp, Lt(Num(0), At(p, r, i)), F.CloseBrace);
        Formula weights = All(And(
            All(Le(Num(0), At(p, r, i)), B("i", Labels)),
            Equal(Sum(Index("i", Labels), At(p, r, i)), Num(1)),
            Le(Call("card", positive), Num(5))), B("r", Roles));
        Formula monomial = Multiply(Multiply(At(p, Role(t, 0), i), At(p, Role(t, 1), j)), At(p, Role(t, 2), k));
        Formula orderedIndices = F.Seq(Index("i", Labels), F.Comma, Index("j", Labels), F.Comma,
            Index("k", Labels), F.Comma, F.Sp, Lt(k, j), F.Comma, Lt(j, i));
        Formula cubic = All(Equal(At(v, t), Sum(orderedIndices, monomial)), B("t", Fin(6)));
        return All(Iff(Test(v), Exists(And(weights, cubic), B("p", Arrow(Roles, Arrow(Labels, Real))))),
            B("v", Profile));
    }

    private static Formula ProblemFormula()
    {
        Formula space = Id("Omega"), x = Id("X"), mu = Id("mu"), v = Id("v");
        Formula simplex = And(All(Le(Num(0), At(v, Id("t"))), B("t", Fin(6))),
            Equal(Sum(Index("t", Fin(6)), At(v, Id("t"))), Num(1)));
        Formula probability = Call("IsProbabilityMeasure", mu);
        Formula realization = And(IsMeasurable(x), Call("iIndepFun", x, mu), Equal(Call("realRankProfile", mu, x), v));
        Formula forward = All(Imp(And(probability, realization), Test(v)), B("Omega", Id("Type")),
            B("m", Call("MeasurableSpace", space)), B("mu", Call("Measure", space)), B("X", Values(space)));
        Formula triples = Arrow(Roles, Labels);
        Formula converse = Imp(Test(v), Exists(And(probability, realization),
            B("mu", Call("Measure", triples)), B("X", Values(triples))));
        return All(Imp(simplex, And(forward, converse)), B("v", Profile));
    }
}
