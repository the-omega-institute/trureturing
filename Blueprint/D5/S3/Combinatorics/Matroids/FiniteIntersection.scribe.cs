using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class FiniteIntersectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two matroids on a common finite ground have an attained intersection min-max equality.",
        H("Finite matroid intersection"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-matroid-intersection"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/FiniteIntersection.finite_matroid_intersection"),
            H("A common independent set and an attaining rank cut"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/FiniteGeometry/schrijver2017coursecombinatorialoptimization")),
            Blocks(
                Paragraph(Text(
                    "Let alpha be any type in an arbitrary universe u, E a finite subset of alpha, and M1 and M2 matroids whose grounds both equal E. There are sets I and X, both contained in E, such that the same I is independent in both matroids and its cardinality equals the rank of X in M1 plus the rank of E minus X in M2. For every set J independent in both matroids and every set Y in alpha, the cardinality of J is at most the rank of Y in M1 plus the rank of E minus Y in M2.")),
                Paragraph(Text(
                    "Cardinality is Set.ncard and rank is ENat.toNat of the native Matroid.eRk. Finiteness of the common ground makes every rank finite, even when alpha is infinite. Empty grounds, loops and rank zero are included. No representation over a field or positivity assumption is required. Although the attaining X lies in E, the upper bound permits every Y; it therefore also holds for every Y contained in E.")),
                Paragraph(Text(
                    "Theorem 10.9 on page 188 of Schrijver's course states the maximum cardinality of a common independent set as the minimum of the two-rank cut sum. The finite-ground definition is on page 173. The existential equality and the universal bound exhibit both attained extrema: use the attaining cut to bound every common independent set, and use the attaining independent set to bound every cut sum from below.")),
                Paragraph(Text(
                    "The proof proceeds by induction on the ground cardinality. If every element is a loop in at least one matroid, the empty independent set and the loop set of the first matroid give equality. Otherwise a common nonloop gives smaller deletion and contraction pairs. Their two common-independent certificates combine with submodularity in each matroid; failure of attainment would force the combined cut ranks to exceed the submodular upper bound. Splitting a common independent set at an arbitrary cut gives the universal inequality."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var statement = And(Attaining(), UpperBound());
        statement = Imp(Equal(Ground("M2"), V("E")), statement);
        statement = Imp(Equal(Ground("M1"), V("E")), statement);
        statement = All("M2", MatroidType, statement);
        statement = All("M1", MatroidType, statement);
        statement = Imp(A(Q("Set", "Finite"), V("E")), statement);
        statement = All("E", SetType, statement);
        return All("alpha", new Formula.Subscript(V("Type"), V("u")), statement);
    }

    private static Formula Attaining()
    {
        var equality = Equal(Card("I"), RankSum("X"));
        var clauses = And(Subset("I", "E"), And(Subset("X", "E"),
            And(Indep("M1", "I"), And(Indep("M2", "I"), equality))));
        return Some("I", SetType, Some("X", SetType, clauses));
    }

    private static Formula UpperBound() => All("J", SetType, All("Y", SetType,
        Imp(Indep("M1", "J"), Imp(Indep("M2", "J"),
            new Formula.Relation(Card("J"), FormulaRelationOperator.LessThanOrEqual, RankSum("Y"))))));

    private static Formula RankSum(string cut) => Seq(
        Rank("M1", V(cut)), Sp, Plus, Sp,
        Rank("M2", Parenthesized(Seq(V("E"), Sp, Setminus, Sp, V(cut)))));
    private static Formula Rank(string matroid, Formula set) =>
        A(Q("ENat", "toNat"), A(Q("Matroid", "eRk"), V(matroid), set));
    private static Formula Ground(string matroid) => A(Q("Matroid", "E"), V(matroid));
    private static Formula Indep(string matroid, string set) => A(Q("Matroid", "Indep"), V(matroid), V(set));
    private static Formula Card(string set) => A(Q("Set", "ncard"), V(set));
    private static Formula Subset(string a, string b) =>
        new Formula.Relation(V(a), FormulaRelationOperator.SubsetOf, V(b));
    private static Formula SetType => A(V("Set"), V("alpha"));
    private static Formula MatroidType => A(V("Matroid"), V("alpha"));
    private static Formula V(string name) => F.Id(name);
    private static Formula A(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

}
