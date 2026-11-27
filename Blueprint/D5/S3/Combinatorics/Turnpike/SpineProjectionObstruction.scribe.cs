using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Turnpike;

internal sealed class SpineProjectionObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Turnpike/SpineProjectionObstruction";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Combinatorics/elder2026turnpike");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A realizable seven-point distance multiset has a spine-feasible assignment with no full triangle coupling.",
        H("Full and endpoint-spine triangle projections differ"),
        Blocks(
            Paragraph(Text("The numerical relation and linear constraints are Proposition 10 and System 11 of Elder, Marçais and Kingsford. Each interval and each numerical label is retained. The comparison fixes the entire assignment array P. The two existential coupling arrays are independent; there is no requirement to extend a chosen spine array, and no common joint distribution over all intervals is assumed.")),
            Paragraph(Text("Publication indices run from 1 to n and 1 to d. In Lean, vertex i and label q are represented by i−1 in Fin n and q−1 in Fin d. Thus I consists of ordered pairs i<j, Delta consists of ordered triples i<j<k, and S consists of triples (1,j,k) with 1<j<k. No containment pruning, endpoint fixing, or presolve restrictions are present.")),
            Paragraph(Text("Write R for the complete ordered numerical two-partition relation:")),
            DisplayMath(RelationBody()),
            Paragraph(Text("For H equal to Delta or S, write E(H,P) for the following explicit existential system. All sums over R include its entire guarded relation; an empty sum is zero. The components of r are a,b,c, assigned respectively to ij,jk,ik.")),
            DisplayMath(Equal(App(Q("E"), X("H"), X("P")), FeasibleBody(X("H")))),
            Describe.Lean(DescribeId.Create("turnpike-spine-projection-claim"), DeclarationHandle.Create(Module + ".claim"),
                H("The universal projection equality"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Q("claim"), Prop()), Par(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed assertion includes every admissibility premise. Realizability by a ruler is not assumed. Equality of the two feasible projections is equivalent to the displayed pointwise equivalence for every entire P array. This is the precise fixed-assignment interpretation studied here; scalar expected differences form a weaker observation."))), DescribeRole.Definition),
            Def("y", "turnpike-spine-values", "Distinct distance values", Vec(18,16,14,13,12,11,10,9,8,7,6,5,4,3,2,1)),
            Def("μ", "turnpike-spine-counts", "Positive multiplicities", Vec(1,1,1,1,1,1,1,2,2,1,1,2,2,2,1,1)),
            Def("ruler", "turnpike-spine-ruler", "An actual realizing ruler", Vec(0,4,7,8,13,16,18)),
            Paragraph(Text("Realizability requires strict increase, a label for every actual interval difference, and the exact occurrence count of every label. These three conditions are satisfied by the displayed x, y and mu:")),
            DisplayMath(RealizesBody()),
            Describe.Lean(DescribeId.Create("turnpike-spine-assignment"), DeclarationHandle.Create(Module + ".assignment"),
                H("The fractional assignment"), StatementSource.FromAuthor(Disp(Equal(App(X("P"),X("e"),X("q")),
                    new Formula.Fraction(Add(App(Q("indicator"),Equal(X("q"),App(X("L"),X("e")))),App(Q("indicator"),Equal(X("q"),App(X("U"),X("e"))))),D(2))))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("The indicator of a true equality is one and otherwise zero. In the following complete list, ij:(u,v) means that L and U are the labels of the numerical values u and v: 12:(4,2), 13:(7,5), 14:(8,10), 15:(13,11), 16:(16,14), 17:(18,18), 23:(1,5), 24:(4,8), 25:(9,9), 26:(12,12), 27:(14,16), 34:(3,3), 35:(6,6), 36:(9,9), 37:(11,13), 45:(5,1), 46:(8,4), 47:(10,8), 56:(3,3), 57:(5,7), 67:(2,4). Equal entries give a deterministic row.")),
                    Paragraph(Text("The reflection of x is z=(0,2,5,10,11,14,18). Averaging their interval-label assignments gives the same column multiplicities. The displayed P differs only by replacing row 23 from the point mass at 3 with the half-mixture at 1 and 5, and replacing row 34 in the opposite direction. These two changes cancel separately in every column. Each row remains a probability distribution."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("turnpike-spine-projection-result"), DeclarationHandle.Create(Module + ".result"),
                H("A literal refutation of the universal equality"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Par(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("For each spine triangle, put half-mass at each of these two numerical triples, adding masses if they coincide: 123:(4,1,5),(2,5,7); 124:(4,4,8),(2,8,10); 125:(4,9,13),(2,9,11); 126:(4,12,16),(2,12,14); 127:(4,14,18),(2,16,18); 134:(7,3,10),(5,3,8); 135:(7,6,13),(5,6,11); 136:(7,9,16),(5,9,14); 137:(7,11,18),(5,13,18); 145:(8,5,13),(10,1,11); 146:(8,8,16),(10,4,14); 147:(8,10,18),(10,8,18); 156:(13,3,16),(11,3,14); 157:(13,5,18),(11,7,18); 167:(16,2,18),(14,4,18). Every other relation coordinate has mass zero. Exact addition holds, and the only equal summands are 4+4 and 8+8, both with multiplicity two. The three coordinate marginals are precisely the displayed P rows.")),
                    Paragraph(Text("For the omitted triangle 235, every full coupling satisfies the separator below. Labels 14,11,8 denote values 3,6,9 respectively. If b=11 and c=8 then numerical addition forces a=14. Consequently the sum of the indicators of b=11 and c=8, minus that of a=14, is at most one on every triple of R. Multiplying by nonnegative T and using normalization proves the inequality.")),
                    DisplayMath(LE(Subtract(Add(App(X("P"),Q("35"),D(11)),App(X("P"),Q("25"),D(8))),App(X("P"),Q("23"),D(14))),D(1))),
                    Paragraph(Text("Here P35 is the point mass at 6, P25 the point mass at 9, and P23 has no mass at 3. The separator's left side is therefore two. No full coupling exists at this same P, regardless of which spine coupling is chosen. Restriction of any full coupling gives a spine coupling, so the inclusion of full projections into spine projections is proper on this input.")),
                    Paragraph(Text("The input is realized by the displayed strictly increasing x, so the full system at the ruler's integral assignment is nonempty. This excludes a particular fractional assignment rather than the numerical multiset. Its expected interval lengths are 3(j−i), which satisfy every scalar triangle equality. The scalar conclusion of Lemma 13 and the marginal completion problem thus differ. No all-n family theorem, minimum failing size, LP integrality statement, complexity result, or claim about pruned formulations is asserted."))), DescribeRole.Theorem))));

    private static ScribeNode Def(string name, string id, string title, Formula value) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
        StatementSource.FromAuthor(Disp(Equal(Q(name),value))), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text("Entries are listed in increasing index order."))), DescribeRole.Definition);

    private static Formula ClaimBody()
    {
        Formula body = All("P", Arrow(App(Q("I"),X("n")),Arrow(Fin("d"),Real())),
            Iff(FeasibleBody(App(Q("Delta"),X("n"))),FeasibleBody(App(Q("S"),X("n")))));
        body = Imp(Equal(SumOver("q",Fin("d"),App(X("mu"),X("q"))),App(Q("choose"),X("n"),D(2))),body);
        body = Imp(All("q",Fin("d"),LT(D(0),App(X("mu"),X("q")))),body);
        body = Imp(All("q",Fin("d"),LT(D(0),App(X("y"),X("q")))),body);
        body = Imp(All("a",Fin("d"),All("b",Fin("d"),Imp(LT(X("a"),X("b")),LT(App(X("y"),X("b")),App(X("y"),X("a")))))),body);
        body = Imp(LE(D(1),X("d")),body); body = Imp(LE(D(3),X("n")),body);
        return All("n",Nat(),All("d",Nat(),All("y",Arrow(Fin("d"),Real()),All("mu",Arrow(Fin("d"),Nat()),body))));
    }
    private static Formula RealizesBody()
    {
        Formula increasing = All("i",Fin("n"),All("j",Fin("n"),
            Imp(LT(X("i"),X("j")),LT(App(X("x"),X("i")),App(X("x"),X("j")))));
        Formula difference = Subtract(App(X("x"),App(Q("right"),X("e"))),
            App(X("x"),App(Q("left"),X("e"))));
        Formula labels = All("e",App(Q("I"),X("n")),
            Some("q",Fin("d"),Equal(difference,App(X("y"),X("q")))));
        Formula counts = All("q",Fin("d"),Equal(
            SumOver("e",App(Q("I"),X("n")),
                App(Q("indicator"),Equal(difference,App(X("y"),X("q"))))),
            App(X("mu"),X("q"))));
        return And(increasing,And(labels,counts));
    }
    private static Formula RelationBody() => Equal(X("R"),Seq(OpenBrace,Typed(Seq(X("a"),Comma,X("b"),Comma,X("c")),App(Q("cube"),Fin("d"))),Mid,
        And(Equal(Add(App(X("y"),X("a")),App(X("y"),X("b"))),App(X("y"),X("c"))),
            Or(new Formula.Not(Equal(X("a"),X("b"))),LE(D(2),App(X("mu"),X("a"))))),CloseBrace));
    private static Formula FeasibleBody(Formula domain)
    {
        Formula bounds = All("e",App(Q("I"),X("n")),All("q",Fin("d"),And(LE(D(0),App(X("P"),X("e"),X("q"))),LE(App(X("P"),X("e"),X("q")),D(1)))));
        Formula rows = All("e",App(Q("I"),X("n")),Equal(SumOver("q",Fin("d"),App(X("P"),X("e"),X("q"))),D(1)));
        Formula cols = All("q",Fin("d"),Equal(SumOver("e",App(Q("I"),X("n")),App(X("P"),X("e"),X("q"))),App(X("mu"),X("q"))));
        Formula block = And(All("r",X("R"),And(LE(D(0),App(X("T"),X("tau"),X("r"))),LE(App(X("T"),X("tau"),X("r")),D(1)))),
            And(Equal(SumOver("r",X("R"),App(X("T"),X("tau"),X("r"))),D(1)),
            And(Marginal("a","ij"),And(Marginal("b","jk"),Marginal("c","ik")))));
        return And(bounds,And(rows,And(cols,Some("T",Arrow(domain,Arrow(X("R"),Real())),All("tau",domain,block)))));
    }
    private static Formula Marginal(string coordinate,string edge) => All("q",Fin("d"),Equal(
        SumOver("r",X("R"),Multiply(App(Q("indicator"),Equal(App(Q(coordinate),X("r")),X("q"))),App(X("T"),X("tau"),X("r")))),
        App(X("P"),App(Q(edge),X("tau")),X("q"))));
    private static Formula Vec(params int[] entries)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (int entry in entries) { if(items.Count>0) items.Add(Comma); items.Add(D(entry)); }
        return Par(Seq([..items]));
    }
    private static Formula Fin(string name) => App(Q("Fin"),X(name));
    private static Formula Real() => Seq(Mathbb,Grp(F.Id("R")));
    private static Formula Nat() => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Prop() => Q("Prop");
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula App(Formula f,params Formula[] args) => new Formula.Apply(f,[..args]);
    private static Formula Par(Formula x) => Seq(Left,Open,x,Right,Close);
    private static Formula Typed(Formula a,Formula b) => Par(Seq(a,Colon,Sp,b));
    private static Formula All(string v,Formula t,Formula b) => Seq(Forall,Sp,Typed(X(v),t),Comma,Sp,Par(b));
    private static Formula Some(string v,Formula t,Formula b) => Seq(Exists,Sp,Typed(X(v),t),Comma,Sp,Par(b));
    private static Formula SumOver(string v,Formula t,Formula b) => Seq(Sum,Underscore,Grp(Typed(X(v),t)),Sp,Par(b));
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b));
    private static Formula Or(Formula a,Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Or,Par(b));
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Implies,Par(b));
    private static Formula Iff(Formula a,Formula b) => And(Imp(a,b),Imp(b,a));
    private static Formula LT(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula LE(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Multiply(Formula a,Formula b) => new Formula.Binary(Par(a),FormulaBinaryOperator.Multiply,Par(b));
    private static Formula X(string name) => name == "mu" ? Mu : name == "tau" ? Tau : F.Id(name);
    private static Formula Q(string name) => Seq(Operatorname,Grp(F.Id(name)));
}
