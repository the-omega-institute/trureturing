using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrincipalSpecialization;

internal sealed class BinghamCaterpillarPs3FamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/bingham2026principalspecializations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive j, the source caterpillars (5,j,j,4,3) and (4,j,j,5,3) have different second and identical third ordinary chromatic symmetric principal specializations.",
        H("A family with equal third and unequal second principal specializations"),
        Blocks(
            Node("parts", "Positive parts", "Parts", PartsFormula(),
                "A length-l composition is represented by a function from Fin l to the positive naturals. Fin l uses indices 0 through l−1. The source uses indices 1 through l; adding one identifies the spine indices.", AssessedProvenance.FromRepo(Source)),
            Node("vertex", "The source vertex carrier", "Vertex", VertexFormula(),
                "The dependent pair (i,0) represents the source spine vertex v_(i+1). The pair (i,r), for 1 ≤ r < val(a(i)), represents its leaf w_(i+1,r). Thus the ith block has exactly val(a(i)) vertices. A part equal to one has no leaves.", AssessedProvenance.FromRepo(Source)),
            Node("edges", "The oriented source edge list", "edgeRel", EdgeFormula(),
                "Subscripts 1 and 2 denote the two projections of a vertex. The first disjunct lists spine-to-leaf edges inside a block; the second lists forward consecutive spine edges. The val maps are the natural-number projections of Fin elements.", AssessedProvenance.FromRepo(Source)),
            Node("graph", "The caterpillar", "caterpillar", CaterpillarFormula(),
                "Mathlib SimpleGraph.fromRel symmetrizes the displayed relation and excludes loops. This is exactly Definition 2.1's caterpillar whenever the source endpoint conditions hold. Both five-part families satisfy those conditions for every positive j. The definition is total on all positive part vectors.", AssessedProvenance.FromLiterature(Source)),
            Node("ps", "The ordinary principal specialization", "ps", PsFormula(),
                "Equation (2.1) of the source changes to colors 0 through k−1. SimpleGraph.Coloring means every edge has different endpoint colors; it imposes no surjectivity. Every proper coloring into Fin k occurs once in the finite sum. X is Polynomial.X over the integers. These polynomials embed injectively in the source's complex coefficient ring, preserving equality and inequality. No t refinement is used.", AssessedProvenance.FromLiterature(Source)),
            Node("alpha", "The first family", "alpha", FamilyFormula("alpha", 5, 4),
                "The tuple denotes the Fin 5 indexed function with the displayed entries, all in the positive naturals.", AssessedProvenance.FromLiterature(Source)),
            Node("beta", "The second family", "beta", FamilyFormula("beta", 4, 5),
                "The repeated internal part is the same arbitrary positive natural j in both positions. The proof uses the fixed end blocks 5,4,3 in the stated algebraic identity.", AssessedProvenance.FromLiterature(Source)),
            Node("spine-good", "Proper spine colors", "SpineGood", SpineGoodFormula(),
                "Consecutive spine vertices receive distinct colors.", AssessedProvenance.FromRepo(Source)),
            Node("leaf-sum", "The choices at one leaf", "leafSum", LeafSumFormula(),
                "The sum ranges over every color different from the incident spine color.", AssessedProvenance.FromRepo(Source)),
            Node("block-weight", "The weight of one block", "blockWeight", BlockWeightFormula(),
                "A positive part m gives one spine vertex and val(m) minus one leaves. The zeroth power accounts for an empty leaf set.", AssessedProvenance.FromRepo(Source)),
            HelperTheorem("spine-sum", "The complete finite spine sum", "ps_spine_sum", SpineSumFormula(),
                "The coloring bijection and independent leaf choices give this identity for every positive part vector and every number of colors."),
            HelperTheorem("sum-successor", "Expanding a finite function sum", "sum_finfun_succ", SumSuccessorFormula(),
                "The first value and the remaining function uniquely determine a function on Fin (n+1)."),
            HelperTheorem("leaf-sum-all", "A leaf sum over the whole color set", "leafSum_eq", LeafSumEqFormula(),
                "The forbidden color contributes zero; every other color contributes its monomial."),
            Node("claim", "Remark 3.11, first question", "claim", Iff(F.Id("claim"), P(ClaimBody())),
                "The domain is all positive integers, including j=1. Equality is formal polynomial equality in Z[X], with an indeterminate X. The second question, whether these are the only such pairs, is outside this statement.", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("bingham-family-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The entire positive-parameter family"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Restricting a proper coloring to the spine and its leaves gives a bijection with proper spine colorings and independent leaf assignments. Weight is additive over the actual vertices. Summing the leaf choices gives, for spine color c and positive part a, the block weight X^c times (the sum of X^d over d different from c) raised to val(a)−1. Empty leaf sets contribute one. The five spine colors are then summed subject to consecutive inequality. For three colors, an identity with an arbitrary repeated three-entry middle weight vector interchanges the fixed 5 and 4 blocks while keeping the final 3 block. Polynomial normalization proves that identity before substituting the weights for j, so no finite cutoff on j or numerical evaluation of X occurs. For two colors, the two alternating spine choices give X^(val(j)+5)+X^(val(j)+7) for alpha and X^(val(j)+6)+X^(val(j)+6) for beta. Their coefficients at degree val(j)+5 are one and zero. The proof settles the first question only; classification, the t-chromatic invariant, and the source's four-color conjectures remain outside its scope."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bingham-2026-caterpillar-principal-specialization-family"),
                    ResolutionKind.Proved))), []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("bingham-family-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock HelperTheorem(string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("bingham-family-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Arrow(Formula x, Formula y) => Seq(P(x),Sp,To,Sp,P(y));
    private static Formula SumOver(string x, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum,Seq(F.Id(x),Colon,type)),Sp,body);
    private static Formula ProductOver(string x, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod,Seq(F.Id(x),Colon,type)),Sp,body);
    private static Formula IntegerPolynomial() => Call("Polynomial",Seq(Mathbb,Grp(F.Id("Z"))));
    private static Formula ColorBinders(Formula body) => All("k",Nat(),All("c",Call("Fin",F.Id("k")),body));
    private static Formula AllowedColors() => Seq(OpenBrace,F.Id("d"),Colon,Call("Fin",F.Id("k")),Mid,Sp,Ne(F.Id("d"),F.Id("c")),CloseBrace);
    private static Formula SpineGoodFormula() => All("l",Nat(),All("k",Nat(),
        All("c",Arrow(Call("Fin",F.Id("l")),Call("Fin",F.Id("k"))),
            Iff(Call("SpineGood",F.Id("c")),All("i",Call("Fin",F.Id("l")),All("j",Call("Fin",F.Id("l")),
                Seq(P(Equal(PlusOf(Val(F.Id("i")),D(1)),Val(F.Id("j")))),Sp,Rightarrow,Sp,
                    P(Ne(Call("c",F.Id("i")),Call("c",F.Id("j")))))))))));
    private static Formula LeafSumFormula() => ColorBinders(Equal(Call("leafSum",F.Id("c")),
        SumOver("d",AllowedColors(),new Formula.Power(Call("Polynomial.X"),Call("Fin.val",Call("Subtype.val",F.Id("d")))))));
    private static Formula BlockWeightFormula() => All("k",Nat(),All("m",Positive(),All("c",Call("Fin",F.Id("k")),
        Equal(Call("blockWeight",F.Id("m"),F.Id("c")),
            new Formula.Binary(new Formula.Power(Call("Polynomial.X"),Val(F.Id("c"))),FormulaBinaryOperator.Multiply,
                new Formula.Power(Call("leafSum",F.Id("c")),new Formula.Binary(Call("PNat.val",F.Id("m")),FormulaBinaryOperator.Subtract,D(1))))))));
    private static Formula SpineSumFormula() => All("l",Nat(),All("k",Nat(),All("a",Call("Parts",F.Id("l")),
        Equal(Call("ps",Call("caterpillar",F.Id("a")),F.Id("k")),
            SumOver("c",Arrow(Call("Fin",F.Id("l")),Call("Fin",F.Id("k"))),
                Seq(Operatorname,Grp(F.Id("if")),Sp,Call("SpineGood",F.Id("c")),Sp,Operatorname,Grp(F.Id("then")),Sp,
                    ProductOver("i",Call("Fin",F.Id("l")),Call("blockWeight",Call("a",F.Id("i")),Call("c",F.Id("i")))),Sp,
                    Operatorname,Grp(F.Id("else")),Sp,D(0)))))));
    private static Formula SumSuccessorFormula() => All("A",Seq(F.Id("Type"),Star),
        Seq(OpenBracket,Call("Fintype",F.Id("A")),CloseBracket,Sp,All("n",Nat(),
            All("f",Arrow(Arrow(Call("Fin",PlusOf(F.Id("n"),D(1))),F.Id("A")),IntegerPolynomial()),
                Equal(SumOver("c",Arrow(Call("Fin",PlusOf(F.Id("n"),D(1))),F.Id("A")),Call("f",F.Id("c"))),
                    SumOver("x",F.Id("A"),SumOver("c",Arrow(Call("Fin",F.Id("n")),F.Id("A")),
                        Call("f",Call("Fin.cons",F.Id("x"),F.Id("c"))))))))));
    private static Formula LeafSumEqFormula() => ColorBinders(Equal(Call("leafSum",F.Id("c")),
        SumOver("d",Call("Fin",F.Id("k")),Seq(Operatorname,Grp(F.Id("if")),Sp,P(Ne(F.Id("d"),F.Id("c"))),Sp,
            Operatorname,Grp(F.Id("then")),Sp,new Formula.Power(Call("Polynomial.X"),Val(F.Id("d"))),Sp,
            Operatorname,Grp(F.Id("else")),Sp,D(0)))));

    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Qualified(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count != 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Qualified(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Qualified(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, P(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.And, P(y));
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Or, P(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Positive() => new Formula.Power(Nat(), Plus);
    private static Formula PlusOf(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Proj(Formula x, byte i) => new Formula.Subscript(x, D(i));
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula PartsFormula() => All("l", Nat(), Equal(Call("Parts", F.Id("l")),
        P(Seq(Call("Fin", F.Id("l")), Sp, To, Sp, Positive()))));
    private static Formula PartBinders(Formula body) => All("l", Nat(), All("a", Call("Parts", F.Id("l")), body));
    private static Formula VertexFormula() => PartBinders(Equal(Call("Vertex", F.Id("a")),
        Seq(new Formula.Subscript(Sigma, Seq(F.Id("i"), Colon, Call("Fin", F.Id("l")))), Sp,
            Call("Fin", Call("PNat.val", Call("a", F.Id("i")))))));
    private static Formula EdgeFormula()
    {
        Formula u = F.Id("u"), v = F.Id("v");
        Formula leaf = And(Equal(Proj(u, 1), Proj(v, 1)),
            And(Equal(Val(Proj(u, 2)), D(0)), Ne(Val(Proj(v, 2)), D(0))));
        Formula spine = And(Equal(Val(Proj(u, 2)), D(0)),
            And(Equal(Val(Proj(v, 2)), D(0)), Equal(PlusOf(Val(Proj(u, 1)), D(1)), Val(Proj(v, 1)))));
        return PartBinders(All("u", Call("Vertex", F.Id("a")), All("v", Call("Vertex", F.Id("a")),
            Iff(Call("edgeRel", F.Id("a"), u, v), Or(leaf, spine)))));
    }
    private static Formula CaterpillarFormula() => PartBinders(Equal(Call("caterpillar", F.Id("a")),
        Call("SimpleGraph.fromRel", Call("edgeRel", F.Id("a")))));
    private static Formula PsFormula()
    {
        Formula colors = Call("SimpleGraph.Coloring", F.Id("G"), Call("Fin", F.Id("k")));
        Formula exponent = Seq(new Formula.Subscript(F.Sum, Seq(F.Id("v"), Colon, F.Id("V"))), Sp,
            Val(Call("c", F.Id("v"))));
        Formula sum = Seq(new Formula.Subscript(F.Sum, Seq(F.Id("c"), Colon, colors)), Sp,
            new Formula.Power(Call("Polynomial.X"), exponent));
        return All("V", Seq(F.Id("Type"), Star), Seq(OpenBracket, Call("Fintype", F.Id("V")), CloseBracket, Sp,
            All("G", Call("SimpleGraph", F.Id("V")), All("k", Nat(), Equal(Call("ps", F.Id("G"), F.Id("k")), sum)))));
    }
    private static Formula FamilyFormula(string name, byte first, byte fourth) => All("j", Positive(),
        Equal(Call(name, F.Id("j")), Seq(Bang, OpenBracket, D(first), Comma, F.Id("j"), Comma,
            F.Id("j"), Comma, D(fourth), Comma, D(3), CloseBracket)));
    private static Formula Specialization(string family, byte k) =>
        Call("ps", Call("caterpillar", Call(family, F.Id("j"))), D(k));
    private static Formula ClaimBody() => All("j", Positive(), And(
        Ne(Specialization("alpha", 2), Specialization("beta", 2)),
        Equal(Specialization("alpha", 3), Specialization("beta", 3))));
}
