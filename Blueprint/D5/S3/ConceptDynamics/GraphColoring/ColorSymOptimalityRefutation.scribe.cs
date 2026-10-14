using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class ColorSymOptimalityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/godingrisottogni2025colorsym");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A colorable K4 list assignment defeats every ColorSym execution.",
        H("ColorSym need not find an existing list multicoloring"),
        Blocks(
            Definition("supp", "Color support", SupportFormula(), AssessedProvenance.FromLiterature(Source),
                "The support of an integer color is the set of vertices whose lists contain it. "
                + "Vertices of the complete graph are indexed by Fin n, with the paper's indices shifted down by one."),
            Definition("Ip", "Proper intersections", AtomFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 2.1, p. 59, defines the proper intersection by taking the intersection of the selected lists "
                + "and removing the union of all other lists. Here colors are integers in the union of the lists, "
                + "filtered by exact support; the empty support has empty proper intersection."),
            Definition("IsColoring", "List multicoloring", ColoringFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 1, pp. 57–58: \"a coloring function φ on the vertices of G that assigns to each vertex v "
                + "a subset of b elements from L(v) in such a way that φ(u) ∩ φ(v) = ∅ for any uv ∈ E(G)\". "
                + "For a complete graph, every pair of distinct vertices is adjacent. The symbol p denotes φ."),
            Definition("Colorable", "Existence of a list multicoloring", ColorableFormula(), AssessedProvenance.FromLiterature(Source),
                "A list assignment is colorable when such a family of disjoint b-element subsets exists."),
            Definition("AdmissibleOrder", "Order of supports", OrderFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 3.1, p. 63: \"Otherwise, for each set S with |S| = i, consider |Ip(S)|\". "
                + "The order contains every support of size at least two exactly once, with nondecreasing size."),
            Definition("AdmissiblePick", "Choosing a color", PickFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 3.1, p. 63: \"Remove a color from Ip(S) and assign it to vj.\" "
                + "The function pick selects an element from every nonempty integer-color pool."),
            Definition("best", "Least-loaded vertex and tie breaking", BestFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 3.1, p. 63: \"let j ∈ S be the index for which w(j) is minimum "
                + "(if more than one j with minimum w, then take the smallest index)\". "
                + "Sorting the set of minimizers in ascending vertex order selects exactly this vertex."),
            Definition("stopped", "Stopping condition", StoppedFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 3.1, p. 63: \"If wi ≥ b for each i or i = n + 1, then Stop.\" "
                + "The first component of st records output sets and the second records their loads. "
                + "Exhausting the support list implements the terminal step n + 1."),
            Definition("assign", "Assigning one color", AssignFormula(), AssessedProvenance.FromLiterature(Source),
                "A color is inserted at the selected vertex and its load increases by one."),
            Definition("runPool", "Processing one proper intersection", PoolFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 3.1, p. 63: \"Goto Step i until Ip(S) is empty.\" "
                + "The fuel is initially the pool cardinality. Each assignment erases the chosen color, "
                + "so an admissible pick decreases that cardinality by one."),
            Definition("runSupports", "Processing all supports", SupportsFormula(), AssessedProvenance.FromLiterature(Source),
                "Each support is processed with its proper intersection as the color pool. "
                + "The empty list returns the current pair of outputs and loads."),
            Definition("initial", "Singleton proper intersections", InitialFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 3.1, p. 63: \"Color every proper intersections of sets of size 1: "
                + "vi gets |Ip({i})| colors. Thus wi = |Ip({i})|.\" "
                + "All singleton proper intersections are assigned before shared colors are processed."),
            Definition("colorSym", "ColorSym output", OutputFormula(), AssessedProvenance.FromLiterature(Source),
                "The output is the first component of the final pair after the singleton step and all ordered supports."),
            Definition("claim", "ColorSym optimality conjecture", ClaimFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 3.1, p. 63: \"We conjecture that this algorithm is optimal "
                + "(i.e., produces an (L, b)-coloring if K_n is (L, b)-colorable).\" "
                + "The parameters n, a and b are natural numbers, L assigns finite integer-color lists, "
                + "and every list has exactly a elements. The formula allows any admissible support order "
                + "and color selection, and asks only for a b-coloring contained in the output."),
            Describe.Lean(
                DescribeId.Create("colorsym-optimality-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The optimality conjecture is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take four lists {1,2,3,4,5,6}, {1,2,3,4,7,8}, {5,6,9,10,11,12}, "
                    + "and {5,6,13,14,15,16}, and b = 4. The disjoint subsets {1,2,5,6}, "
                    + "{3,4,7,8}, {9,10,11,12}, and {13,14,15,16} form a 4-coloring. "
                    + "Every ColorSym execution has final loads (5,3,4,4), independently of color choice. "
                    + "Vertex 2 receives only three colors. Current-load balancing spends the pair pool "
                    + "on vertex 1 before its later triple pool, while vertex 2 has no later supply."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("godin-grisot-togni-2022-colorsym-optimality"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("colorsym-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula SupportFormula()
    {
        Formula n = F.Id("n"), l = F.Id("L"), c = F.Id("c"), i = F.Id("i");
        return All("n", N(), All("L", Lists(n), All("c", Z(),
            Equal(Call("supp", l, c), App(Q("Finset", "filter"),
                LambdaOf("i", Fin(n), Member(c, App(l, i))), Q("Finset", "univ"))))));
    }

    private static Formula AtomFormula()
    {
        Formula n = F.Id("n"), l = F.Id("L"), s = F.Id("S"), c = F.Id("c");
        return All("n", N(), All("L", Lists(n), All("S", Supports(n),
            Equal(Call("Ip", l, s), App(Q("Finset", "filter"),
                LambdaOf("c", Z(), Equal(Call("supp", l, c), s)),
                App(Q("Finset", "biUnion"), Q("Finset", "univ"), l))))));
    }

    private static Formula ColoringFormula()
    {
        Formula n = F.Id("n"), l = F.Id("L"), b = F.Id("b"), p = F.Id("p");
        Formula i = F.Id("i"), j = F.Id("j");
        Formula condition = And(
            All("i", Fin(n), And(Subset(App(p, i), App(l, i)), Equal(Card(App(p, i)), b))),
            All("i", Fin(n), All("j", Fin(n), Implies(NotEqual(i, j),
                Call("Disjoint", App(p, i), App(p, j))))));
        return All("n", N(), All("L", Lists(n), All("b", N(), All("p", Lists(n),
            Equal(Call("IsColoring", l, b, p), condition)))));
    }

    private static Formula ColorableFormula()
    {
        Formula n = F.Id("n"), l = F.Id("L"), b = F.Id("b"), p = F.Id("p");
        return All("n", N(), All("L", Lists(n), All("b", N(),
            Equal(Call("Colorable", l, b), ExistsOf("p", Lists(n), Call("IsColoring", l, b, p))))));
    }

    private static Formula OrderFormula()
    {
        Formula n = F.Id("n"), o = F.Id("ord"), s = F.Id("S"), t = F.Id("T");
        return All("n", N(), All("ord", Call("List", Supports(n)),
            Equal(Call("AdmissibleOrder", o), And(App(Q("List", "Nodup"), o),
                All("S", Supports(n), Iff(Member(s, o), Le(D(2), Card(s)))),
                App(Q("List", "Pairwise"), LambdaOf("S", Supports(n),
                    LambdaOf("T", Supports(n), Le(Card(s), Card(t)))), o)))));
    }

    private static Formula PickFormula()
    {
        Formula pick = F.Id("pick"), s = F.Id("s");
        return All("pick", PickType(), Equal(Call("AdmissiblePick", pick),
            All("s", Colors(), Implies(App(Q("Finset", "Nonempty"), s), Member(App(pick, s), s)))));
    }

    private static Formula BestFormula()
    {
        Formula n = F.Id("n"), s = F.Id("S"), w = F.Id("w"), i = F.Id("i"), j = F.Id("j");
        Formula rest = F.Id("rest");
        Formula minimizers = App(Q("Finset", "filter"), LambdaOf("i", Fin(n),
            All("j", Fin(n), Implies(Member(j, s), Le(App(w, i), App(w, j))))), s);
        Formula ascending = LambdaOf("i", Fin(n), LambdaOf("j", Fin(n), Le(i, j)));
        Formula sorted = App(Q("Finset", "sort"), minimizers, ascending);
        Formula emptyCase = Implies(Equal(sorted, Seq(OpenBracket, CloseBracket)),
            Equal(Call("best", s, w), Op("none")));
        Formula consCase = All("j", Fin(n), All("rest", Call("List", Fin(n)),
            Implies(Equal(sorted, App(Q("List", "cons"), j, rest)),
                Equal(Call("best", s, w), Call("some", j)))));
        return All("n", N(), All("S", Supports(n), All("w", Arrow(Fin(n), N()),
            And(emptyCase, consCase))));
    }

    private static Formula StoppedFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b"), st = F.Id("st"), j = F.Id("j");
        return All("n", N(), All("b", N(), All("st", StateType(n),
            Equal(Call("stopped", b, st), Call("decide", All("j", Fin(n), Le(b, App(Snd(st), j))))))));
    }

    private static Formula AssignFormula()
    {
        Formula n = F.Id("n"), st = F.Id("st"), j = F.Id("j"), c = F.Id("c");
        Formula outUpdate = App(Q("Function", "update"), Fst(st), j, Call("insert", c, App(Fst(st), j)));
        Formula loadUpdate = App(Q("Function", "update"), Snd(st), j, Add(App(Snd(st), j), D(1)));
        return All("n", N(), All("st", StateType(n), All("j", Fin(n), All("c", Z(),
            Equal(Call("assign", st, j, c), Pair(outUpdate, loadUpdate))))));
    }

    private static Formula PoolFormula()
    {
        Formula n = F.Id("n"), s = F.Id("S"), b = F.Id("b"), pick = F.Id("pick");
        Formula fuel = F.Id("fuel"), pool = F.Id("pool"), st = F.Id("st"), j = F.Id("j"), c = F.Id("c");
        Formula zero = Equal(Call("runPool", s, b, pick, D(0), pool, st), st);
        Formula recurse = Call("runPool", s, b, pick, fuel,
            App(Q("Finset", "erase"), pool, c), Call("assign", st, j, c));
        Formula letColor = Seq(Op("let"), Sp, c, Sp, Colon, Eq, Sp, App(pick, pool), Semi, Sp, recurse);
        Formula match = Seq(Op("match"), Sp, Call("best", s, Snd(st)), Sp, Op("with"), Sp,
            Bar, Sp, Op("none"), Sp, Mapsto, Sp, st, Sp,
            Bar, Sp, Call("some", j), Sp, Mapsto, Sp, letColor);
        Formula step = Equal(Call("runPool", s, b, pick, Add(fuel, D(1)), pool, st),
            If(Call("stopped", b, st), st, If(Equal(pool, Emptyset), st, match)));
        Formula equations = All("pool", Colors(), All("st", StateType(n),
            And(zero, All("fuel", N(), step))));
        return All("n", N(), All("S", Supports(n), All("b", N(), All("pick", PickType(), equations))));
    }

    private static Formula SupportsFormula()
    {
        Formula n = F.Id("n"), l = F.Id("L"), b = F.Id("b"), pick = F.Id("pick");
        Formula ord = F.Id("ord"), s = F.Id("S"), st = F.Id("st"), ip = Call("Ip", l, s);
        Formula empty = Equal(Call("runSupports", l, b, pick, Seq(OpenBracket, CloseBracket), st), st);
        Formula cons = Equal(Call("runSupports", l, b, pick, App(Q("List", "cons"), s, ord), st),
            Call("runSupports", l, b, pick, ord, Call("runPool", s, b, pick, Card(ip), ip, st)));
        return All("n", N(), All("L", Lists(n), All("b", N(), All("pick", PickType(),
            All("st", StateType(n), And(empty,
                All("S", Supports(n), All("ord", Call("List", Supports(n)), cons))))))));
    }

    private static Formula InitialFormula()
    {
        Formula n = F.Id("n"), l = F.Id("L"), i = F.Id("i");
        Formula atom = Call("Ip", l, Singleton(i));
        return All("n", N(), All("L", Lists(n), Equal(Call("initial", l),
            Pair(LambdaOf("i", Fin(n), atom), LambdaOf("i", Fin(n), Card(atom))))));
    }

    private static Formula OutputFormula()
    {
        Formula n = F.Id("n"), l = F.Id("L"), b = F.Id("b"), ord = F.Id("ord"), pick = F.Id("pick");
        return All("n", N(), All("L", Lists(n), All("b", N(),
            All("ord", Call("List", Supports(n)), All("pick", PickType(),
                Equal(Call("colorSym", l, b, ord, pick),
                    Fst(Call("runSupports", l, b, pick, ord, Call("initial", l)))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), a = F.Id("a"), b = F.Id("b"), l = F.Id("L");
        Formula ord = F.Id("ord"), pick = F.Id("pick"), p = F.Id("p"), i = F.Id("i");
        Formula success = ExistsOf("p", Lists(n), And(Call("IsColoring", l, b, p),
            All("i", Fin(n), Subset(App(p, i), App(Call("colorSym", l, b, ord, pick), i)))));
        Formula choices = ExistsOf("ord", Call("List", Supports(n)), ExistsOf("pick", PickType(),
            And(Call("AdmissibleOrder", ord), Call("AdmissiblePick", pick), success)));
        Formula quantified = All("n", N(), All("a", N(), All("b", N(), All("L", Lists(n),
            Implies(All("i", Fin(n), Equal(Card(App(l, i)), a)),
                Implies(Call("Colorable", l, b), choices))))));
        return Equal(F.Id("claim"), quantified);
    }

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => new Formula.Integers();
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Colors() => Call("Finset", Z());
    private static Formula Lists(Formula n) => Arrow(Fin(n), Colors());
    private static Formula Supports(Formula n) => Call("Finset", Fin(n));
    private static Formula PickType() => Arrow(Colors(), Z());
    private static Formula StateType(Formula n) => Seq(Parenthesized(Lists(n)), Sp, Times, Sp,
        Parenthesized(Arrow(Fin(n), N())));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Op(owner), Dot, Op(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Op(name), args);
    private static Formula Card(Formula s) => App(Q("Finset", "card"), s);
    private static Formula Fst(Formula st) => Seq(Parenthesized(st), Dot, D(1));
    private static Formula Snd(Formula st) => Seq(Parenthesized(st), Dot, D(2));
    private static Formula Pair(Formula a, Formula b) => Seq(Langle, a, Comma, Sp, b, Rangle);
    private static Formula Singleton(Formula a) => Seq(OpenBrace, a, CloseBrace);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(params Formula[] values)
    {
        Formula value = Parenthesized(values[^1]);
        for (int i = values.Length - 2; i >= 0; --i)
            value = new Formula.Logic(Parenthesized(values[i]), FormulaLogicOperator.And, value);
        return value;
    }
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOf(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(Op("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Seq(Op("if"), Sp, condition, Sp, Op("then"), Sp, yes, Sp, Op("else"), Sp, no);
}
