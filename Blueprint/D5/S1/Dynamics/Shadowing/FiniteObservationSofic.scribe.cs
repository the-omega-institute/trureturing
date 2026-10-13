using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class FiniteObservationSoficDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/FiniteObservationSofic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every continuous observation into a finite discrete alphabet of a finite-open-cover shadowing source has an exact entire finite graph language.",
        H("Finite Observations of Shadowing Sources"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("entire-graph-label-language"),
                DeclarationHandle.Create(Owner + "graphLanguage"),
                H("All complete forward graph paths"),
                StatementSource.FromAuthor(GraphFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary vertex type V, alphabet A, directed edge relation E and vertex label l, "
                    + "graphLanguage(E,l) consists of words w for which one entire path p satisfies "
                    + "E(p(n),p(n+1)) and l(p(n))=w(n) for every natural n. All vertices are allowed "
                    + "as initial vertices, and time zero is included. Vertices with no predecessor "
                    + "are retained; vertices with no infinite continuation produce no word."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-graph-sofic-language"),
                DeclarationHandle.Create(Owner + "IsSofic"),
                H("Exact finite graph presentation"),
                StatementSource.FromAuthor(SoficFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "IsSofic(S) means that some natural n, a relation E on Fin n and a label map "
                    + "l:Fin n→A have S=graphLanguage(E,l). The equality concerns complete infinite "
                    + "words. It is stronger than finite-prefix realization or one-sided language inclusion. "
                    + "The n=0 graph is allowed and its language is empty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-observation-exact-sofic-image"),
                DeclarationHandle.Create(Owner + "finite_observation_isSofic"),
                H("Finite observations preserve exact sofic histories"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing")),
                Blocks(
                    Paragraph(Text(
                        "Let X be any topological space, f:X→X any self-map, and a:X→A continuous, "
                        + "where A is finite and discrete. Assume the exact HasShadowing notion imported "
                        + "from MittagLefflerInverseLimit: every finite open output cover C has a finite "
                        + "open control cover D, and every whole D-pseudo-orbit is C-shadowed by one point. "
                        + "Then the range of completeItinerary(f,a), x↦(n↦a(f^[n](x))), is sofic.")),
                    Paragraph(Text(
                        "Take C to be all observation fibers a⁻¹{c}, including empty fibers, and choose "
                        + "a finite shadowing control cover D. Use D×A as the finite vertex type. "
                        + "There is an edge (U,c)→(V,d) exactly when one x lies in U with a(x)=c "
                        + "and f(x) lies in V with a(f(x))=d. Label (U,c) by c. Empty cells may be "
                        + "retained, since no complete path can use them.")),
                    Paragraph(Text(
                        "A complete graph path has, at each time n, one edge witness x(n). "
                        + "Both f(x(n)) and x(n+1) lie in the next vertex's D-member, so these witnesses "
                        + "form one whole D-pseudo-orbit. Its C-tracer z has a(f^[n](z)) equal to the "
                        + "path label at every n. This proves graph-language soundness for whole histories. "
                        + "Conversely, for any actual source point x choose a D-member containing each "
                        + "f^[n](x); those vertices and source points give all edges and the exact observed "
                        + "word. A finite-carrier equivalence reindexes D×A as Fin n without changing "
                        + "either complete-path language. Together these prove exact equality.")),
                    Paragraph(Text(
                        "The graph construction requires no compactness or separation of X and no continuity, "
                        + "surjectivity or invertibility of f. Off compact sources this finite-open-cover "
                        + "hypothesis should not be silently identified with metric or uniform shadowing, "
                        + "whose control covers can be infinite. For the original compact Hausdorff "
                        + "continuous source it is precisely the intended finite-cover formulation. "
                        + "Empty sources and alphabets are included by the same proof: any putative full "
                        + "graph path would yield a source edge witness, so the graph language is empty.")),
                    Paragraph(Text(
                        "The noncompact qualification is substantive. In ordinary mathematics, the "
                        + "successor map on the natural numbers with the discrete metric has metric "
                        + "shadowing: an error tolerance below one forces exact orbits. Observe the "
                        + "mechanical word b(n)=floor((n+1)alpha)-floor(n alpha), choosing irrational "
                        + "alpha with 0<alpha<1. This is a "
                        + "continuous binary observation on that discrete source, and all its complete "
                        + "histories have irrational limiting frequency alpha. None is periodic, whereas "
                        + "a nonempty entire finite graph language contains a periodic cycle word. Hence "
                        + "this metric-shadowing source cannot satisfy the finite-cover HasShadowing "
                        + "premise. This comparison is ordinary explanatory mathematics, not an additional "
                        + "formalized metric-shadowing theorem in the present module.")),
                    Paragraph(Text(
                        "The S1 statement writes the history as x↦(n↦a(f^[n](x))), the definitional "
                        + "expansion of the existing S3 completeItinerary, and reuses HasShadowing. "
                        + "Its retained Reg mirror imports the original history definition explicitly "
                        + "and checks the same statement by definitional equality. The mathematical "
                        + "S1 import closure contains no S3 dependency. Its full-history finite graph conclusion supports "
                        + "obstructions to proposed shadowing covers, but does not construct a single "
                        + "globally coherent family of Peng's finite-net arrays. Questions 5.1 and 5.2 "
                        + "remain unresolved here. No literature originality or solution-priority claim "
                        + "is attached to this graph mechanism. The conclusion is soficity of the "
                        + "observed image; no shadowing property of arbitrary image factors is asserted."))),
                DescribeRole.Theorem))));

    private static Formula GraphFormula()
    {
        Formula v = F.Id("V"), a = F.Id("A"), edge = F.Id("E"), label = F.Id("l");
        Formula word = F.Id("w"), path = F.Id("p"), n = F.Id("n");
        Formula pathLaw = Seq(Forall, Sp, Typed(n, Nat()), Comma, Sp,
            Apply(edge, Apply(path, n), Apply(path, Seq(n, Plus, D(1)))), Sp, Land, Sp,
            Apply(label, Apply(path, n)), Sp, Eq, Sp, Apply(word, n));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(v, Seq(F.Id("Type"), Sp, F.Id("u"))), Comma, Sp,
                Typed(a, Seq(F.Id("Type"), Sp, F.Id("v"))), Comma, Sp,
                Typed(edge, Seq(v, Sp, Rightarrow, Sp, v, Sp, Rightarrow, Sp, F.Id("Prop"))), Comma, Sp,
                Typed(label, Seq(v, Sp, Rightarrow, Sp, a)), Comma),
            Seq(Call("graphLanguage", edge, label), Sp, Eq, Sp, OpenBrace,
                Typed(word, Seq(Nat(), Sp, Rightarrow, Sp, a)), Sp, Mid, Sp,
                Exists, Sp, Typed(path, Seq(Nat(), Sp, Rightarrow, Sp, v)), Comma, Sp,
                pathLaw, CloseBrace, Dot)
        ]));
    }

    private static Formula SoficFormula()
    {
        Formula a = F.Id("A"), s = F.Id("S"), n = F.Id("n");
        Formula edge = F.Id("E"), label = F.Id("l"), vertices = Call("Fin", n);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(a, Seq(F.Id("Type"), Sp, F.Id("u"))), Comma, Sp,
                Typed(s, Call("Set", Seq(Nat(), Sp, Rightarrow, Sp, a))), Comma),
            Seq(Call("IsSofic", s), Sp, Leftrightarrow, Sp,
                Exists, Sp, Typed(n, Nat()), Comma, Sp,
                Typed(edge, Seq(vertices, Sp, Rightarrow, Sp, vertices, Sp, Rightarrow, Sp, F.Id("Prop"))), Comma, Sp,
                Typed(label, Seq(vertices, Sp, Rightarrow, Sp, a)), Comma, Sp,
                s, Sp, Eq, Sp, Call("graphLanguage", edge, label), Dot)
        ]));
    }

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("X"), aType = F.Id("A"), f = F.Id("f"), a = F.Id("a");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(x, Seq(F.Id("Type"), Sp, F.Id("u"))), Comma, Sp,
                Typeclass("TopologicalSpace", x), Comma, Sp,
                Typed(aType, Seq(F.Id("Type"), Sp, F.Id("v"))), Comma, Sp,
                Typeclass("TopologicalSpace", aType), Comma, Sp,
                Typeclass("DiscreteTopology", aType), Comma, Sp,
                Typeclass("Finite", aType), Comma),
            Seq(Forall, Sp, Typed(f, Seq(x, Sp, Rightarrow, Sp, x)), Comma, Sp,
                Typed(a, Seq(x, Sp, Rightarrow, Sp, aType)), Comma, Sp,
                Call("Continuous", a), Sp, Rightarrow, Sp,
                Call("HasShadowing", f), Sp, Rightarrow, Sp,
                Call("IsSofic", Call("Set.range", Call("completeItinerary", f, a))), Dot)
        ]));
    }

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var names = name.Split('.');
        var items = new List<Formula> { F.Id(names[0]) };
        for (var i = 1; i < names.Length; i++) items.AddRange([Dot, F.Id(names[i])]);
        return Apply(Seq(Operatorname, Grp([.. items])), arguments);
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
