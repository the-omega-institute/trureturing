using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class CoherentFollowerCoverDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/CoherentFollowerCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent closed forward-invariant finite-follower languages over finite alphabets have finite live covers with onto maps on entire paths.",
        H("Coherent All-Subface Follower Covers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coherent-follower-0"),
                DeclarationHandle.Create(Owner + "finite_followers_of_graph"),
                H("Finite followers of a finite graph"), StatementSource.FromAuthor(FormulaFor(0)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary alphabet and a finite vertex type, the nonempty followers of the complete graph language form a finite type. Consuming a finite past tracks the reachable subset at the next time. Every initial vertex is allowed, so the empty past begins at the entire vertex set and needs no predecessor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-1"),
                DeclarationHandle.Create(Owner + "followers_card_le_pow"),
                H("The powerset bound"), StatementSource.FromAuthor(FormulaFor(1)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A presentation on n vertices has at most 2^n nonempty followers. Followers factor through reachable subsets, including subsets containing transient or dead vertices; no trimming premise is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-2"),
                DeclarationHandle.Create(Owner + "finite_followers_of_sofic"),
                H("Soficity supplies finite followers"), StatementSource.FromAuthor(FormulaFor(2)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing IsSofic predicate supplies a finite vertex-labelled graph presentation and hence finite followers. No particular presentation is retained in the language-family data."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-3"),
                DeclarationHandle.Create(Owner + "LanguageSystem"),
                H("Coherent language premises"), StatementSource.FromAuthor(FormulaFor(3)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary index type I and a family of topological alphabets A_i, every finite scope F has a nonempty closed forward-invariant language L_F with finitely many nonempty followers. For F contained in G, the coordinate restriction of entire words in L_G has image exactly L_F. The shift need not be onto. ofSofic obtains this data from a coherent family of sofic languages. Finite alphabets are required only for finiteness of vertices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coherent-follower-4"),
                DeclarationHandle.Create(Owner + "Context"),
                H("Reachable all-subface contexts"), StatementSource.FromAuthor(FormulaFor(4)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write Q_H(u) for the follower of a finite past u in L_H. A context at F is the vector of Q_H(u restricted to H) over every H contained in F, realized by one common past u that extends to a word in L_F. Reachability is part of the definition; arbitrary independent choices of followers are excluded. The face type is finite by the powerset of F, even when I is uncountable. Contexts inject into the product of the finite follower types."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coherent-follower-5"),
                DeclarationHandle.Create(Owner + "Vertex"),
                H("Allowed current letters"), StatementSource.FromAuthor(FormulaFor(5)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A vertex consists of a reachable context s and a current letter a whose left derivative in the top component is nonempty. Its label is a. An edge requires the next context to be the componentwise derivative by the restrictions of a. The next letter is already allowed because its endpoint is a vertex. This gives deterministic context updates without choosing a representative past."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coherent-follower-6"),
                DeclarationHandle.Create(Owner + "path_in_initial_follower"),
                H("Exact soundness from an arbitrary initial past"), StatementSource.FromAuthor(FormulaFor(6)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let p be any entire graph path and let u represent its initial context. Then u concatenated with the whole label word of p belongs to L_F. The past u may be nonempty. At time n the edge equations reconstruct the context after u followed by the first n labels. All these finite prefixes have continuations. Choosing continuations gives a sequence eventually equal to the prescribed future in each coordinate; the existing product-convergence and closed-limit lemmas place that future in the closed initial follower."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-7"),
                DeclarationHandle.Create(Owner + "graphLanguage_exact"),
                H("The complete graph language is exact"), StatementSource.FromAuthor(FormulaFor(7)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The graph language equals L_F with every initial vertex allowed. Forward invariance removes the initial finite past from path soundness. Conversely each word in L_F gives a path of its prefix contexts from the empty past. The construction uses one-sided time and requires no negative-time orbit or onto shift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-8"),
                DeclarationHandle.Create(Owner + "vertex_live"),
                H("Every vertex starts a whole path"), StatementSource.FromAuthor(FormulaFor(8)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose a finite past representing the vertex context and a whole continuation witnessing allowedness of its current letter. The prefix-context path of that single admitted concatenation, beginning after the chosen past, starts at the prescribed vertex. Thus no admitted vertex is dead."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-9"),
                DeclarationHandle.Create(Owner + "vertex_nonempty"),
                H("Every stage is nonempty"), StatementSource.FromAuthor(FormulaFor(9)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A word from the nonempty language gives a prefix-context path and therefore an initial vertex. This remains valid for an empty coordinate scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-10"),
                DeclarationHandle.Create(Owner + "restrictVertex_label"),
                H("Labels commute with deletion"), StatementSource.FromAuthor(FormulaFor(10)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vertex map restricts the current symbol and deletes the face-vector components outside the smaller scope. Its label is exactly the coordinate restriction of the original label."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-11"),
                DeclarationHandle.Create(Owner + "restrictVertex_edge"),
                H("Deletion preserves edges"), StatementSource.FromAuthor(FormulaFor(11)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each smaller-scope face is also a larger-scope face. The corresponding derivative equation is literally one of the original edge equations. A projected allowed letter remains allowed by restriction of the common admitted extension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-12"),
                DeclarationHandle.Create(Owner + "restrictVertex_refl"),
                H("Identity on vertices"), StatementSource.FromAuthor(FormulaFor(12)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Restriction from a scope to itself is the identity, including the entire reachable context and its current letter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-13"),
                DeclarationHandle.Create(Owner + "restrictVertex_comp"),
                H("Exact vertex deletion squares"), StatementSource.FromAuthor(FormulaFor(13)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F contained in G contained in H, restricting from H to G and then to F equals restriction directly from H to F. All subface components and symbols coincide; no choice of presentation or representative past enters the maps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-14"),
                DeclarationHandle.Create(Owner + "restrictPath_refl"),
                H("Identity on whole paths"), StatementSource.FromAuthor(FormulaFor(14)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pointwise identity on vertices induces identity on entire path spaces."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-15"),
                DeclarationHandle.Create(Owner + "restrictPath_comp"),
                H("Exact whole-path deletion squares"), StatementSource.FromAuthor(FormulaFor(15)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pointwise composition of vertex restrictions proves composition on complete infinite paths. Equality includes time zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-16"),
                DeclarationHandle.Create(Owner + "restrictPath_surjective"),
                H("Every prescribed whole path lifts"), StatementSource.FromAuthor(FormulaFor(16)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix an arbitrary target path p, its label word z, and one past u representing its initial context. Initial-follower soundness puts the single concatenation uz in L_F. Whole-word coordinate surjectivity gives one w in L_G restricting to uz. At time n choose the context after the first length(u)+n letters of w and the current letter at that time. The resulting graph path restricts to p at every time: its context projects to the context after u followed by the first n letters of z, and its letter projects to z(n). The fine initial context is after a finite past and is not required to be empty. Vertex, edge or label surjectivity alone is not used as a replacement for this assertion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-17"),
                DeclarationHandle.Create(Owner + "projected_path_language"),
                H("Whole-path equality in the graph-language interface"), StatementSource.FromAuthor(FormulaFor(17)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The label map here is the vertex restriction itself. Its complete graph language is exactly the smaller graph path language with identity labels. Edge preservation gives one inclusion; surjectivity of the entire path map gives the other."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-18"),
                DeclarationHandle.Create(Owner + "every_prefix_lifts"),
                H("Compatibility with the existing prefix criterion"), StatementSource.FromAuthor(FormulaFor(18)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite alphabets, every finite prefix of every whole target path lifts through the vertex restriction. This applies the existing graphLanguage_eq_iff_prefix_lifts theorem to the exact whole-path equality. Its finite inverse-system compactness argument is reused rather than reproved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-19"),
                DeclarationHandle.Create(Owner + "vertex_card_bound_product"),
                H("One fixed finite product bound"), StatementSource.FromAuthor(FormulaFor(19)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vertex cardinal is at most the alphabet cardinal times the product of the nonempty-follower cardinals over all subfaces H of F. The injection records the current symbol and all follower components; Nat.card product and Pi formulas supply the estimate. This bound depends only on the once-fixed languages at subfaces of F, independently of every later upper scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-20"),
                DeclarationHandle.Create(Owner + "empty_singleton_loop"),
                H("The empty-scope singleton loop"), StatementSource.FromAuthor(FormulaFor(20)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At the empty scope the alphabet and whole-word type are singletons. Nonemptiness forces its language to contain the unique word, all reachable follower components are the full set, and its unique vertex has a loop."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-21"),
                DeclarationHandle.Create(Owner + "coherent_follower_cover"),
                H("Coherent finite live covers"), StatementSource.FromAuthor(FormulaFor(21)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructed graph stages are finite, nonempty, forward-live and exact presentations of their languages. The vertex and whole-path restrictions have identity and composition laws, preserve labels and edges, and are surjective on whole paths. The all-subface product bound and empty-scope loop describe the size and initial object. These conclusions are conditional on the coherent language family. A coherent family has not been constructed from an arbitrary compact source with shadowing, so original Peng Q5.1 remains open. The result is a general symbolic and topological dynamics bridge and carries no global novelty or official-resolution claim."))),
                DescribeRole.Theorem))));

    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args)
    {
        var head = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (head.Count > 0) head.Add(Dot);
            head.Add(Id(part));
        }
        var items = new List<Formula> { Seq([.. head]), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula All(string x, Formula t) => Seq(Forall, Sp, Id(x), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string x, Formula t) => Seq(Exists, Sp, Id(x), Colon, Sp, t, Comma, Sp);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Inst(Formula t) => Seq(OpenBracket, t, CloseBracket, Comma, Sp);
    private static Formula Ands(params Formula[] fs)
    {
        var items = new List<Formula>();
        foreach (var f in fs)
        {
            if (items.Count > 0) items.AddRange([Sp, Land, Sp]);
            items.AddRange([Open, f, Close]);
        }
        return Seq([.. items]);
    }
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula Type => Id("Type");
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Scope => Call("Finset", Id("I"));
    private static Formula Letter(Formula f) => Call("Letter", Id("A"), f);
    private static Formula Word(Formula f) => Call("ScopedWord", Id("A"), f);
    private static Formula Vertex(Formula f) => Call("S.Vertex", f);
    private static Formula Path(Formula f) => Call("S.Path", f);
    private static Formula Lang(Formula f) => Call("S.language", f);
    private static Formula Graph(Formula f) => Call("graphLanguage", Call("S.Edge", f), Call("S.label", f));
    private static Formula GraphPath(Formula f) => Call("graphLanguage", Call("S.Edge", f), Id("id"));
    private static Formula Restrict(Formula h, Formula v) => Call("S.restrictVertex", h, v);
    private static Formula RestrictPath(Formula h, Formula p) => Call("S.restrictPath", h, p);
    private static Formula FiniteAlphabet => Seq(Grp(), Inst(Seq(All("i", Id("I")), Call("Finite", Call("A", Id("i"))))));
    private static Formula Family(bool system = true) => Seq(
        All("I", Type), All("A", Arr(Id("I"), Type)),
        Inst(Seq(All("i", Id("I")), Call("TopologicalSpace", Call("A", Id("i"))))),
        system ? All("S", Call("LanguageSystem", Id("A"))) : Grp());
    private static Formula Inclusion(string h, string f, string g) =>
        All(h, Seq(Id(f), Sp, Subseteq, Sp, Id(g)));
    private static Formula TwoScopes() => Seq(All("F", Scope), All("G", Scope), Inclusion("h", "F", "G"));
    private static Formula ThreeScopes() => Seq(All("F", Scope), All("G", Scope), All("H", Scope),
        Inclusion("h", "F", "G"), Inclusion("k", "G", "H"));
    private static Formula Reflexive => Call("Subset.refl", Id("F"));
    private static Formula Composite => Call("Subset.trans", Id("h"), Id("k"));
    private static Formula Live(Formula f) => Seq(All("v", Vertex(f)), Ex("p", Path(f)),
        Equal(Call("p", D(0)), Id("v")));
    private static Formula Onto() => Seq(TwoScopes(), Call("Surjective", Call("S.restrictPath", Id("h"))));
    private static Formula VertexIdentity() => Seq(All("F", Scope), All("v", Vertex(Id("F"))),
        Equal(Restrict(Reflexive, Id("v")), Id("v")));
    private static Formula VertexComposition() => Seq(ThreeScopes(), All("v", Vertex(Id("H"))),
        Equal(Restrict(Id("h"), Restrict(Id("k"), Id("v"))), Restrict(Composite, Id("v"))));
    private static Formula LabelLaw() => Seq(TwoScopes(), All("v", Vertex(Id("G"))),
        Equal(Call("S.label", Restrict(Id("h"), Id("v"))),
            Call("restrictLetter", Id("A"), Id("h"), Call("S.label", Id("v")))));
    private static Formula EdgeLaw() => Seq(TwoScopes(), All("v", Vertex(Id("G"))), All("w", Vertex(Id("G"))),
        Arr(Call("S.Edge", Id("v"), Id("w")),
            Call("S.Edge", Restrict(Id("h"), Id("v")), Restrict(Id("h"), Id("w")))));
    private static Formula PathIdentity() => Seq(All("F", Scope), All("p", Path(Id("F"))),
        Equal(RestrictPath(Reflexive, Id("p")), Id("p")));
    private static Formula PathComposition() => Seq(ThreeScopes(), All("p", Path(Id("H"))),
        Equal(RestrictPath(Id("h"), RestrictPath(Id("k"), Id("p"))), RestrictPath(Composite, Id("p"))));
    private static Formula Bound() => Seq(Call("Nat.card", Vertex(Id("F"))), Sp, Le, Sp,
        Call("Nat.card", Letter(Id("F"))), Sp, Cdot, Sp,
        Prod, Underscore, Grp(Seq(Id("H"), Colon, Call("Face", Id("F")))), Sp,
        Call("Nat.card", Call("Followers", Lang(Call("Subtype.val", Id("H"))))));
    private static Formula EmptyLoop() => Ands(Call("Nonempty", Vertex(Emptyset)),
        Call("Subsingleton", Vertex(Emptyset)),
        Seq(All("v", Vertex(Emptyset)), All("w", Vertex(Emptyset)), Call("S.Edge", Id("v"), Id("w"))));
    private static Formula ProjectedLanguage() => Seq(TwoScopes(),
        Equal(Call("graphLanguage", Call("S.Edge", Id("G")), Call("S.restrictVertex", Id("h"))), GraphPath(Id("F"))));
    private static Formula Prefixes() => Seq(TwoScopes(),
        All("p", Arr(Nat, Vertex(Id("F")))),
        Arr(Seq(Id("p"), Sp, InMacro, Sp, GraphPath(Id("F"))),
            Seq(All("m", Nat), Call("PrefixLift", Call("S.Edge", Id("G")), Call("S.restrictVertex", Id("h")), Id("p"), Id("m")))));
    private static Formula FormulaFor(int n)
    {
        if (n <= 2)
        {
            var telescope = Seq(All("A", Type), All("V", Type),
                Inst(Call(n == 1 ? "Fintype" : "Finite", Id("V"))),
                All("e", Arr(Id("V"), Arr(Id("V"), Id("Prop")))), All("ell", Arr(Id("V"), Id("A"))));
            var followers = Call("Followers", Call("graphLanguage", Id("e"), Id("ell")));
            return n switch
            {
                0 => St(telescope, Call("Finite", followers)),
                1 => St(telescope, Seq(Call("Nat.card", followers), Sp, Le, Sp,
                    D(2), Caret, Grp(Call("Fintype.card", Id("V"))))),
                _ => St(All("A", Type), All("L", Call("Set", Call("Word", Id("A")))),
                    Arr(Call("IsSofic", Id("L")), Call("Finite", Call("Followers", Id("L")))))
            };
        }
        return n switch
        {
            3 => St(Family(false), Seq(Call("LanguageSystem", Id("A")), Sp, Eq, Sp,
                OpenBrace, Id("L"), Colon, Seq(Pi, Underscore, Grp(Seq(Id("F"), Colon, Scope)), Sp,
                    Call("Set", Word(Id("F")))), Sp, Mid, Sp,
                Ands(Seq(All("F", Scope), Call("Nonempty", Call("L", Id("F")))),
                    Seq(All("F", Scope), Call("IsClosed", Call("L", Id("F")))),
                    Seq(All("F", Scope), Call("ForwardInvariant", Call("L", Id("F")))),
                    Seq(All("F", Scope), Call("Finite", Call("Followers", Call("L", Id("F"))))),
                    Seq(TwoScopes(), Equal(Call("Set.image", Call("restrictWord", Id("A"), Id("h")), Call("L", Id("G"))), Call("L", Id("F"))))),
                CloseBrace)),
            4 => St(Family(), All("F", Scope), Seq(Call("S.Context", Id("F")), Sp, Eq, Sp,
                OpenBrace, Id("s"), Colon, Call("RawContext", Id("A"), Id("F")), Sp, Mid, Sp,
                Ex("u", Call("List", Letter(Id("F")))),
                Ands(Call("S.IsPrefix", Id("F"), Id("u")), Equal(Id("s"), Call("S.vector", Id("F"), Id("u")))), CloseBrace)),
            5 => St(Family(), All("F", Scope), Seq(Vertex(Id("F")), Sp, Eq, Sp,
                OpenBrace, Open, Id("s"), Comma, Id("a"), Close, Colon,
                Call("S.Context", Id("F")), Sp, Times, Sp, Letter(Id("F")), Sp, Mid, Sp,
                Call("Nonempty", Call("derivative", Call("apply", Call("Subtype.val", Id("s")),
                    Call("topFace", Id("F"))), Id("a"))), CloseBrace)),
            6 => St(Family(), All("F", Scope), All("p", Path(Id("F"))), All("u", Call("List", Letter(Id("F")))),
                Arr(Equal(Call("Subtype.val", Call("context", Call("p", D(0)))), Call("S.vector", Id("F"), Id("u"))),
                    Seq(Call("prepend", Id("u"), Call("S.pathLabels", Id("p"))), Sp, InMacro, Sp, Lang(Id("F"))))),
            7 => St(Family(), All("F", Scope), Equal(Graph(Id("F")), Lang(Id("F")))),
            8 => St(Family(), All("F", Scope), Live(Id("F"))),
            9 => St(Family(), All("F", Scope), Call("Nonempty", Vertex(Id("F")))),
            10 => St(Family(), LabelLaw()),
            11 => St(Family(), EdgeLaw()),
            12 => St(Family(), VertexIdentity()),
            13 => St(Family(), VertexComposition()),
            14 => St(Family(), PathIdentity()),
            15 => St(Family(), PathComposition()),
            16 => St(Family(), Onto()),
            17 => St(Family(), ProjectedLanguage()),
            18 => St(Family(), FiniteAlphabet, Prefixes()),
            19 => St(Family(), FiniteAlphabet, All("F", Scope), Bound()),
            20 => St(Family(), EmptyLoop()),
            21 => St(Family(), FiniteAlphabet,
                Ands(Seq(All("F", Scope), Call("Finite", Vertex(Id("F")))),
                    Seq(All("F", Scope), Call("Nonempty", Vertex(Id("F")))),
                    Seq(All("F", Scope), Live(Id("F"))),
                    Seq(All("F", Scope), Equal(Graph(Id("F")), Lang(Id("F")))),
                    Onto(), VertexIdentity(), VertexComposition(), LabelLaw(), EdgeLaw(),
                    PathIdentity(), PathComposition(), Prefixes(), Seq(All("F", Scope), Bound()), EmptyLoop())),
            _ => throw new ArgumentOutOfRangeException(nameof(n))
        };
    }
}
