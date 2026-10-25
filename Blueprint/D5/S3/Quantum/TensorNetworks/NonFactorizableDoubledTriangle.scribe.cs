using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class NonFactorizableDoubledTriangleDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/delascuevasetal2024invariantpolynomialdecompositions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A doubled triangle with simultaneous exchange of edge copies has no local factorization.",
        H("A nonfactorizable doubled triangle"),
        Blocks(
            Paragraph(Text(
                "Vertices are indexed by Fin (n + 1). A and B denote the specified actions on vertices and multifacets, respectively. "
                    + "Membership proofs in subtype constructors are implicit; these proofs do not affect values.")),
            Node("weighted-simplicial-complex", "WeightedSimplicialComplex", "Weighted simplicial complexes",
                WeightedFormula(), AssessedProvenance.FromLiterature(Source),
                "A natural weight is assigned to every vertex subset. Weights divide the weights of larger subsets, "
                    + "and every singleton has nonzero weight. These are the divisibility condition and standing singleton assumption "
                    + "of Definition def:wsc, TeX lines 318–327."),
            Node("multifacet", "Multifacet", "Distinct copies of each facet",
                MultifacetFormula(), AssessedProvenance.FromLiterature(Source),
                "A facet is a vertex subset maximal among those of nonzero weight. A multifacet consists of a facet F "
                    + "and an index in Fin (ω F), giving exactly ω F distinct copies. This is the multifacet multiset "
                    + "of Definition def:wsc, TeX lines 327–332, expressed as a dependent sum."),
            Node("collapse", "collapse", "Forgetting the copy index",
                CollapseFormula(), AssessedProvenance.FromLiterature(Source),
                "Collapse sends a multifacet to its underlying vertex subset by projecting its facet and then its subset. "
                    + "It is the canonical collapse map of TeX line 332."),
            Node("incident", "Incident", "Multifacets incident to a vertex",
                IncidentFormula(), AssessedProvenance.FromLiterature(Source),
                "The local multifacets at i are exactly the multifacets whose underlying facet contains i. "
                    + "This retains each copy separately, as in TeX lines 330–332."),
            Node("compatible", "Compatible", "Compatible vertex and multifacet actions",
                CompatibleFormula(), AssessedProvenance.FromLiterature(Source),
                "The vertex action preserves every weight, and collapse intertwines the multifacet action with the induced action "
                    + "on vertex subsets. These are precisely the two requirements in the definition of an action on a weighted "
                    + "simplicial complex, TeX lines 425–435. No finiteness assumption on G is needed here."),
            Node("transport", "transport", "Inverse pullback of local labels",
                TransportFormula(), AssessedProvenance.FromLiterature(Source),
                "A local labeling β at i is transported to the labeling at g i that evaluates β on the inverse translate "
                    + "of each multifacet. Collapse compatibility ensures that this inverse translate is incident to i. "
                    + "This is the inverse pullback action on functions and translated subsets of TeX lines 405–413."),
            Node("k", "K", "The stabilizer count",
                KFormula(), AssessedProvenance.FromLiterature(Source),
                "For a labeling α, count all global labelings γ whose restriction at each vertex can be changed into the "
                    + "restriction of α by an element fixing that vertex. The group element may be chosen independently "
                    + "at every vertex. This is K in TeX lines 1519–1521. The definition uses Nat.card for an arbitrary label type ι; "
                    + "the factorization equations below use finite label types."),
            Node("factorizable", "Factorizable", "Positive equivariant local factorization",
                FactorizableFormula(), AssessedProvenance.FromLiterature(Source),
                "For every natural m, choose a real factor C i β for each vertex and each local labeling by Fin m. "
                    + "Every factor must be positive, transported local labelings must have the same factor, and the product "
                    + "over vertices must equal the reciprocal of K for every global labeling. K is cast from ℕ to ℝ before inversion. "
                    + "Fin m represents every finite label set, including the empty one. The group is finite. "
                    + "These are the equations and inequalities of TeX lines 1515–1522."),
            Node("claim", "claim", "Universal factorizability",
                ClaimFormula(), AssessedProvenance.FromRepo(Source),
                "Every weighted simplicial complex on Fin (n + 1), with every finite group and every compatible pair of actions, "
                    + "is asserted to be factorizable. Its negation supplies a nonfactorizable structure and hence answers "
                    + "the existence question at TeX lines 1544–1549 affirmatively."),
            Describe.Lean(
                DescribeId.Create("nonfactorizable-doubled-triangle-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The doubled triangle is not factorizable"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "On the vertices 0, 1, 2, give the empty set and singletons weight 1, the three edges weight 2, "
                            + "and the full vertex set weight 0. These weights satisfy divisibility and the singleton condition. "
                            + "The facets are exactly the complements of the single vertices. Index their copies by pairs (e,k) "
                            + "in Fin 3 × Fin 2, where the underlying edge omits e. This indexing is bijective, and a copy "
                            + "is incident to i exactly when i differs from e.")),
                    Paragraph(Text(
                        "Use MulAction.ofEndHom with the constant identity endomorphism homomorphism to let Multiplicative (ZMod 2) fix every vertex. "
                            + "Its identity fixes every copy, and its other element "
                            + "reverses the Fin 2 index on each edge simultaneously. Reversal is an involution, so these maps "
                            + "define a group action. They preserve each underlying edge, while the vertex action preserves every weight; "
                            + "the two actions are therefore compatible.")),
                    Paragraph(Text(
                        "For a,b,c in Fin 2, define αₐᵦ𝒸 by labeling copy 0 of every edge with 0 and copy 1 of the edges "
                            + "omitting 0, 1, 2 with a, b, c, respectively. In these coordinates, equality of the local pullbacks "
                            + "means that, at each vertex i, γ agrees with αₐᵦ𝒸 on all copies of edges not omitting i, "
                            + "either directly or after reversing both copy indices. These are the only two possibilities because "
                            + "the group has two elements, each equal to its inverse. The bijection of copies transfers K to the "
                            + "cardinality of this set of binary functions. Enumerating the eight choices of a,b,c and the binary "
                            + "functions gives K(α₀₀₀) = 1 and K(αₐᵦ𝒸) = 2 for all other choices.")),
                    Paragraph(Text(
                        "For any real local factors C, let Pₐᵦ𝒸 be their product over the three vertices at the restrictions "
                            + "of αₐᵦ𝒸. The restriction at vertex 0 is independent of a, the restriction at vertex 1 is independent "
                            + "of b, and the restriction at vertex 2 is independent of c: each vertex sees only the two edges "
                            + "that contain it. Consequently P₀₀₀ P₀₁₁ P₁₀₁ P₁₁₀ = P₀₀₁ P₀₁₀ P₁₀₀ P₁₁₁. "
                            + "For each vertex, the factors on either side contain each possible pair of the other two binary "
                            + "coordinates exactly once; expanding the products and commuting real factors proves the identity.")),
                    Paragraph(Text(
                        "If the structure were factorizable, take m = 2 in its defining equations. They give P₀₀₀ = 1 "
                            + "and Pₐᵦ𝒸 = 1/2 for all other choices. Substitution into the parity identity yields 1/8 = 1/16, "
                            + "a contradiction. Thus even the product equations have no solution; positivity and equivariance "
                            + "cannot restore one. Finally, applying universal factorizability to n = 2, these weights, this finite "
                            + "group and these compatible actions would give the impossible factorization. Hence claim is false."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("delascuevas-klingler-netzer-2024-nonfactorizable-doubled-triangle"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("nonfactorizable-doubled-triangle-" + id),
            DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula WeightedFormula()
    {
        Formula divisibility = All("S", VertexSets(), All("T", VertexSets(),
            Imp(Rel(X("S"), FormulaRelationOperator.SubsetOf, X("T")),
                Rel(At(X("ω"), X("S")), FormulaRelationOperator.Divides, At(X("ω"), X("T"))))));
        Formula singletons = All("i", Vertices(), NotEqual(
            At(X("ω"), Seq(OpenBrace, X("i"), CloseBrace)), Typed(D(0), Naturals())));
        return WeightBinders(Iff(LocalCall("WeightedSimplicialComplex", X("ω")), And(divisibility, singletons)));
    }

    private static Formula MultifacetFormula()
    {
        Formula facets = SubtypeOf("S", VertexSets(), At(Qualified("Maximal"),
            LambdaOf("T", VertexSets(), NotEqual(At(X("ω"), X("T")), Typed(D(0), Naturals()))), X("S")));
        Formula copies = At(Qualified("Sigma"), LambdaOf("F", facets,
            FinOf(At(X("ω"), At(Qualified("Subtype", "val"), X("F"))))));
        return WeightBinders(Equal(Typed(LocalCall("Multifacet", X("ω")), Type()), copies));
    }

    private static Formula CollapseFormula() => WeightBinders(All("x", Multifacets(),
        Equal(Typed(LocalCall("collapse", X("x")), VertexSets()),
            At(Qualified("Subtype", "val"), At(Qualified("Sigma", "fst"), X("x"))))));

    private static Formula IncidentFormula() => WeightBinders(All("i", Vertices(),
        Equal(Typed(Incident(X("i")), Type()), SubtypeOf("x", Multifacets(),
            Rel(X("i"), FormulaRelationOperator.MemberOf, LocalCall("collapse", X("x")))))));

    private static Formula CompatibleFormula()
    {
        Formula image = LambdaOf("x", Vertices(), Act("A", X("g"), X("x")));
        Formula weights = All("g", X("G"), All("S", VertexSets(), Equal(
            At(X("ω"), At(Qualified("Finset", "image"), image, X("S"))), At(X("ω"), X("S")))));
        Formula collapse = All("g", X("G"), All("x", Multifacets(), Equal(
            LocalCall("collapse", Act("B", X("g"), X("x"))),
            At(Qualified("Finset", "image"), image, LocalCall("collapse", X("x"))))));
        return ActionBinders(Iff(Compatibility(), And(weights, collapse)), finite: false);
    }

    private static Formula TransportFormula()
    {
        Formula target = Incident(Act("A", X("g"), X("i")));
        Formula inverseImage = Act("B", Inverse(X("g")), At(Qualified("Subtype", "val"), X("x")));
        Formula value = LambdaOf("x", target, At(X("β"), Seq(Langle, Sp, inverseImage, Sp, Rangle)));
        Formula equation = Equal(Typed(LocalCall("transport", X("h"), X("g"), X("i"), X("β")), Arrow(target, X("ι"))), value);
        return ActionBinders(All("h", Compatibility(), All("ι", Type(), All("g", X("G"),
            All("i", Vertices(), All("β", Arrow(Incident(X("i")), X("ι")), equation))))), finite: false);
    }

    private static Formula KFormula()
    {
        Formula pullback = LambdaOf("x", Multifacets(), At(X("γ"), Act("B", Inverse(X("g")), X("x"))));
        Formula condition = All("i", Vertices(), Some("g", X("G"), And(
            Equal(Act("A", X("g"), X("i")), X("i")),
            Equal(Restrict(X("i"), pullback), Restrict(X("i"), X("α"))))));
        Formula countedType = SubtypeOf("γ", Arrow(Multifacets(), X("ι")), condition);
        return ActionBinders(All("ι", Type(), All("α", Arrow(Multifacets(), X("ι")),
            Equal(Typed(LocalCall("K", X("G"), X("A"), X("B"), X("α")), Naturals()),
                At(Qualified("Nat", "card"), countedType)))), finite: false);
    }

    private static Formula FactorizableFormula()
    {
        Formula localLabels = Arrow(Incident(X("i")), FinOf(X("m")));
        Formula factorType = PiOf("i", Vertices(), Arrow(localLabels, Reals()));
        Formula positive = All("i", Vertices(), All("β", localLabels,
            Rel(Typed(D(0), Reals()), FormulaRelationOperator.LessThan, At(X("C"), X("i"), X("β")))));
        Formula invariant = All("g", X("G"), All("i", Vertices(), All("β", localLabels,
            Equal(At(X("C"), Act("A", X("g"), X("i")), LocalCall("transport", X("h"), X("g"), X("i"), X("β"))),
                At(X("C"), X("i"), X("β"))))));
        Formula factors = ProductOver("i", Vertices(), At(X("C"), X("i"), Restrict(X("i"), X("α"))));
        Formula realCount = Typed(At(Qualified("Nat", "cast"), LocalCall("K", X("G"), X("A"), X("B"), X("α"))), Reals());
        Formula equations = All("α", Arrow(Multifacets(), FinOf(X("m"))), Equal(factors, Inverse(realCount)));
        Formula solution = All("m", Naturals(), Some("C", factorType, And(positive, And(invariant, equations))));
        return ActionBinders(All("h", Compatibility(), Iff(LocalCall("Factorizable", X("ω"), X("G"), X("A"), X("B"), X("h")), solution)),
            finite: true);
    }

    private static Formula ClaimFormula() => Iff(Local("claim"), WeightBinders(
        Imp(LocalCall("WeightedSimplicialComplex", X("ω")), GroupBinders(
            All("h", Compatibility(), LocalCall("Factorizable", X("ω"), X("G"), X("A"), X("B"), X("h"))), finite: true))));

    private static Formula WeightBinders(Formula body) =>
        All("n", Naturals(), All("ω", Arrow(VertexSets(), Naturals()), body));
    private static Formula ActionBinders(Formula body, bool finite) => WeightBinders(GroupBinders(body, finite));
    private static Formula GroupBinders(Formula body, bool finite)
    {
        Formula actions = All("A", At(Qualified("MulAction"), X("G"), Vertices()),
            All("B", At(Qualified("MulAction"), X("G"), Multifacets()), body));
        if (finite) actions = InstanceOf(At(Qualified("Fintype"), X("G")), actions);
        return All("G", Type(), InstanceOf(At(Qualified("Group"), X("G")), actions));
    }

    private static Formula Compatibility() => LocalCall("Compatible", X("ω"), X("G"), X("A"), X("B"));
    private static Formula Vertices() => FinOf(new Formula.Binary(X("n"), FormulaBinaryOperator.Add, D(1)));
    private static Formula VertexSets() => At(Qualified("Finset"), Vertices());
    private static Formula Multifacets() => LocalCall("Multifacet", X("ω"));
    private static Formula Incident(Formula i) => LocalCall("Incident", X("ω"), i);
    private static Formula Restrict(Formula i, Formula labels) => At(Qualified("Subtype", "restrict"),
        LambdaOf("x", Multifacets(), Rel(i, FormulaRelationOperator.MemberOf, LocalCall("collapse", X("x")))), labels);
    private static Formula Act(string action, Formula g, Formula x) => At(Seq(X(action), Dot, Qualified("smul")), g, x);
    private static Formula Inverse(Formula value) => At(Qualified("Inv", "inv"), value);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Type() => Qualified("Type");
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "TensorNetworks", "NonFactorizableDoubledTriangle", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula X(string name) => name switch
    {
        "ω" => Omega,
        "ι" => Iota,
        "α" => Alpha,
        "β" => Beta,
        "γ" => GammaLower,
        _ => F.Id(name)
    };
    private static Formula Qualified(params string[] names)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(name));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula PiOf(string name, Formula type, Formula body) =>
        new Formula.TypeArrow(Typed(X(name), type), Parenthesized(body));
    private static Formula SubtypeOf(string name, Formula type, Formula predicate) =>
        Seq(OpenBrace, Typed(X(name), type), Sp, Mid, Sp, Parenthesized(predicate), CloseBrace);
    private static Formula InstanceOf(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula ProductOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) => new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => Rel(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
