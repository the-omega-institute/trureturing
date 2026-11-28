using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class KeplerSupportTwoDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/kepler2026balphaspectral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The equivalence-class sum counts Kepler's supports, with two signed vectors per support.",
        H("Counting Kepler's signed support-two eigenvectors"),
        Blocks(
            Describe.Lean(DescribeId.Create("kepler-b-alpha"), DeclarationHandle.Create(Owner + ".bAlpha"),
                H("The Bα matrix"),
                StatementSource.FromAuthor(Disp(MatrixFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Kepler's Definition 1.5, printed p. 1 of arXiv:2607.25221v1, defines the matrix for α in [0,1]. A is the adjacency matrix, D the diagonal degree matrix and L = D − A the graph Laplacian. The same expression defines the Lean matrix for every real α."))),
                DescribeRole.Definition),
            Definition("Twins", "Agreement outside a pair",
                GraphBinders(Vertices("u", "v",
                    IffOf(Call("Twins", V("G"), V("u"), V("v")),
                        All("w", V("V"), Imp(Ne(V("w"), V("u")), Imp(Ne(V("w"), V("v")),
                            IffOf(Adj(V("w"), V("u")), Adj(V("w"), V("v"))))))))),
                "Adjacency is compared at every vertex outside the two named vertices."),
            Definition("signedPair", "Signed coordinate vector", All("V", V("Type"),
                UnderInstance(Call("DecidableEq", V("V")), Vertices("u", "v",
                    Eqn(Call("signedPair", V("u"), V("v")),
                        Seq(QCall("Pi", "single", V("u"), D(1)), Sp, Minus, Sp,
                            QCall("Pi", "single", V("v"), D(1))))))),
                "The first endpoint contributes +1 and the second contributes −1."),
            Definition("pairEigenvalue", "Eigenvalue on a qualifying pair",
                FiniteGraphParameter(Vertices("u", "v",
                    Eqn(Call("pairEigenvalue", V("G"), Alpha, V("u"), V("v")),
                        Seq(Parenthesized(OneMinusAlpha()), Sp, Cdot, Sp,
                            Parenthesized(Typed(QCall("SimpleGraph", "degree", V("G"), V("u")), Reals())),
                            Sp, Minus, Sp, Parenthesized(AdjacencyCoefficient()), Sp, Cdot, Sp,
                            Call("ite", Adj(V("u"), V("v")), D(1), D(0))))), withEquality: false),
                "The degree is cast to the reals. The adjacency term is 1 precisely when the endpoints are adjacent."),
            Definition("classSetoid", "The equivalence relation for the parameter",
                ClassSetoidFormula(),
                "At half the equivalence proof uses reflexivity, symmetry and transitivity of equality of degrees. Away from half it uses the equivalence of outside-adjacency agreement."),
            Definition("classGraph", "The complete graph within each class",
                ClassGraphFormula(),
                "Symmetry reverses the inequality and applies symmetry of the setoid relation. A loop contradicts the inequality at its endpoint."),
            Definition("Class", "Vertices in a quotient class",
                SetoidBinders(All("C", Call("Quotient", V("s")),
                    Eqn(Call("Class", V("s"), V("C")), Subtype("v", V("V"),
                        Eqn(QCall("Quotient", "mk", V("s"), V("v")), V("C")))))),
                "A class is the fiber over its quotient element."),
            Definition("classPairSum", "Sum of binomial class sizes",
                All("V", V("Type"), UnderInstance(Call("Fintype", V("V")), All("s", Call("Setoid", V("V")),
                    Eqn(Call("classPairSum", V("s")), ClassSum(V("s")))))),
                "Each finite class contributes the number of its two-element subsets."),
            Definition("IsSignedEigenvector", "Signed eigenvector predicate",
                SignedEigenvectorFormula(),
                "Remark 4.3 specifies one +1 entry, one −1 entry and zeros elsewhere. The eigen-equation for Bα uses a real eigenvalue.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("SignedEigenvectors", "Type of qualifying vectors",
                FiniteGraphParameter(Eqn(Call("SignedEigenvectors", V("G"), Alpha),
                    Subtype("x", VectorType(), Call("IsSignedEigenvector", V("G"), Alpha, V("x"))))),
                "The subtype counts each signed vector once."),
            Definition("SupportPairs", "Unordered qualifying supports",
                FiniteGraphParameter(Eqn(Call("SupportPairs", V("G"), Alpha),
                    QCall("SimpleGraph", "edgeSet", ClassGraph())), withEquality: false),
                "Edges of the class graph are Mathlib unordered pairs."),
            Definition("directedRealization", "Realization of each oriented dart",
                DirectedRealizationFormula(),
                "The proof p(d) uses the dart's distinct endpoints for the signed coordinates and its class-graph edge for the eigen-equation. The +1 and −1 entries recover the ordered endpoints, so f is injective. For surjectivity, the signed coordinates and eigen-equation give an admissible dart with those endpoints. The inverse chooses a preimage using this surjectivity proof, and injectivity identifies it with that dart."),
            Describe.Lean(DescribeId.Create("kepler-graphwise-count"), DeclarationHandle.Create(Owner + ".graphwise_count"),
                H("Unordered supports and signed eigenvectors"),
                StatementSource.FromAuthor(Disp(CountFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Remark 4.3, printed p. 8, asks “What Theorem 4.2 does not address is how many of these types of eigenvectors a given graph has.” The vector has exactly one +1, one −1 and zeros elsewhere.")),
                    Paragraph(Text("The outside rows give (2α − 1) times the difference of the two adjacency entries. The inside rows give the eigenvalue (1 − α)d − (2α − 1)ε, where d is the common degree and ε indicates the edge within the pair. A class C contributes a pair for each two-element subset. The two oriented darts of each support realize the two opposite signed vectors. Empty and singleton carriers give zero in both counts.")),
                    Paragraph(Text("The source resolution scope is the fixed-graph question in Remark 4.3 together with the Bα definition in Definition 1.5. The Lean result covers every finite simple undirected graph represented by a Mathlib SimpleGraph and every real α, so the source interval [0,1], α = 0, α = 1/2 and α = 1 are included.")),
                    Paragraph(Text("The verified output ends with the exact unordered-support class sum and the exact factor-of-two signed-vector count. Theorems 4.1 and 4.2 supply source context. Their correction, the labeled-graph enumeration, union bound, limiting proportion and half-parameter all-graphs statement lie outside this result."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kepler-2026-remark-4-3-support-two-count"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose,
        AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("kepler-" + name.ToLowerInvariant()), DeclarationHandle.Create(Owner + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Member(Formula owner, string name) => Seq(owner, Dot, Op(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Op(name), args);
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Member(Op(owner), name), args);
    private static Formula Parenthesized(Formula term) => Seq(Open, term, Close);
    private static Formula Typed(Formula name, Formula type) => Seq(name, Sp, Colon, Sp, type);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula UnderInstance(Formula type, Formula body) =>
        Seq(Forall, Sp, OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Eqn(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Ne(Formula lhs, Formula rhs) => Seq(lhs, Sp, Neq, Sp, rhs);
    private static Formula And(Formula lhs, Formula rhs) => new Formula.Logic(lhs, FormulaLogicOperator.And, rhs);
    private static Formula IffOf(Formula lhs, Formula rhs) => new Formula.Logic(lhs, FormulaLogicOperator.Iff, Parenthesized(rhs));
    private static Formula Imp(Formula lhs, Formula rhs) => new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.Implies, rhs);
    private static Formula Vertices(string first, string second, Formula body) =>
        All(first, V("V"), All(second, V("V"), body));
    private static Formula GraphBinders(Formula body) =>
        All("V", V("Type"), All("G", Call("SimpleGraph", V("V")), body));
    private static Formula SetoidBinders(Formula body) =>
        All("V", V("Type"), All("s", Call("Setoid", V("V")), body));
    private static Formula FiniteGraphParameter(Formula body, bool withEquality = true)
    {
        Formula graph = All("G", Call("SimpleGraph", V("V")),
            UnderInstance(Call("DecidableRel", Member(V("G"), "Adj")),
                Seq(Forall, Sp, Typed(Alpha, Reals()), Comma, Sp, body)));
        return All("V", V("Type"), UnderInstance(Call("Fintype", V("V")),
            withEquality ? UnderInstance(Call("DecidableEq", V("V")), graph) : graph));
    }

    private static Formula Subtype(string variable, Formula type, Formula predicate) =>
        Seq(OpenBrace, Typed(V(variable), type), Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula VectorType() => Seq(V("V"), Sp, To, Sp, Reals());
    private static Formula Adj(Formula u, Formula v) => QCall("SimpleGraph", "Adj", V("G"), u, v);
    private static Formula OneMinusAlpha() => Seq(D(1), Sp, Minus, Sp, Alpha);
    private static Formula AdjacencyCoefficient() => Seq(D(2), Sp, Cdot, Sp, Alpha, Sp, Minus, Sp, D(1));
    private static Formula ClassSetoid() => Call("classSetoid", V("G"), Alpha);
    private static Formula ClassGraph() => Call("classGraph", ClassSetoid());

    private static Formula Tuple(params Formula[] entries)
    {
        var items = new List<Formula> { Langle, Sp };
        for (int i = 0; i < entries.Length; i++)
        {
            if (i > 0)
                items.AddRange([Comma, Sp]);
            items.Add(entries[i]);
        }
        items.Add(Rangle);
        return Seq([.. items]);
    }

    private static Formula ClassSetoidFormula()
    {
        Formula r = V("r"), h = V("h"), u = V("u"), v = V("v"), g = V("G");
        Formula sameDegree = Seq(LambdaLower, Sp, u, Sp, v, Dot, Sp,
            Eqn(QCall("SimpleGraph", "degree", g, u), QCall("SimpleGraph", "degree", g, v)));
        return FiniteGraphParameter(new Formula.Aligned([
            Eqn(r, Call("ite", Eqn(Alpha, new Formula.Fraction(D(1), D(2))),
                sameDegree, Call("Twins", g))),
            Typed(h, Call("Equivalence", r)),
            Eqn(ClassSetoid(), Tuple(r, h)),
        ]), withEquality: false);
    }

    private static Formula ClassGraphFormula()
    {
        Formula a = V("a"), h = V("h"), k = V("k"), u = V("u"), v = V("v"), s = V("s");
        return SetoidBinders(new Formula.Aligned([
            Eqn(a, Seq(LambdaLower, Sp, u, Sp, v, Dot, Sp,
                And(Ne(u, v), App(Member(s, "r"), u, v)))),
            Seq(Typed(h, QCall("Std", "Symm", a)), Quad, Sp, Typed(k, QCall("Std", "Irrefl", a))),
            Eqn(Call("classGraph", s), Tuple(a, h, k)),
        ]));
    }

    private static Formula DirectedRealizationFormula()
    {
        Formula d = V("d"), x = V("x"), f = V("f"), h = V("h"), p = V("p");
        Formula darts = V("D"), vectors = V("S");
        Formula realization = Call("directedRealization", V("G"), Alpha);
        Formula coordinates = Call("signedPair", Member(d, "fst"), Member(d, "snd"));
        Formula preimage = App(Member(h, "surjective"), x);
        return FiniteGraphParameter(new Formula.Aligned([
            Eqn(darts, QCall("SimpleGraph", "Dart", ClassGraph())),
            Eqn(vectors, Call("SignedEigenvectors", V("G"), Alpha)),
            Typed(p, All("d", darts, Call("IsSignedEigenvector", V("G"), Alpha, coordinates))),
            Eqn(Parenthesized(Typed(f, Seq(darts, Sp, To, Sp, vectors))),
                Seq(LambdaLower, Sp, Typed(d, darts), Dot, Sp, Tuple(coordinates, App(p, d)))),
            Typed(h, QCall("Function", "Bijective", f)),
            Eqn(Parenthesized(Typed(realization, Seq(darts, Sp, Equiv, Sp, vectors))),
                QCall("Equiv", "ofBijective", f, h)),
            All("x", vectors, Eqn(App(Member(realization, "invFun"), x), QCall("Classical", "choose", preimage))),
        ]));
    }

    private static Formula SignedEigenvectorFormula()
    {
        Formula u = V("u"), v = V("v"), w = V("w"), x = V("x");
        Formula outside = All("w", V("V"), Imp(Ne(w, u), Imp(Ne(w, v), Eqn(App(x, w), D(0)))));
        Formula coordinates = And(Eqn(App(x, u), D(1)), And(Eqn(App(x, v), Seq(Minus, D(1))), outside));
        Formula endpoints = ExistsIn("u", V("V"), ExistsIn("v", V("V"), And(Ne(u, v), coordinates)));
        Formula eigenEquation = ExistsIn("l", Reals(),
            Eqn(QCall("Matrix", "mulVec", Call("bAlpha", V("G"), Alpha), x), Seq(V("l"), Sp, Cdot, Sp, x)));
        return FiniteGraphParameter(All("x", VectorType(),
            IffOf(Call("IsSignedEigenvector", V("G"), Alpha, x),
                And(Parenthesized(endpoints), Parenthesized(eigenEquation)))));
    }

    private static Formula MatrixFormula()
    {
        Formula adjacency = QCall("SimpleGraph", "adjMatrix", V("G"), Reals());
        Formula laplacian = QCall("SimpleGraph", "lapMatrix", V("G"), Reals());
        return FiniteGraphParameter(Eqn(Call("bAlpha", V("G"), Alpha),
            Seq(Alpha, Sp, Cdot, Sp, adjacency, Sp, Plus, Sp, Parenthesized(OneMinusAlpha()), Sp, Cdot, Sp, laplacian)));
    }

    private static Formula ClassSum(Formula relation)
    {
        Formula classes = new Formula.Subscript(Sum, Typed(V("C"), Call("Quotient", relation)));
        Formula size = QCall("Nat", "card", Call("Class", relation, V("C")));
        return Seq(classes, Sp, QCall("Nat", "choose", size, D(2)));
    }

    private static Formula CountFormula()
    {
        Formula total = Call("classPairSum", ClassSetoid());
        Formula supports = QCall("Nat", "card", Call("SupportPairs", V("G"), Alpha));
        Formula vectors = QCall("Nat", "card", Call("SignedEigenvectors", V("G"), Alpha));
        return FiniteGraphParameter(And(Eqn(supports, total), Eqn(vectors, Seq(D(2), Sp, Cdot, Sp, total))));
    }
}
