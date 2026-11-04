using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class BochniakChelstowskiKasprzakSoltanQuantumTwinsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/bochniak2025quantumtwins");
    private static readonly Formula C = Seq(Mathbb, Grp(F.Id("C")));
    private static readonly Formula V = F.Id("V");
    private static readonly Formula G = F.Id("G");
    private static readonly Formula B = F.Id("B");
    private static readonly Formula Functions = Arrow(V, C);
    private static readonly Formula Hom = Call("AlgHom", C, Functions, B);
    private static readonly Formula Words = Arrow(Call("Fin", D(4)), Name("Bool"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacency determines algebra homomorphisms for finite twin-free graphs.",
        H("Quantum twins and neighbourhood separation"),
        Blocks(
            Paragraph(Text(
                "For a finite vertex type V, the algebra V → ℂ has pointwise operations. "
                + "The graph adjacency operator sends a point indicator to its neighbourhood indicator. "
                + "Two vertices are ordinary twins when all their adjacency entries agree. "
                + "The homomorphism target B may be noncommutative and has no finite dimension requirement. "
                + "Displayed square brackets are anonymous Lean instance arguments. "
                + "In the graph structure expression, the proof fields symm and loopless are suppressed; "
                + "they assert symmetry and irreflexivity of the displayed adjacency relation.")),
            Node("adjacencyOperator", "The adjacency operator", AdjacencyFormula(),
                "For the classical graph, C(G) = V → ℂ and A_G acts by summing over adjacent vertices. "
                + "Here adjacencyOperator G is exactly Matrix.toLin' of SimpleGraph.adjMatrix ℂ G, "
                + "with its usual row action on column functions. This is the classical specialization "
                + "of the adjacency operator used in Section 3 of the source.",
                AssessedProvenance.FromLiterature(Source)),
            Node("HasTwinsIn", "Distinct homomorphisms agreeing after adjacency", TwinsFormula(),
                "Definition 3.8, p. 10: “Let G = (V_G, ψ_G, A_G) be a quantum graph and H be a compact quantum group. "
                + "We say that G has H-twin vertices, or simply H-twins, if there exists a pair of different actions of H on G "
                + "ρ₁, ρ₂ : C(G) → C(G) ⊗ C(H) such that ρ₁ ∘ A_G = ρ₂ ∘ A_G. (4) "
                + "We say that G has quantum twin vertices if there exists a quantum group H such that G has H-twins.” "
                + "HasTwinsIn retains distinctness and equality after adjacency while allowing all unital complex algebra "
                + "homomorphisms into an arbitrary complex algebra B. It does not assert the existence of quantum group actions.",
                AssessedProvenance.FromLiterature(Source)),
            Node("prism", "The prism on the complete graph with five vertices",
                Equal(Typed(Call("prism"), Call("SimpleGraph", Product(Call("Fin", D(2)), Call("Fin", D(5))))),
                    Apply(Q("SimpleGraph", "boxProd"),
                        Apply(Q("SimpleGraph", "completeGraph"), Call("Fin", D(2))),
                        Apply(Q("SimpleGraph", "completeGraph"), Call("Fin", D(5))))),
                "The source, p. 13, calls K₂ □ K₅ “the so-called prism having a basis in K₅”. "
                + "The vertices are pairs in Fin 2 × Fin 5, and SimpleGraph.boxProd is the Cartesian graph product.",
                AssessedProvenance.FromLiterature(Source)),
            Node("cycleProduct", "The Cartesian product of two cycles",
                Equal(Typed(Call("cycleProduct"), Call("SimpleGraph", Product(Call("Fin", D(4)), Call("Fin", D(3))))),
                    Apply(Q("SimpleGraph", "boxProd"),
                        Apply(Q("SimpleGraph", "cycleGraph"), D(4)),
                        Apply(Q("SimpleGraph", "cycleGraph"), D(3)))),
                "The second graph on p. 13 is C₄ □ C₃. Its vertices are pairs in Fin 4 × Fin 3, "
                + "with each cycle and their Cartesian product supplied by SimpleGraph.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The negative answer in a larger class of homomorphisms",
                Equal(Typed(Call("claim"), Name("Prop")), ClaimBody()),
                "Question 3.17, p. 13: “Do the above-mentioned graphs possess quantum twin vertices?” "
                + "The graphs are K₂ □ K₅, C₄ □ C₃ and the tesseract. The last has vertex type Fin 4 → Bool "
                + "and adjacency hammingDist u v = 1. The formula asserts, for every complex target algebra, "
                + "the absence of two distinct homomorphisms agreeing after adjacency, separately for each graph. "
                + "Since a compact quantum group action is a unital complex algebra homomorphism into C(G) ⊗ C(H), "
                + "this stronger assertion implies a negative answer to the question. The compact quantum group axioms "
                + "and the action-to-homomorphism passage are explained here and are not formalized in this module.",
                AssessedProvenance.FromLiterature(Source)),
            Theorem("algHom_eq_of_adjacency_eq", "Rigidity for every finite twin-free graph", RigidityFormula(),
                "Fix a vertex x. Multiply its adjacent neighbourhood indicators and the complements of its nonadjacent "
                + "neighbourhood indicators. At x every factor is one. At any other vertex y, injectivity of adjacency "
                + "rows supplies a factor that vanishes. Thus this product is Pi.single x 1. "
                + "The equalizer subalgebra of the two homomorphisms contains all neighbourhood indicators, "
                + "hence these products and all point indicators. Every function is the sum of its values times "
                + "the point indicators, so the equalizer is the whole function algebra."),
            Theorem("result", "None of the three graphs has quantum twins", ClaimBody(),
                "The adjacency rows of each of the three graphs are distinct. Apply the rigidity theorem "
                + "to each graph and to every complex target algebra B. This excludes the two distinct "
                + "homomorphisms required by HasTwinsIn. The proof uses no invertibility of the adjacency matrix. "
                + "The general rigidity theorem covers every finite simple graph whose ordinary twin classes are singletons."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("quantum-twins-" + name.ToLowerInvariant()), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create("quantum-twins-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem,
        openProblemResolutionClaim: name == "result"
            ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("bochniak-chelstowski-kasprzak-soltan-2025-quantum-twin-vertices"),
                ResolutionKind.Proved)
            : null);

    private static Formula AdjacencyFormula() => GraphParameters(Equal(
        Typed(Call("adjacencyOperator", G), Call("LinearMap", Apply(Q("RingHom", "id"), C), Functions, Functions)),
        Apply(Seq(Q("Matrix", "toLin"), Apos), Apply(Q("SimpleGraph", "adjMatrix"), C, G))));

    private static Formula TwinsFormula()
    {
        Formula rhoone = new Formula.Subscript(Rho, D(1));
        Formula rhotwo = new Formula.Subscript(Rho, D(2));
        Formula agreement = All(F.Id("f"), Functions, Equal(
            Apply(rhoone, Call("adjacencyOperator", G, F.Id("f"))),
            Apply(rhotwo, Call("adjacencyOperator", G, F.Id("f")))));
        Formula twins = ExistsOf(rhoone, Hom,
            ExistsOf(rhotwo, Hom, And(NotEqual(rhoone, rhotwo), agreement)));
        return GraphParameters(TargetParameters(Equal(
            Typed(Call("HasTwinsIn", G, B), Name("Prop")), twins)));
    }

    private static Formula RigidityFormula() => GraphParameters(ImpliesFormula(
        All(F.Id("x"), V, All(F.Id("y"), V, ImpliesFormula(
            All(F.Id("v"), V, IffFormula(
                Apply(Q("SimpleGraph", "Adj"), G, F.Id("x"), F.Id("v")),
                Apply(Q("SimpleGraph", "Adj"), G, F.Id("y"), F.Id("v")))),
            Equal(F.Id("x"), F.Id("y"))))),
        TargetParameters(All(Phi, Hom, All(Psi, Hom, ImpliesFormula(
            All(F.Id("f"), Functions, Equal(Apply(Phi, Call("adjacencyOperator", G, F.Id("f"))),
                Apply(Psi, Call("adjacencyOperator", G, F.Id("f"))))), Equal(Phi, Psi)))))));

    private static Formula ClaimBody() => TargetParameters(And(
        Negate(Call("HasTwinsIn", Call("prism"), B)),
        And(Negate(Call("HasTwinsIn", Call("cycleProduct"), B)),
            Negate(Call("HasTwinsIn", TesseractExpression(), B)))));

    private static Formula TesseractExpression() => Typed(Seq(OpenBrace,
        Q("Adj"), Sp, Colon, Eq, Sp,
        LambdaOf(F.Id("u"), Words, LambdaOf(F.Id("v"), Words,
            Equal(Call("hammingDist", F.Id("u"), F.Id("v")), D(1)))),
        Comma, Sp, Q("symm"), Sp, Colon, Eq, Sp, Dot, Dot, Dot,
        Comma, Sp, Q("loopless"), Sp, Colon, Eq, Sp, Dot, Dot, Dot, CloseBrace), Call("SimpleGraph", Words));

    private static Formula GraphParameters(Formula body) => All(V, Name("Type"),
        Instance(Call("Fintype", V), All(G, Call("SimpleGraph", V), body)));
    private static Formula TargetParameters(Formula body) => All(B, Name("Type"),
        Instance(Call("Ring", B), Instance(Call("Algebra", C, B), body)));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name))));
    private static Formula Q(string name) => Name(name);
    private static Formula Call(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Name(name) : Apply(Name(name), arguments);
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula ExistsOf(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(Formula name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(name, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Product(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Times, Sp, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Negate(Formula value) => Seq(Neg, Sp, Parenthesized(value));
}
