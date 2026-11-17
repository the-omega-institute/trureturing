using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class CStarTriangleEqualityPreserversDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle equality and norm scale in complex C-star algebras.",
        H("CStarTriangleEqualityPreservers"), Blocks(
            Describe.Lean(DescribeId.Create("cstartriangleequalitypreservers-preservesteabothdirections"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.PreservesTEABothDirections"),
                H("PreservesTEABothDirections"),
                StatementSource.FromAuthor(Space("A",Space("B",All("T",Linear(X("A"),X("B")),Equal(Call("PreservesTEABothDirections",X("T")),All("a",X("A"),All("b",X("A"),Iff(Tea(X("a"),X("b")),Tea(App(X("T"),X("a")),App(X("T"),X("b"))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Problem 1.1, page 4: Does the same conclusion hold for arbitrary complex C∗-algebras if TEA pairs are preserved in both directions? Both directions here quantify over every pair in the domain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cstartriangleequalitypreservers-scalarmultipleofisometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.ScalarMultipleOfIsometry"),
                H("ScalarMultipleOfIsometry"),
                StatementSource.FromAuthor(Space("A",Space("B",All("T",Linear(X("A"),X("B")),Equal(Call("ScalarMultipleOfIsometry",X("T")),ScalarBody(X("A"),X("B"),X("T"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Problem 1.1, page 4: For which complex C∗-algebras 𝒜, ℬ must every linear bijection T : 𝒜 → ℬ preserving parallelism in both directions be a scalar multiple of an isometry? Does the same conclusion hold for arbitrary complex C∗-algebras if TEA pairs are preserved in both directions? The scalar gamma is nonzero and U is a surjective complex-linear isometry."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cstartriangleequalitypreservers-claim"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.claim"),
                H("claim"),
                StatementSource.FromAuthor(Equal(Call("claim"),Parenthesized(ClaimBody()))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Problem 1.1, page 4: For which complex C∗-algebras 𝒜, ℬ must every linear bijection T : 𝒜 → ℬ preserving parallelism in both directions be a scalar multiple of an isometry? Does the same conclusion hold for arbitrary complex C∗-algebras if TEA pairs are preserved in both directions? The second sentence is expressed for arbitrary NonUnitalCStarAlgebra carriers A and B and a complex LinearMap T. Function.Bijective supplies both injectivity and surjectivity; no boundedness or continuity is assumed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cstartriangleequalitypreservers-result"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.result"),
                H("result"),
                StatementSource.FromAuthor(ClaimBody()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("A finite complex seminorm additive on original TEA pairs is a nonnegative scalar times the original norm. Applying this to a↦‖T(a)‖, injectivity gives a positive scale on a nonzero algebra and surjectivity gives the isometric equivalence. The zero-algebra case uses scalar one. The argument uses forward preservation; the displayed conclusion retains both directions as in Problem 1.1."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("op-ltww2611tea"),
                    ResolutionKind.Proved)))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Ty => Call("Type");
    private static Formula C => Call("Complex");
    private static Formula N(long value) => new Formula.Number(value);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => F.Seq(F.Open, f, F.Close);
    private static Formula Q(string owner, string name) => F.Seq(F.Operatorname, F.Grp(X(owner)), F.Dot, F.Operatorname, F.Grp(X(name)));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(Formula type, Formula body) => F.Seq(F.OpenBracket, type, F.CloseBracket, F.Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Smul(Formula a, Formula b) => App(Q("HSMul", "hSMul"), a, b);
    private static Formula Space(string name, Formula body) => All(name, Ty, Inst(Call("NormedAddCommGroup", X(name)), Inst(Call("NormedSpace", C, X(name)), body)));
    private static Formula Tea(Formula a, Formula b) => Call("TEAPair", a, b);
    private static Formula TeaBody(Formula a, Formula b) => Equal(Norm(Add(a, b)), Add(Norm(a), Norm(b)));
    private static Formula Linear(Formula a, Formula b) => Call("LinearMap", App(Q("RingHom", "id"), C), a, b);
    private static Formula IsoEquiv(Formula a, Formula b) => Call("LinearIsometryEquiv", App(Q("RingHom", "id"), C), a, b);
    private static Formula BothBody(Formula type, Formula t) => All("a", type, All("b", type, Iff(TeaBody(X("a"), X("b")), TeaBody(App(t, X("a")), App(t, X("b"))))));
    private static Formula ScalarBody(Formula a, Formula b, Formula t) => Ex("gamma", C, Ex("U", IsoEquiv(a, b), And(NotEqual(X("gamma"), N(0)), All("a", a, Equal(App(t, X("a")), Smul(X("gamma"), App(X("U"), X("a"))))))));
    private static Formula ClaimBody() => All("A", Ty, All("B", Ty, Inst(Call("NonUnitalCStarAlgebra", X("A")), Inst(Call("NonUnitalCStarAlgebra", X("B")), All("T", Linear(X("A"), X("B")), Imp(App(Q("Function", "Bijective"), X("T")), Imp(BothBody(X("A"), X("T")), ScalarBody(X("A"), X("B"), X("T")))))))));
}
