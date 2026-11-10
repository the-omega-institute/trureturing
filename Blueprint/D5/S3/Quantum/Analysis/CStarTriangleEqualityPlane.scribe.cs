using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class CStarTriangleEqualityPlaneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle equality and norm scale in complex C-star algebras.",
        H("CStarTriangleEqualityPlane"), Blocks(
            Describe.Lean(DescribeId.Create("cstartriangleequalityplane-normparallel"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.NormParallel"),
                H("NormParallel"),
                StatementSource.FromAuthor(Space("E", All("a", X("E"), All("b", X("E"), Equal(Call("NormParallel", X("a"), X("b")), Ex("mu", C, And(Equal(Norm(X("mu")), N(1)), Equal(Norm(Add(X("a"), Smul(X("mu"), X("b")))), Add(Norm(X("a")), Norm(X("b"))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Page 1: Two elements a, b in a normed space E over 𝔽 = ℝ or ℂ are said to be norm parallel, or simply parallel, if ‖a + λb‖ = ‖a‖ + ‖b‖ for some λ ∈ 𝔽 with |λ| = 1. Here the field is complex, and zero elements are included."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cstartriangleequalityplane-teapair"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.TEAPair"),
                H("TEAPair"),
                StatementSource.FromAuthor(All("E", Ty, Inst(Call("NormedAddCommGroup", X("E")), All("a", X("E"), All("b", X("E"), Equal(Tea(X("a"), X("b")), Parenthesized(TeaBody(X("a"), X("b"))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Page 1: In this case, we write a ∥ b. If this equality holds specifically with λ = 1, then (a, b) is called a triangle equality attaining (TEA) pair. Thus TEAPair means equality in the triangle inequality, with no phase adjustment."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cstartriangleequalityplane-affinefaceplane"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.affineFacePlane"),
                H("affineFacePlane"),
                StatementSource.FromAuthor(All("X", Ty, Inst(Call("TopologicalSpace", X("X")), Inst(Call("CompactSpace", X("X")), All("t", Call("ContinuousMap", X("X"), R), All("ht", All("x", X("X"), new Formula.Relation(App(X("t"), X("x")), FormulaRelationOperator.MemberOf, App(Q("Set", "Icc"), N(0), N(1)))), All("xzero", X("X"), All("xone", X("X"), All("hzero", Equal(App(X("t"), X("xzero")), N(0)), All("hone", Equal(App(X("t"), X("xone")), N(1)), All("v", Product(C,C), All("x", X("X"), Equal(App(Call("affineFacePlane", X("t"), X("ht"), X("xzero"), X("xone"), X("hzero"), X("hone")), X("v"), X("x")), Add(Multiply(Parenthesized(Subtract(N(1), Parenthesized(F.Seq(App(X("t"), X("x")), F.Colon, C)))), App(Q("Prod","fst"), X("v"))), Multiply(Parenthesized(F.Seq(App(X("t"), X("x")), F.Colon, C)), App(Q("Prod","snd"), X("v"))))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("A continuous real function with values in [0,1] attaining both endpoints defines this complex-linear isometric map from the sup-norm plane into ContinuousMap X Complex. Its value is displayed at every point; ht, hzero and hone are the indicated proofs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cstartriangleequalityplane-seminorm-on-isometric-plane"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_on_isometric_plane"),
                H("seminorm on isometric plane"),
                StatementSource.FromAuthor(Space("F", All("p", SeminormType(X("F")), Imp(PAdd(X("F"), X("p")), All("J", Isometric(Product(C,C), X("F")), All("v", Product(C,C), Equal(App(X("p"), App(X("J"), X("v"))), Multiply(App(X("p"), App(X("J"), Pair(N(1),N(0)))), Norm(X("v")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Pullback along any complex-linear isometric embedding of the complex sup plane forces a common seminorm scale. The seminorm may vanish, and the embedding need not have an algebraic image."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cstartriangleequalityplane-seminorm-orthogonal-axes"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_orthogonal_axes"),
                H("seminorm orthogonal axes"),
                StatementSource.FromAuthor(Alg(false, All("p", SeminormType(X("A")), Imp(PAdd(X("A"), X("p")), All("a", X("A"), All("b", X("A"), Imp(Equal(Norm(X("a")), N(1)), Imp(Equal(Norm(X("b")), N(1)), Imp(And(Equal(Multiply(Call("star", X("a")), X("b")), N(0)), Equal(Multiply(X("a"), Call("star", X("b"))), N(0))), Equal(App(X("p"), X("a")), App(X("p"), X("b")))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Two C-star orthogonal elements of norm one have equal values under a complex seminorm additive on TEA pairs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cstartriangleequalityplane-seminorm-orthogonal-unit-scale"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_orthogonal_unit_scale"),
                H("seminorm orthogonal unit scale"),
                StatementSource.FromAuthor(Alg(false, All("p", SeminormType(X("A")), Imp(PAdd(X("A"), X("p")), All("x", X("A"), All("g", X("A"), Imp(Equal(Norm(X("g")), N(1)), Imp(Equal(Multiply(Call("star", X("x")), X("g")), N(0)), Imp(Equal(Multiply(X("x"), Call("star", X("g"))), N(0)), Equal(App(X("p"), X("x")), Multiply(App(X("p"), X("g")), Norm(X("x"))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("An element orthogonal on both sides to a norm-one element has the scale fixed by that element; the first element may be zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cstartriangleequalityplane-seminorm-product-rigidity"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_product_rigidity"),
                H("seminorm product rigidity"),
                StatementSource.FromAuthor(Space("E",Space("F",All("p",SeminormType(Product(X("E"),X("F"))),Imp(PAdd(Product(X("E"),X("F")),X("p")),All("ezero",X("E"),All("fzero",X("F"),Imp(Equal(Norm(X("ezero")),N(1)),Imp(Equal(Norm(X("fzero")),N(1)),All("v",Product(X("E"),X("F")),Equal(App(X("p"),X("v")),Multiply(App(X("p"),Pair(X("ezero"),N(0))),Norm(X("v")))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("A finite complex seminorm additive on TEA pairs of a sup product has one norm scale when both factors contain a unit vector. The scale can be zero."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Ty => Call("Type");
    private static Formula C => Call("Complex");
    private static Formula R => Call("Real");
    private static Formula N(long value) => new Formula.Number(value);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => F.Seq(F.Open, f, F.Close);
    private static Formula Q(string owner, string name) => F.Seq(F.Operatorname, F.Grp(X(owner)), F.Dot, F.Operatorname, F.Grp(X(name)));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(Formula type, Formula body) => F.Seq(F.OpenBracket, type, F.CloseBracket, F.Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Smul(Formula a, Formula b) => App(Q("HSMul", "hSMul"), a, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(F.Seq(a, F.Comma, b));
    private static Formula Space(string name, Formula body) => All(name, Ty, Inst(Call("NormedAddCommGroup", X(name)), Inst(Call("NormedSpace", C, X(name)), body)));
    private static Formula Alg(bool unital, Formula body) => All("A", Ty, Inst(Call(unital ? "CStarAlgebra" : "NonUnitalCStarAlgebra", X("A")), unital ? Inst(Call("Nontrivial", X("A")), body) : body));
    private static Formula Tea(Formula a, Formula b) => Call("TEAPair", a, b);
    private static Formula TeaBody(Formula a, Formula b) => Equal(Norm(Add(a, b)), Add(Norm(a), Norm(b)));
    private static Formula PAdd(Formula type, Formula p) => All("a", type, All("b", type, Imp(Tea(X("a"), X("b")), Equal(App(p, Add(X("a"), X("b"))), Add(App(p, X("a")), App(p, X("b")))))));
    private static Formula SeminormType(Formula type) => Call("Seminorm", C, type);
    private static Formula Isometric(Formula a, Formula b) => Call("LinearIsometry", App(Q("RingHom", "id"), C), a, b);
    private static Formula Product(Formula a, Formula b) => F.Seq(a, F.Sp, F.Times, F.Sp, b);
}
