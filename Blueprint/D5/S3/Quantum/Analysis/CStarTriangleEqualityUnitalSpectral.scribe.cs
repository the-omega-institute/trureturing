using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class CStarTriangleEqualityUnitalSpectralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle equality and norm scale in complex C-star algebras.",
        H("CStarTriangleEqualityUnitalSpectral"), Blocks(
            Describe.Lean(DescribeId.Create("cstartriangleequalityunitalspectral-seminorm-spectral-plane-scale"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.seminorm_spectral_plane_scale"),
                H("seminorm spectral plane scale"),
                StatementSource.FromAuthor(Alg(true, All("p", SeminormType(X("A")), Imp(PAdd(X("A"), X("p")), All("h", X("A"), Imp(Call("IsSelfAdjoint", X("h")), All("alpha", C, All("beta", C, Scale(X("p"), Add(Smul(X("alpha"),N(1)), Smul(X("beta"),X("h")))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Spectral endpoint evaluation identifies the affine span of the identity and any selfadjoint element with a complex sup plane. The seminorm scale there is its value at the identity; no continuity assumption occurs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cstartriangleequalityunitalspectral-seminorm-unital-lipschitz"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.seminorm_unital_lipschitz"),
                H("seminorm unital lipschitz"),
                StatementSource.FromAuthor(Alg(true, All("p", SeminormType(X("A")), Imp(PAdd(X("A"), X("p")), Call("LipschitzWith", Parenthesized(F.Seq(App(Q("Subtype","mk"),Multiply(N(2),App(X("p"),N(1))),new Formula.Placeholder()),F.Colon,Call("NNReal"))), X("p")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("The decomposition into real and imaginary selfadjoint parts gives Lipschitz constant 2 p(1). The NNReal constant is Subtype.mk of 2 p(1); the dot denotes the proof that this value is nonnegative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cstartriangleequalityunitalspectral-norm-one-add-skew-quadratic"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.norm_one_add_skew_quadratic"),
                H("norm one add skew quadratic"),
                StatementSource.FromAuthor(Alg(true, All("h", X("A"), Imp(Call("IsSelfAdjoint", X("h")), All("s", R, And(Le(N(0), Subtract(Norm(Add(N(1),Smul(X("s"),Smul(Q("Complex","I"),X("h"))))),N(1))), Le(Subtract(Norm(Add(N(1),Smul(X("s"),Smul(Q("Complex","I"),X("h"))))),N(1)),Multiply(new Formula.Power(X("s"),N(2)),new Formula.Power(Norm(X("h")),N(2)))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("The norm increment in a skew-adjoint direction lies between zero and s squared times the squared norm of h, for every real s and selfadjoint h."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cstartriangleequalityunitalspectral-seminorm-normal-scale"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.seminorm_normal_scale"),
                H("seminorm normal scale"),
                StatementSource.FromAuthor(Alg(true, All("p", SeminormType(X("A")), Imp(PAdd(X("A"),X("p")), All("a",X("A"),Inst(Call("IsStarNormal",X("a")),Scale(X("p"),X("a")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("For every normal element, spectral norm attainment determines the same scale p(1). The statement includes all unitary elements."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Ty => Call("Type");
    private static Formula C => Call("Complex");
    private static Formula R => Call("Real");
    private static Formula N(long value) => new Formula.Number(value);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => F.Seq(F.Open, f, F.Close);
    private static Formula Q(string owner, string name) => F.Seq(F.Operatorname, F.Grp(X(owner)), F.Dot, F.Operatorname, F.Grp(X(name)));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(Formula type, Formula body) => F.Seq(F.OpenBracket, type, F.CloseBracket, F.Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Smul(Formula a, Formula b) => App(Q("HSMul", "hSMul"), a, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Alg(bool unital, Formula body) => All("A", Ty, Inst(Call(unital ? "CStarAlgebra" : "NonUnitalCStarAlgebra", X("A")), unital ? Inst(Call("Nontrivial", X("A")), body) : body));
    private static Formula Tea(Formula a, Formula b) => Call("TEAPair", a, b);
    private static Formula PAdd(Formula type, Formula p) => All("a", type, All("b", type, Imp(Tea(X("a"), X("b")), Equal(App(p, Add(X("a"), X("b"))), Add(App(p, X("a")), App(p, X("b")))))));
    private static Formula SeminormType(Formula type) => Call("Seminorm", C, type);
    private static Formula Scale(Formula p, Formula a) => Equal(App(p, a), Multiply(App(p, N(1)), Norm(a)));
}
