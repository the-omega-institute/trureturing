using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class CStarTriangleEqualityUnitalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle equality and norm scale in complex C-star algebras.",
        H("CStarTriangleEqualityUnital"), Blocks(
            Describe.Lean(DescribeId.Create("cstartriangleequalityunital-seminorm-unital-rigidity"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityUnital.seminorm_unital_rigidity"),
                H("seminorm unital rigidity"),
                StatementSource.FromAuthor(Alg(true,All("p",SeminormType(X("A")),Imp(PAdd(X("A"),X("p")),All("a",X("A"),Scale(X("p"),X("a"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("A finite complex seminorm additive on TEA pairs is p(1) times the original norm on a nonzero unital complex C-star algebra. A spectral real-part lower bound and the Russo-Dye convex-hull theorem give the two inequalities."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Ty => Call("Type");
    private static Formula C => Call("Complex");
    private static Formula N(long value) => new Formula.Number(value);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => F.Seq(F.Open, f, F.Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(Formula type, Formula body) => F.Seq(F.OpenBracket, type, F.CloseBracket, F.Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Alg(bool unital, Formula body) => All("A", Ty, Inst(Call(unital ? "CStarAlgebra" : "NonUnitalCStarAlgebra", X("A")), unital ? Inst(Call("Nontrivial", X("A")), body) : body));
    private static Formula Tea(Formula a, Formula b) => Call("TEAPair", a, b);
    private static Formula PAdd(Formula type, Formula p) => All("a", type, All("b", type, Imp(Tea(X("a"), X("b")), Equal(App(p, Add(X("a"), X("b"))), Add(App(p, X("a")), App(p, X("b")))))));
    private static Formula SeminormType(Formula type) => Call("Seminorm", C, type);
    private static Formula Scale(Formula p, Formula a) => Equal(App(p, a), Multiply(App(p, N(1)), Norm(a)));
}
