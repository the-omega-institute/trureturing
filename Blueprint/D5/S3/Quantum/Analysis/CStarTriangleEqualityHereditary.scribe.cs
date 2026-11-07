using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class CStarTriangleEqualityHereditaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle equality and norm scale in complex C-star algebras.",
        H("CStarTriangleEqualityHereditary"), Blocks(
            Describe.Lean(DescribeId.Create("cstartriangleequalityhereditary-seminorm-algebraically-unital-rigidity"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityHereditary.seminorm_algebraically_unital_rigidity"),
                H("seminorm algebraically unital rigidity"),
                StatementSource.FromAuthor(Alg(false,Imp(UnitalHyp(X("A")),All("p",SeminormType(X("A")),Imp(PAdd(X("A"),X("p")),Ex("c",R,And(Le(N(0),X("c")),All("a",X("A"),Equal(App(X("p"),X("a")),Multiply(X("c"),Norm(X("a")))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Existence of an algebraic two-sided identity suffices for the full seminorm conclusion; the zero algebra is included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cstartriangleequalityhereditary-seminorm-cross-scale-of-continuous"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityHereditary.seminorm_cross_scale_of_continuous"),
                H("seminorm cross scale of continuous"),
                StatementSource.FromAuthor(Alg(false,All("p",SeminormType(X("A")),Imp(Call("Continuous",X("p")),Imp(PAdd(X("A"),X("p")),All("a",X("A"),All("b",X("A"),Cross(X("p"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Joint sandwich approximation places two elements in the same closed subalgebra with a contractive local identity. Continuity then transfers the common scale identity to any pair. No separability or countable approximate unit is assumed."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Ty => Call("Type");
    private static Formula C => Call("Complex");
    private static Formula R => Call("Real");
    private static Formula N(long value) => new Formula.Number(value);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => F.Seq(F.Open, f, F.Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(Formula type, Formula body) => F.Seq(F.OpenBracket, type, F.CloseBracket, F.Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Alg(bool unital, Formula body) => All("A", Ty, Inst(Call(unital ? "CStarAlgebra" : "NonUnitalCStarAlgebra", X("A")), unital ? Inst(Call("Nontrivial", X("A")), body) : body));
    private static Formula Tea(Formula a, Formula b) => Call("TEAPair", a, b);
    private static Formula PAdd(Formula type, Formula p) => All("a", type, All("b", type, Imp(Tea(X("a"), X("b")), Equal(App(p, Add(X("a"), X("b"))), Add(App(p, X("a")), App(p, X("b")))))));
    private static Formula SeminormType(Formula type) => Call("Seminorm", C, type);
    private static Formula UnitalHyp(Formula type) => Ex("q", type, All("a", type, And(Equal(Multiply(X("q"), X("a")), X("a")), Equal(Multiply(X("a"), X("q")), X("a")))));
    private static Formula Cross(Formula p) => Equal(Multiply(App(p, X("a")), Norm(X("b"))), Multiply(App(p, X("b")), Norm(X("a"))));
}
