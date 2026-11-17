using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class CStarTriangleEqualityNonunitalContinuityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle equality and norm scale in complex C-star algebras.",
        H("CStarTriangleEqualityNonunitalContinuity"), Blocks(
            Describe.Lean(DescribeId.Create("cstartriangleequalitynonunitalcontinuity-seminorm-nonunital-lipschitz"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityNonunitalContinuity.seminorm_nonunital_lipschitz"),
                H("seminorm nonunital lipschitz"),
                StatementSource.FromAuthor(Alg(false,Imp(Not(UnitalHyp(X("A"))),All("p",SeminormType(X("A")),Imp(PAdd(X("A"),X("p")),Ex("C",Call("NNReal"),Call("LipschitzWith",X("C"),X("p")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Without an algebraic two-sided identity, every finite complex TEA-additive seminorm is Lipschitz. Three real spectral values provide disjoint cutoffs, and the nine-corner estimate gives a global bound."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Ty => Call("Type");
    private static Formula C => Call("Complex");
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => F.Seq(F.Open, f, F.Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(Formula type, Formula body) => F.Seq(F.OpenBracket, type, F.CloseBracket, F.Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Alg(bool unital, Formula body) => All("A", Ty, Inst(Call(unital ? "CStarAlgebra" : "NonUnitalCStarAlgebra", X("A")), unital ? Inst(Call("Nontrivial", X("A")), body) : body));
    private static Formula Tea(Formula a, Formula b) => Call("TEAPair", a, b);
    private static Formula PAdd(Formula type, Formula p) => All("a", type, All("b", type, Imp(Tea(X("a"), X("b")), Equal(App(p, Add(X("a"), X("b"))), Add(App(p, X("a")), App(p, X("b")))))));
    private static Formula SeminormType(Formula type) => Call("Seminorm", C, type);
    private static Formula UnitalHyp(Formula type) => Ex("q", type, All("a", type, And(Equal(Multiply(X("q"), X("a")), X("a")), Equal(Multiply(X("a"), X("q")), X("a")))));
    private static Formula Not(Formula a) => new Formula.Not(Parenthesized(a));
}
