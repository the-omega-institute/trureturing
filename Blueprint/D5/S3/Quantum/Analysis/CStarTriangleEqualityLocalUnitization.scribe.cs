using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class CStarTriangleEqualityLocalUnitizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle equality and norm scale in complex C-star algebras.",
        H("CStarTriangleEqualityLocalUnitization"), Blocks(
            Describe.Lean(DescribeId.Create("cstartriangleequalitylocalunitization-local-unitization-seminorm-scale"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CStarTriangleEqualityLocalUnitization.local_unitization_seminorm_scale"),
                H("local unitization seminorm scale"),
                StatementSource.FromAuthor(All("A",Ty,All("B",Ty,Inst(Call("NonUnitalCStarAlgebra",X("A")),Inst(Call("NonUnitalCStarAlgebra",X("B")),All("phi",Call("NonUnitalStarAlgHom",C,X("B"),X("A")),Imp(App(Q("Function","Injective"),X("phi")),Imp(Not(UnitalHyp(X("B"))),All("e",X("A"),Imp(Le(Norm(X("e")),N(1)),Imp(All("b",X("B"),Equal(Multiply(X("e"),App(X("phi"),X("b"))),App(X("phi"),X("b")))),Imp(All("q",SeminormType(Call("Unitization",C,X("B"))),Imp(RawPAdd(Call("Unitization",C,X("B")),X("q")),All("x",Call("Unitization",C,X("B")),Scale(X("q"),X("x"))))),All("p",SeminormType(X("A")),Imp(RawPAdd(X("A"),X("p")),All("b",X("B"),Equal(App(X("p"),App(X("phi"),X("b"))),Multiply(App(X("p"),X("e")),Norm(X("b"))))))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/litsaiwangwong2026tea")),
                Blocks(Paragraph(Text("Let phi embed a genuinely nonunital complex C-star algebra B into A, and let a contraction e act as a left identity on its image. If every TEA-additive complex seminorm on Unitization Complex B has the unital scale property, then any such seminorm on A has scale p(e) on phi(B). The linear local-unitization map is isometric; multiplicativity of that map is not required."))), DescribeRole.Theorem))));

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
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula TeaBody(Formula a, Formula b) => Equal(Norm(Add(a, b)), Add(Norm(a), Norm(b)));
    private static Formula RawPAdd(Formula type, Formula p) => All("x", type, All("y", type, Imp(TeaBody(X("x"), X("y")), Equal(App(p, Add(X("x"), X("y"))), Add(App(p, X("x")), App(p, X("y")))))));
    private static Formula SeminormType(Formula type) => Call("Seminorm", C, type);
    private static Formula Scale(Formula p, Formula a) => Equal(App(p, a), Multiply(App(p, N(1)), Norm(a)));
    private static Formula UnitalHyp(Formula type) => Ex("q", type, All("a", type, And(Equal(Multiply(X("q"), X("a")), X("a")), Equal(Multiply(X("a"), X("q")), X("a")))));
    private static Formula Not(Formula a) => new Formula.Not(Parenthesized(a));
}
