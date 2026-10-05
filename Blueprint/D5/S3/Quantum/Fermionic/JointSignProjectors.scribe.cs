using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

#pragma warning disable IDE0051 // Shared DSL helper vocabulary intentionally exceeds each document formula set.
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class JointSignProjectorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent sign reversals give a joint minus projector with exact trace.",
        H("The joint minus sector of commuting involutions"), Blocks(
            Paragraph(Text("Type denotes an arbitrary type, Fintype its finite enumeration, and DecidableEq decidable equality. Complex denotes complex numbers. M(Omega) is Matrix Omega Omega Complex, Fun(I,M) is the function type I → M, and val applies a function. Matrix multiplication is written as a product. Matrix one is the identity and matrix zero is the zero matrix; neg is additive negation. IsHermitian means equality to the conjugate transpose, Commute(A,B) means AB=BA, and IsStarProjection(P) means P²=P and P*=P. trace is the matrix trace, card is finite-type cardinality, and asComplex displays the natural-to-complex cast. The division displayed below is division in Complex.")),
            Describe.Lean(DescribeId.Create("fgauss-joint-sign-projection"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/JointSignProjectors.joint_sign_projection"),
                H("Exact trace and simultaneous minus eigenvalues"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The B operators are commuting Hermitian involutions. For each i, the involution U(i) reverses B(i) and commutes with every other B(j). The joint minus projection has trace card(Omega)/2^card(I). In particular it is nonzero when Omega is nonempty. It commutes with every matrix which commutes with all the B operators. The construction multiplies the commuting projections (1−B(i))/2. Induction inserts one factor at a time; conjugation by its sign reversal cancels the mixed trace, so each inserted factor halves the trace."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Ne(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.NotEqual, rhs);
    private static Formula Mul(Formula lhs, Formula rhs) =>
        new Formula.Binary(lhs, FormulaBinaryOperator.Multiply, rhs);
    private static Formula And(Formula lhs, Formula rhs) =>
        new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.And, Parenthesized(rhs));
    private static Formula Implies(Formula lhs, Formula rhs) =>
        new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.Implies, Parenthesized(rhs));
    private static Formula At(string name, Formula index) => Call("val", Id(name), index);

    private static Formula Statement()
    {
        var labels = Id("I"); var omega = Id("Omega");
        var i = Id("i"); var j = Id("j"); var p = Id("P"); var q = Id("Q");
        var matrix = Call("M", omega);
        var one = Parenthesized(Seq(D(1), Colon, matrix));
        var bi = At("B",i); var bj = At("B",j); var ui = At("U",i);
        var hB = All("i", labels, And(Call("IsHermitian",bi),Eq(Mul(bi,bi),one)));
        var hBB = All("i", labels, All("j", labels, Call("Commute",bi,bj)));
        var hU = All("i", labels, Eq(Mul(ui,ui),one));
        var hflip = All("i", labels, Eq(Mul(ui,bi),Call("neg",Mul(bi,ui))));
        var hfix = All("i", labels, All("j", labels, Implies(Ne(i,j),Call("Commute",ui,bj))));
        var hypotheses = And(hB,And(hBB,And(hU,And(hflip,hfix))));
        var conclusion = ExistsIn("P",matrix,And(Call("IsStarProjection",p),
            And(Eq(Call("trace",p),new Formula.Fraction(Call("asComplex",Call("card",omega)),
                new Formula.Power(Call("asComplex",D(2)),Call("card",labels)))),
                And(All("i",labels,Eq(Mul(bi,p),Call("neg",p))),
                    All("Q",matrix,Implies(All("i",labels,Call("Commute",q,bi)),
                        Call("Commute",q,p)))))));
        return All("I",Id("Type"),All("Omega",Id("Type"),Seq(
            OpenBracket,Call("Fintype",labels),CloseBracket,Sp,
            OpenBracket,Call("Fintype",omega),CloseBracket,Sp,
            OpenBracket,Call("DecidableEq",omega),CloseBracket,Sp,
            All("B",Call("Fun",labels,matrix),All("U",Call("Fun",labels,matrix),
                Implies(hypotheses,conclusion))))));
    }
}
