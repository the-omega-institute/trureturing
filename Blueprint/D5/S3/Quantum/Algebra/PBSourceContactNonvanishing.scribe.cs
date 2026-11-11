using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBSourceContactNonvanishingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative source nonvanishing on the original complete two-coordinate actor contact model, including both source signs and both actor axes.",
        H("Nonvanishing of the original source readout"),
        Blocks(
            Paragraph(Text("The actor is the entire complex two-coordinate vector space. Its squared Euclidean norm is the sum of the two squared coordinate norms. The fixed operators are C=diag(1,2), H=2C+hJ and B=H+C, where J exchanges the two coordinates. The fixed source is (1/sqrt(2),r), with r either 1 or -1. The parameters x,y,h are real, abs(y)>1 and abs(h)<1. The orientation here is the source's fixed positive imaginary unit; both signs of y remain in scope.")),
            Paragraph(Text("The Contact predicate retains the actual vectors u,p,q,a and the complex source amplitude eta. It imposes the original unit norm, both real diagonal graph pairings, the full mixed graph equality, q=(ell I+2 C inverse)p+i B C u, a=i(I-ell C inverse)p, and the two coordinates of a-Hu+ell C squared u/2=eta times the same fixed source. Here ell=x+iy. The displayed coordinate functions are these literal two-dimensional operators; no axis is removed and neither coordinate of u nor x is divided out.")),
            Describe.Lean(DescribeId.Create("original-source-nonvanishing"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBSourceContactNonvanishing.original_contact_nonvanishing"),
                H("The full quantitative source bound"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The source readout is u adjoint times (C-ell I) inverse times C times the fixed source. It is nonzero. The norm of eta is at least sqrt(2) times (1+3 norm(u second coordinate) squared-abs(h)), and is strictly positive. The proof uses the actual source equation and graph constraints to obtain eta times the source readout equal to the original residual numerator. The signed imaginary part of that numerator is bounded below by 3+9 norm(u second coordinate) squared-3 abs(h), while abs(y) times the norm of the source readout is at most 3/sqrt(2).")),
                    Paragraph(Text("This is the quantitative nonvanishing clause of the original actual-contact reduction. It does not establish the converse reconstruction, the projective phase quotient, the complete finite-environment PB threshold, an attaining contact, the strict descent theorem, or the opposite imaginary orientation's conjugation transport. The mathematical model keeps the source fixed; it makes no physical acquisition or preparation claim.")),
                    Paragraph(Text("The source-bound four-slot registration remains unfinished at https://github.com/the-omega-institute/trureturing/issues/29263. The required original-contact witness, whole-family variation and exact source occurrence ties have not been supplied; the mathematical Lean proof does not establish registration completion.")))))));
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => Call(s, xs);
    private static Formula N(int n) => Num(n);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Norm(Formula a) => C("norm", a);
    private static Formula Statement()
    {
        var reals = Seq(Mathbb, Grp(I("R")));
        var complexes = Seq(Mathbb, Grp(I("C")));
        var eta = I("eta");
        var bound = Multiply(C("sqrt", N(2)),
            Subtract(Add(N(1), Multiply(N(3), C("pow", Norm(C("apply", I("u"), N(1))), N(2)))), C("abs", I("h"))));
        Formula body = Imp(C("Contact", I("h"), I("r"), I("x"), I("y"), I("u"), I("p"), I("q"), I("a"), eta),
            And(Ne(C("sourceReadout", I("r"), I("x"), I("y"), I("u")), N(0)),
                And(Le(bound, Norm(eta)), Lt(N(0), Norm(eta)))));
        body = All("eta", complexes, body);
        foreach (var s in new[] { "a", "q", "p", "u" }) body = All(s, I("Vec"), body);
        foreach (var s in new[] { "y", "x", "r", "h" }) body = All(s, reals, body);
        return body;
    }
}
