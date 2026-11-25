using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.ErdosNicolas;

internal sealed class ErdosNicolasResidualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/ErdosNicolas/Residual.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/erdosnicolas1989functions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residual estimates", H("Residual estimates"), Blocks(
            Node("f_eq_two_terms", "One-period residual formula", TwoTerms(),
                "For r <= p, the two-site formula holds exactly when p=0 or L<=p+min(r,p-r). " +
                "For p>0 these sites have distances r and p-r. Under the window condition every " +
                "omitted distance is at least L, where the residual vanishes. Conversely an " +
                "exceeded window gives a positive omitted term. At p=0, r=0 and every L gives " +
                "zero. " +
                "The window is exact for p>0: exceeding either omitted distance p+r or 2p-r " +
                "introduces a positive term. For p=3,r=1,L=4 equality still holds; L=5 fails."),
            Node("f_eq_four_terms", "Two-period residual formula", FourTerms(),
                "For natural parameters with r <= p, the four possible contributing sites are " +
                "minus one, zero, one and two. The distances are p+r, r, p-r and 2p-r. " +
                "The omitted sites have distance at least 2p. At either endpoint r=0 or r=p, " +
                "the result is twice w(2p,p). The zero-period case has value zero."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose) => Describe.Lean(
        DescribeId.Create("erdosnicolas-residual-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))),
        DescribeRole.Theorem);
    private static Formula TwoTerms()
    {
        var p=V("p"); var l=V("L"); var r=V("r");
        var body=Eq(Call("f",p,l,r),Add(Call("w",l,r),Call("w",l,Sub(p,r))));
        var window=new Formula.Logic(Eq(p,D(0)),FormulaLogicOperator.Or,
            Le(l,Add(p,Call("min",r,Sub(p,r)))));
        var exact=new Formula.Logic(body,FormulaLogicOperator.Iff,window);
        return All("p","N",All("L","N",All("r","N",Imp(Le(r,p),exact))));
    }

    private static Formula FourTerms()
    {
        var p=V("p"); var r=V("r"); var l=Mul(D(2),p);
        var body=Eq(Call("f",p,l,r),Add(Add(Add(Call("w",l,r),Call("w",l,Sub(p,r))),
            Call("w",l,Add(p,r))),Call("w",l,Sub(l,r))));
        return All("p","N",All("r","N",Imp(Le(r,p),body)));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, string type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            Seq(Mathbb, Grp(V(type))), body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
