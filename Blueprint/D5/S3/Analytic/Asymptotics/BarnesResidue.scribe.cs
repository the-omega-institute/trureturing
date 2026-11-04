using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;
internal sealed class BarnesResidueDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/Asymptotics/braams2026barnesmittagport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single-pole contour shift has the dy normalization 2*pi.", H("A Barnes contour shift"), Blocks(
            Describe.Lean(DescribeId.Create("barnesresidue-barnesres-vertical-shift"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/BarnesResidue.barnesRes_vertical_shift"),
                H("The single-pole shift"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The rectangle argument subtracts the removable divided difference of phi at p. The remaining reciprocal kernel has the arctangent/logarithm primitive. Horizontal terms vanish, and the two vertical reciprocal limits give exactly 2*pi times phi(p), with integration in dy."))), DescribeRole.Theorem))));
    private static Formula Statement()
    {
        Formula a=V("c1"), b=V("c2"), p=V("p"), phi=V("phi");
        Formula f=Map("s",Cx,Div(Apply(phi,V("s")),Sub(V("s"),p)));
        Formula strip=Call("preimage",V("re"),Call("Icc",a,b));
        Formula hypotheses=And(Lt(a,Call("re",p)),And(Lt(Call("re",p),b),
            And(Call("DifferentiableOn",Cx,phi,strip),
            And(Call("Integrable",Map("y",R,Apply(f,Add(a,Mul(V("y"),Imaginary))))),
            And(Call("Integrable",Map("y",R,Apply(f,Add(b,Mul(V("y"),Imaginary))))),
            And(Limit(Horizontal(f,a,b),"atTop"),Limit(Horizontal(f,a,b),"atBot")))))));
        Formula conclusion=Equal(Sub(Vertical(f,b),Vertical(f,a)),Mul(Mul(Num(2),PiValue),Apply(phi,p)));
        return All("phi",Fn(Cx,Cx),All("c1",R,All("c2",R,All("p",Cx,Imp(hypotheses,conclusion)))));
    }
    private static Formula R => F.Id("Real");
    private static Formula Cx => F.Id("Complex");
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(byte n) => D(n);
    private static Formula PiValue => Seq(Pi, Sp);
    private static Formula Imaginary => Seq(Operatorname, Grp(F.Id("ComplexI")));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(V(n), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Map(string n, Formula t, Formula f) => Seq(Open, V(n), Colon, t, Sp, Mapsto, Sp, f, Close);
    private static Formula Add(Formula a, Formula b) => Seq(Open, a, Plus, b, Close);
    private static Formula Sub(Formula a, Formula b) => Seq(Open, a, Minus, b, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Star, b, Close);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And,b);
    private static Formula Vertical(Formula f, Formula c) => Call("integral", Map("y", R, Apply(f, Add(c, Mul(V("y"), Imaginary)))));
    private static Formula Horizontal(Formula f, Formula a, Formula b) => Map("T", R,
        Call("intervalIntegral", Map("x", R, Apply(f, Add(V("x"), Mul(V("T"), Imaginary)))), a,b));
    private static Formula Limit(Formula f, string filter) => Call("Tendsto",f,V(filter),Call("nhds",Num(0)));
}
