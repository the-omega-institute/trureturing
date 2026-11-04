using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;
internal sealed class MellinBarnesSeriesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/Asymptotics/braams2026barnesmittagport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closing a contour sequence identifies its integral with the summable residue series.", H("A Mellin-Barnes residue series"), Blocks(
            Describe.Lean(DescribeId.Create("mellinbarnesseries-mbseries-hassum"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MellinBarnesSeries.mbSeries_hasSum"),
                H("The residue HasSum"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("MBSeriesData retains all seven obligations: the pole lies between consecutive lines; each numerator is holomorphic on its closed strip; the actual integrand equals that numerator divided by s-p away from the pole; every line is integrable; and the horizontal cross-sections vanish at both ends. Iterating the single-pole shift telescopes the line integrals. The moving-left limit and residue summability then identify the integral by HasSum uniqueness. The Mittag-Leffler identity supplies every obligation for its literal kernel."))), DescribeRole.Theorem))));
    private static Formula Statement()
    {
        Formula f=V("F"), c=V("c"), p=V("p"), phi=V("phi");
        Formula residue=Map("n",N,Apply(phi,V("n"),Apply(p,V("n"))));
        Formula line=Map("n",N,Vertical(f,Apply(c,V("n"))));
        Formula hypotheses=And(Call("MBSeriesData",f,c,p,phi),And(Limit(line,"atTop"),Call("Summable",residue)));
        Formula sums=Call("HasSum",Map("n",N,Mul(Mul(Num(2),PiValue),Apply(residue,V("n")))),Vertical(f,Apply(c,Num(0))));
        return All("F",Fn(Cx,Cx),All("c",Fn(N,R),All("p",Fn(N,Cx),All("phi",Fn(N,Fn(Cx,Cx)),Imp(hypotheses,sums)))));
    }
    private static Formula R => F.Id("Real");
    private static Formula Cx => F.Id("Complex");
    private static Formula N => F.Id("Nat");
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
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Star, b, Close);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And,b);
    private static Formula Vertical(Formula f, Formula c) => Call("integral", Map("y", R, Apply(f, Add(c, Mul(V("y"), Imaginary)))));
    private static Formula Limit(Formula f, string filter) => Call("Tendsto",f,V(filter),Call("nhds",Num(0)));
}
