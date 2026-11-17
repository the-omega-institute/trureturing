using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hankel;

internal sealed class SunA006077PositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hankel/SunA006077Positivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/sun2013a006077");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Beta integrals and the Schur product establish positive semidefiniteness.", H("Multinomial moment matrices"),
        Blocks(Paragraph(Text("Nat denotes the nonnegative integers and Z the integers. Matrix.of is displayed with Fin-sized row and column binders and explicit val projections; det of the empty matrix is one. All floor quotients are natural division.")),
            Node("multinomial-possemidef","Every nonnegative shift is positive semidefinite","multinomial_posSemidef",All("s",Nat,All("N",Nat,C("PosSemidef",MatrixOf(V("N"),V("Real"),Typed(C("c",Add(Add(CallVal("i"),CallVal("j")),V("s"))),V("Real")))))),"For 0<a<1 put mu(a,r)=(a)_r/r!. The normalized beta integral has these moments, and integrating t^s times a polynomial square gives a positive semidefinite matrix at every shift s. The identity c(r)=27^r mu(1/3,r) mu(2/3,r) follows from factorial recurrences. A Schur product, diagonal congruence by 27^i, and multiplication by 27^s give the stated matrix. Integrability follows from the beta integral with positive shifted shape. The cited note attests the positive-moment property of c; the beta construction here uses the existing real beta integral declarations.",DescribeRole.Theorem,AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/penson2001coherent")))), []));
    private static DocumentBlock Node(string id,string title,string decl,Formula formula,string prose,DescribeRole role,AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("sun-a006077-positivity-"+id),DeclarationHandle.Create(Prefix+decl),
            H(title),StatementSource.FromAuthor(Disp(formula)),provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),role);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(V(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, f);
    private static Formula Nat => V("Nat");
    private static Formula MatrixOf(Formula size, Formula scalar, Formula entry) => Typed(
        Apply(Qualified("Matrix","of"), LambdaOf("i",C("Fin",size),LambdaOf("j",C("Fin",size),entry))),
        C("Matrix",C("Fin",size),C("Fin",size),scalar));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(V(name),type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value,Colon,Sp,type));
    private static Formula Parenthesized(Formula value) => Seq(Open,value,Close);
    private static Formula Qualified(string owner,string name) => Seq(Operatorname,Grp(V(owner)),Dot,Operatorname,Grp(V(name)));
    private static Formula Apply(Formula f,params Formula[] args) => new Formula.Apply(f,[.. args]);
    private static Formula CallVal(string name) => Apply(Qualified("Fin","val"),V(name));
    private static Formula Add(Formula x,Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Add,y);

}
