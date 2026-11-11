using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hankel;

internal sealed class SunA006077BinaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hankel/SunA006077Binary.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/sun2013a006077");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even and odd index splitting proves both determinant families equal one over F2.", H("The binary Hankel determinants"),
        Blocks(Paragraph(Text("Nat denotes the nonnegative integers and Z the integers. Matrix.of is displayed with Fin-sized row and column binders and explicit val projections; det of the empty matrix is one. All floor quotients are natural division.")),
            Node("epsilon","The positive power-of-two indicator","epsilon",All("n",Nat,Eq(C("epsilon",V("n")),C("ite",Ex("k",Nat,Eq(V("n"),P(N(2),V("k")))),N(1),N(0)))),"Values lie in ZMod 2; epsilon(0)=0.",DescribeRole.Definition),
            Node("s","The first binary family","S",All("k",Nat,Eq(C("S",V("k")),Det(Hk(V("epsilon"),V("k"),N(1))))),"This is the ordinary Rueppel determinant modulo two.",DescribeRole.Definition),
            Node("t","The shifted binary family","T",All("k",Nat,Eq(C("T",V("k")),Det(Hk(V("epsilon"),V("k"),N(2))))),"This is the once-shifted Rueppel determinant modulo two.",DescribeRole.Definition),
            Node("rueppel-determinants","Both determinants at every size","rueppel_determinants",All("n",Nat,And(Eq(C("S",V("n")),N(1)),Eq(C("T",V("n")),N(1)))),"Over ZMod 2, parity splitting gives S(2k)=S(k)^2, S(2k+1)=T(k)^2, T(2k)=S(k)T(k), and T(2k+1)=S(k+1)T(k). The exceptional first corner in the odd S case is separated before taking block determinants. Strong induction includes the empty and one-square cases. The cited note attests the ordinary and shifted integer evaluations and their reduction modulo two.",DescribeRole.Theorem,AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/cigler2018curious")))), []));
    private static DocumentBlock Node(string id,string title,string decl,Formula formula,string prose,DescribeRole role,AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("sun-a006077-binary-"+id),DeclarationHandle.Create(Prefix+decl),
            H(title),StatementSource.FromAuthor(Disp(formula)),provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),role);
    private static Formula V(string s) => F.Id(s);
    private static Formula N(long n) => new Formula.Number(n);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(V(s), [.. xs]);
    private static Formula P(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula All(string s, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, f);
    private static Formula Ex(string s, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, f);
    private static Formula Nat => V("Nat");
    private static Formula Hk(Formula b, Formula k, Formula s) => MatrixOf(k, MatrixScalar,
        Apply(b, Add(Add(CallVal("i"),CallVal("j")),s)));
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
    private static Formula MatrixScalar => C("ZMod",new Formula.Number(2));
    private static Formula Det(Formula x) => C("det", x);

}
