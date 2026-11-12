using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hankel;

internal sealed class SunA006077BlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hankel/SunA006077Blocks.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/sun2013a006077");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residue classes modulo three give exact block determinant formulas.", H("The three residue classes"),
        Blocks(Paragraph(Text("Nat denotes the nonnegative integers and Z the integers. Matrix.of is displayed with Fin-sized row and column binders and explicit val projections; det of the empty matrix is one. All floor quotients are natural division.")),
            Node("d","Unshifted multinomial determinants","D",All("k",Nat,Eq(C("D",V("k")),Det(Hk(V("c"),V("k"))))),"D(0)=1.",DescribeRole.Definition),
            Node("e","Shifted multinomial determinants","E",All("k",Nat,Eq(C("E",V("k")),Det(Hk(V("c"),V("k"),N(1))))),"E(0)=1.",DescribeRole.Definition),
            Node("cross-block-det","A zero lower diagonal block","cross_block_det",All("R",V("Type"),Imp(C("CommRing",V("R")),All("k",Nat,All("A",C("Matrix",C("Fin",V("k")),C("Fin",V("k")),V("R")),All("B",C("Matrix",C("Fin",V("k")),C("Fin",V("k")),V("R")),All("C",C("Matrix",C("Fin",V("k")),C("Fin",V("k")),V("R")),Eq(Det(C("fromBlocks",V("A"),V("B"),V("C"),N(0))),M(M(P(NegOne,V("k")),Det(V("B"))),Det(V("C")))))))))),"For any commutative ring and three k-square matrices A,B,C, the block matrix with rows (A,B) and (C,0) has determinant (-1)^k det(B) det(C). Exchanging its column blocks gives a block triangular matrix; the top left block A is unrestricted.",DescribeRole.Theorem),
            Node("block-zero","The zero residue formula","block_zero",All("m",Nat,Eq(C("W",M(N(3),V("m"))),M(M(P(NegOne,V("m")),C("D",A(V("m"),N(1)))),P(C("E",V("m")),N(2))))),"Group indices by their residues modulo three and apply the same signs to the corresponding rows and columns. The blocks are D of size m+1 and two opposite shifted blocks of size m.",DescribeRole.Theorem),
            Node("block-two","The second residue formula","block_two",All("m",Nat,Eq(C("W",A(M(N(3),V("m")),N(2))),M(M(P(NegOne,A(V("m"),N(1))),C("D",A(V("m"),N(1)))),P(C("E",A(V("m"),N(1))),N(2))))),"The two shifted blocks now both have size m+1. Simultaneous row and column operations contribute determinant multiplier one.",DescribeRole.Theorem),
            Node("zero-branch","The vanishing residue class","zero_branch",All("m",Nat,Eq(C("W",A(M(N(3),V("m")),N(1))),N(0))),"The two off-diagonal residue blocks have unequal dimensions, so every permutation term vanishes. Sun v6, Remark 3.16 credits this entire branch to C. Krattenthaler; no originality is claimed for it.",DescribeRole.Theorem,AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/sun2013a006077")))), []));
    private static DocumentBlock Node(string id,string title,string decl,Formula formula,string prose,DescribeRole role,AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("sun-a006077-blocks-"+id),DeclarationHandle.Create(Prefix+decl),
            H(title),StatementSource.FromAuthor(Disp(formula)),provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),role);
    private static Formula V(string s) => F.Id(s);
    private static Formula N(long n) => new Formula.Number(n);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(V(s), [.. xs]);
    private static Formula A(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula M(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula P(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula All(string s, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, f);
    private static Formula Nat => V("Nat");
    private static Formula NegOne => new Formula.Negate(N(1));
    private static Formula Hk(Formula b, Formula k, Formula s) => MatrixOf(k, MatrixScalar,
        Apply(b, Add(Add(CallVal("i"),CallVal("j")),s)));
    private static Formula Hk(Formula b, Formula k) => MatrixOf(k, MatrixScalar,
        Apply(b, Add(CallVal("i"),CallVal("j"))));
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
    private static Formula MatrixScalar => new Formula.Integers();
    private static Formula Det(Formula x) => C("det", x);

}
