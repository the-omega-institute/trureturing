using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hankel;

internal sealed class SunA006077Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hankel/SunA006077.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/sun2013a006077");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite polynomial translation preserves the complete Hankel determinant.", H("Sun's finite sum and binomial translation"),
        Blocks(Paragraph(Text("Nat denotes the nonnegative integers and Z the integers. Matrix.of is displayed with Fin-sized row and column binders and explicit val projections; det of the empty matrix is one. All floor quotients are natural division.")),
            Node("c","Multinomial moments","c",All("r",Nat,Eq(C("c",V("r")),M(Typed(C("choose",M(N(2),V("r")),V("r")),Z),Typed(C("choose",M(N(3),V("r")),V("r")),Z)))),"The product of the two binomial coefficients is (3r)!/(r!)^3, with no division in the integer definition.",DescribeRole.Definition),
            Node("w","The original finite sum","w",All("n",Nat,Eq(C("w",V("n")),SumTo(V("k"),new Formula.Floor(new Formula.Fraction(V("n"),N(3))),M(M(M(M(P(NegOne,V("k")),P(N(3),Sub(V("n"),M(N(3),V("k"))))),Typed(C("choose",V("n"),M(N(3),V("k"))),Z)),Typed(C("choose",M(N(2),V("k")),V("k")),Z)),Typed(C("choose",M(N(3),V("k")),V("k")),Z))))),"This is the literal sum in Sun v5, Conjecture 3.16. The index runs from zero through floor(n/3), inclusive, so n-3k is nonnegative throughout; no truncated subtraction affects a summand.",DescribeRole.Definition),
            Node("hankel","The source Hankel determinant","W",All("n",Nat,Eq(C("W",V("n")),Det(Hk(V("w"),A(V("n"),N(1)))))),"Rows and columns are numbered zero through n, so W(n) has size n+1.",DescribeRole.Definition),
            Node("sparse","The sparse moments","sparse",All("n",Nat,Eq(C("sparse",V("n")),C("ite",Eq(new Formula.Modulo(V("n"),N(3)),N(0)),M(P(NegOne,C("NatDiv",V("n"),N(3))),C("c",C("NatDiv",V("n"),N(3)))),N(0)))),"Only indices divisible by three survive. At index 3r the sparse moment is (-1)^r c(r).",DescribeRole.Definition),
            Node("translate","Weighted binomial translation","translate",All("x",Z,All("b",new Formula.TypeArrow(Nat,Z),All("n",Nat,Eq(C("translate",V("x"),V("b"),V("n")),SumTo(V("k"),V("n"),M(M(P(V("x"),Sub(V("n"),V("k"))),Typed(C("choose",V("n"),V("k")),Z)),C("b",V("k")))))))),"The translation parameter is any integer. The index bound is inclusive and every exponent n-k is nonnegative.",DescribeRole.Definition),
            Node("source-as-translate","The exact source translation","source_as_translate",All("n",Nat,Eq(C("w",V("n")),C("translate",N(3),V("sparse"),V("n")))),"Deleting the zero terms and substituting j=3k identifies the literal finite sum with the weighted binomial transform.",DescribeRole.Theorem),
            Node("translate-hankel-det","Weighted binomial invariance","translate_hankel_det",All("x",Z,All("b",new Formula.TypeArrow(Nat,Z),All("N",Nat,Eq(Det(Hk(C("translate",V("x"),V("b")),V("N"))),Det(Hk(V("b"),V("N"))))))),"Apply the moment functional to products of the polynomials (X+x)^i. Their coefficient matrix is unit lower triangular, giving a congruence P H P transpose with determinant multiplier one. This is classical weighted binomial invariance.",DescribeRole.Theorem,AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/spivey2006binomial"))),
            Node("source-hankel-reduction","Reduction to sparse moments","source_hankel_reduction",All("n",Nat,Eq(C("W",V("n")),Det(Hk(V("sparse"),A(V("n"),N(1)))))),"The weighted translation by three has the same Hankel determinant at every size.",DescribeRole.Theorem)), []));
    private static DocumentBlock Node(string id,string title,string decl,Formula formula,string prose,DescribeRole role,AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("sun-a006077-source-"+id),DeclarationHandle.Create(Prefix+decl),
            H(title),StatementSource.FromAuthor(Disp(formula)),provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),role);
    private static Formula V(string s) => F.Id(s);
    private static Formula N(long n) => new Formula.Number(n);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(V(s), [.. xs]);
    private static Formula A(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula M(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula P(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula All(string s, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, f);
    private static Formula Nat => V("Nat");
    private static Formula Z => new Formula.Integers();
    private static Formula NegOne => new Formula.Negate(N(1));
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
    private static Formula SumTo(Formula k, Formula bound, Formula term) => Seq(new Formula.Power(new Formula.Subscript(Sum,Eq(k,N(0))),bound),Sp,term);

}
