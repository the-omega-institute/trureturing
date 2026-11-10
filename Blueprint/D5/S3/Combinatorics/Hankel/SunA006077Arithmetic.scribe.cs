using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hankel;

internal sealed class SunA006077ArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sun2013a006077");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quotient coefficient is odd exactly at positive powers of two.", H("Dividing multinomial coefficients by six"),
        Blocks(Paragraph(Text("For a sequence b, H(b,k,s) is the k by k matrix with entry b(i+j+s), where 0 <= i,j < k; det of the empty matrix is one. Nat denotes the nonnegative integers, Z the integers, and all floor quotients are natural division.")),
            Node("q","An explicit integral quotient","q",All("r",Nat,Eq(C("q",V("r")),M(C("choose",C("NatSub",M(N(2),V("r")),N(1)),C("NatSub",V("r"),N(1))),C("choose",C("NatSub",M(N(3),V("r")),N(1)),C("NatSub",V("r"),N(1)))))),"NatSub is natural subtraction. The quotient relation is used only for positive r; the definition also fixes q(0).",DescribeRole.Definition),
            Node("c-six","Exact divisibility by six","c_six",All("r",Nat,Imp(Lt(N(0),V("r")),Eq(C("c",V("r")),M(N(6),C("q",V("r")))))),"Twice and three times the respective reduced binomial coefficients recover the two original binomial factors.",DescribeRole.Theorem),
            Node("q-odd-iff","Parity detects powers of two","q_odd_iff",All("r",Nat,Imp(Lt(N(0),V("r")),Iff(C("Odd",C("q",V("r"))),Ex("k",Nat,Eq(V("r"),P(N(2),V("k"))))))),"Kummer valuations express the central binomial valuation as the binary digit sum of r. Equality to one forces one binary digit; at a power of two the second binomial factor is odd.",DescribeRole.Theorem),
            Node("d","Unshifted normalized determinant","d",All("m",Nat,Eq(C("d",V("m")),Det(C("A",V("m"))))),"A(m) has size m+1. Its first row has entries c(j); every other row i has entries q(i+j).",DescribeRole.Definition),
            Node("e","Shifted normalized determinant","e",All("m",Nat,Eq(C("e",V("m")),Det(Hk(V("q"),V("m"),N(1))))),"All m rows of the shifted determinant are divided by six.",DescribeRole.Definition),
            Node("d-normalization","The unshifted exact factor","D_normalization",All("m",Nat,Eq(C("D",A(V("m"),N(1))),M(P(N(6),V("m")),C("d",V("m"))))),"Each row except the first has a positive coefficient index and contributes one factor of six.",DescribeRole.Theorem),
            Node("e-normalization","The shifted exact factor","E_normalization",All("m",Nat,Eq(C("E",V("m")),M(P(N(6),V("m")),C("e",V("m"))))),"Each shifted row contributes one factor of six, including the empty-size convention.",DescribeRole.Theorem),
            Node("normalized-odd","Both integral quotients are odd","normalized_odd",All("m",Nat,And(C("Odd",C("d",V("m"))),C("Odd",C("e",V("m"))))),"Modulo two the shifted determinant is S(m). The unshifted first row reduces to (1,0,...,0), and its first cofactor is T(m). Both equal one.",DescribeRole.Theorem)), []));
    private static DocumentBlock Node(string id,string title,string decl,Formula formula,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("sun-a006077-arithmetic-"+id),DeclarationHandle.Create(Prefix+decl),
            H(title),StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),role);
    private static Formula V(string s) => F.Id(s);
    private static Formula N(long n) => new Formula.Number(n);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(V(s), [.. xs]);
    private static Formula A(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula M(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula P(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula All(string s, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, f);
    private static Formula Ex(string s, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, f);
    private static Formula Nat => V("Nat");
    private static Formula Hk(Formula b, Formula k, Formula s) => C("H", b, k, s);
    private static Formula Det(Formula x) => C("det", x);

}
