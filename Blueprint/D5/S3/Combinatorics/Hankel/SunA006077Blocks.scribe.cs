using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hankel;

internal sealed class SunA006077BlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hankel/SunA006077Blocks.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sun2013a006077");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residue classes modulo three give exact block determinant formulas.", H("The three residue classes"),
        Blocks(Paragraph(Text("For a sequence b, H(b,k,s) is the k by k matrix with entry b(i+j+s), where 0 <= i,j < k; det of the empty matrix is one. Nat denotes the nonnegative integers, Z the integers, and all floor quotients are natural division.")),
            Node("d","Unshifted multinomial determinants","D",All("k",Nat,Eq(C("D",V("k")),Det(Hk(V("c"),V("k"),N(0))))),"D(0)=1.",DescribeRole.Definition),
            Node("e","Shifted multinomial determinants","E",All("k",Nat,Eq(C("E",V("k")),Det(Hk(V("c"),V("k"),N(1))))),"E(0)=1.",DescribeRole.Definition),
            Node("cross-block-det","Equal square off-diagonal blocks","cross_block_det",All("R",V("Type"),Imp(C("CommRing",V("R")),All("k",Nat,All("A",C("Matrix",C("Fin",V("k")),C("Fin",V("k")),V("R")),All("B",C("Matrix",C("Fin",V("k")),C("Fin",V("k")),V("R")),Eq(Det(C("fromBlocks",N(0),V("A"),V("B"),N(0))),M(M(P(NegOne,V("k")),Det(V("A"))),Det(V("B"))))))))),"For any commutative ring and two k-square matrices, exchanging the two column blocks gives a diagonal block matrix. The exchange has sign (-1)^k.",DescribeRole.Theorem),
            Node("block-zero","The zero residue formula","block_zero",All("m",Nat,Eq(C("W",M(N(3),V("m"))),M(M(P(NegOne,V("m")),C("D",A(V("m"),N(1)))),P(C("E",V("m")),N(2))))),"Group indices by their residues modulo three and apply the same signs to the corresponding rows and columns. The blocks are D of size m+1 and two opposite shifted blocks of size m.",DescribeRole.Theorem),
            Node("block-two","The second residue formula","block_two",All("m",Nat,Eq(C("W",A(M(N(3),V("m")),N(2))),M(M(P(NegOne,A(V("m"),N(1))),C("D",A(V("m"),N(1)))),P(C("E",A(V("m"),N(1))),N(2))))),"The two shifted blocks now both have size m+1. Simultaneous row and column operations contribute determinant multiplier one.",DescribeRole.Theorem),
            Node("zero-branch","The vanishing residue class","zero_branch",All("m",Nat,Eq(C("W",A(M(N(3),V("m")),N(1))),N(0))),"The two off-diagonal residue blocks have unequal dimensions, so every permutation term vanishes. Sun v6, Remark 3.16 credits this entire branch to C. Krattenthaler; no originality is claimed for it.",DescribeRole.Theorem)), []));
    private static DocumentBlock Node(string id,string title,string decl,Formula formula,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("sun-a006077-blocks-"+id),DeclarationHandle.Create(Prefix+decl),
            H(title),StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(Source),
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
    private static Formula Hk(Formula b, Formula k, Formula s) => C("H", b, k, s);
    private static Formula Det(Formula x) => C("det", x);

}
