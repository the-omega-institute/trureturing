using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hankel;

internal sealed class SunA006077PositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hankel/SunA006077Positivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sun2013a006077");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Beta integrals and the Schur product establish positive semidefiniteness.", H("Multinomial moment matrices"),
        Blocks(Paragraph(Text("For a sequence b, H(b,k,s) is the k by k matrix with entry b(i+j+s), where 0 <= i,j < k; det of the empty matrix is one. Nat denotes the nonnegative integers, Z the integers, and all floor quotients are natural division.")),
            Node("multinomial-possemidef","Every nonnegative shift is positive semidefinite","multinomial_posSemidef",All("s",Nat,All("N",Nat,C("PosSemidef",C("realCast",Hk(V("c"),V("N"),V("s")))))),"For 0<a<1 put mu(a,r)=(a)_r/r!. The normalized beta integral has these moments, and integrating t^s times a polynomial square gives a positive semidefinite matrix at every shift s. The identity c(r)=27^r mu(1/3,r) mu(2/3,r) follows from factorial recurrences. A Schur product, diagonal congruence by 27^i, and multiplication by 27^s give the stated matrix. Integrability follows from the beta integral with positive shifted shape. The positive-moment property of c is known, including Penson and Solomon, Example 9; the beta construction here uses the existing real beta integral declarations.",DescribeRole.Theorem)), []));
    private static DocumentBlock Node(string id,string title,string decl,Formula formula,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("sun-a006077-positivity-"+id),DeclarationHandle.Create(Prefix+decl),
            H(title),StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),role);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(V(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, f);
    private static Formula Nat => V("Nat");
    private static Formula Hk(Formula b, Formula k, Formula s) => C("H", b, k, s);

}
