using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GranvikMertensArray_Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GranvikMertensArray.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/granvik2011a192763");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The diagonal and first row of the Granvik Mertens array.",
        H("Granvik's Möbius and Mertens identities"), Blocks(
            Describe.Lean(DescribeId.Create("a192763-array"),
                DeclarationHandle.Create(Prefix + "T"), H("Somos's rational array"),
                StatementSource.FromAuthor(Disp(Seq(Bind("n"), Bind("k"),
                    Call("T", F.Id("n"), F.Id("k")), Sp, InMacro, Sp, Rat()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Indices are natural numbers; a cell with either index zero is zero. On positive indices, T(1,1)=1, T(2,1)=2, and symmetry gives T(n,k)=T(k,n) when k>n. For n at least three, the border update is T(n,1)=(-T(n-1,1)-sum over 2<=i<=n-1 of T(n,i))/(n+1)+T(n-1,1). For n>k>=2, T(n,k)=T(k,((n-1) mod k)+1). For n>=2, T(n,n) is the negative sum of T(n,i) over 1<=i<=n-1. All sums are finite and division is rational. A well-founded measure orders these recursive calls. This is Somos's program in OEIS A192763, with its corner normalization one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a192763-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The diagonal and the Mertens row"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Here mu is ArithmeticFunction.moebius, cast from integers to rationals. The first assertion includes the corner n=1; the second begins at k=2, exactly as in the two COMMENTS conjectures in OEIS A192763.")),
                    Paragraph(Text("The proof constructs a symmetric model. A noncoprime interior cell has value gcd(n,k)*mu(gcd(n,k)); a coprime interior cell has the border value at the last Euclidean quotient. Signed Bézout identities identify that quotient with floor((n-1)/min(u,n-u)), where u is the inverse residue of k modulo n. Inversion and reflection permute the reduced residues. Möbius convolution evaluates their summed border values, and a gcd multiplicity identity supplies the other cells. The resulting row sum gives the required diagonal and border equations.")),
                    Paragraph(Text("The proof also defines the first Granvik/Gérard Mathematica program literally, including its reverse-window sums. Periodicity and the zero diagonal row sum show that Somos's array satisfies this program. Well-founded uniqueness identifies both arrays and the arithmetic model. The companion Math.SE 50719 question prints a different corner; the theorem uses the OEIS programs' value one. No Mertens growth estimate follows from these identities."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a192763-granvik-mertens-array"), ResolutionKind.Proved)))));

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Named(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Named(s), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Bind(string s) => Seq(Forall, Sp, F.Id(s), Colon, Sp, Nat(), Comma, Sp);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x), Sp, Implies, Sp, y);
    private static Formula ResultFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var j = F.Id("j");
        var diagonal = Seq(Bind("n"), Imp(Seq(D(1), Sp, Le, Sp, n),
            Eqn(Call("T", n, n), new Formula.Binary(n, FormulaBinaryOperator.Multiply, Call("mu", n)))));
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(j, Sp, InMacro, Sp, Call("Icc", D(1), k))),
            Sp, Call("mu", j));
        var row = Seq(Bind("k"), Imp(Seq(D(2), Sp, Le, Sp, k),
            Eqn(Call("T", D(1), k), new Formula.Binary(D(2), FormulaBinaryOperator.Add, sum))));
        return Disp(Seq(Par(diagonal), Sp, Land, Sp, Par(row)));
    }
}
