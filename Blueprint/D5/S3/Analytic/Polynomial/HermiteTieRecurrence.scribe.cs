using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class HermiteTieRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/HermiteTieRecurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/sheppard2025a381737");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fifth-lag recurrence for the complete increasing enumeration of physicists Hermite absolute-tie orders.",
        H("The recurrence of the Hermite absolute-tie orders"),
        Blocks(
            Paragraph(Text("Use HermiteAbsoluteTieOrders.IsAbsMax and HasExactlyTwo without changing their definitions. "
                + "The polynomial is HermiteSignedMode.physicistsHermite over the rationals. For each natural order k, "
                + "IsAbsMax compares absolute coefficients at every exponent from zero through k, including parity-zero coefficients. "
                + "HasExactlyTwo means there are distinct exponents u<v and these are precisely all maximizing exponents. "
                + "Thus no restricted coefficient row or selected family of orders enters the assertion.")),
            Node("claim", "The complete actual-enumeration assertion", Equal(F.Id("claim"), Par(ClaimBody())),
                "The function g has a value in the natural numbers at every integer argument. At every positive integer index its value "
                + "is positive, and its values strictly increase on positive indices. For every natural order k, HasExactlyTwo holds "
                + "if and only if k is g(n) at exactly one positive integer index n. The unique-existence notation is expanded into "
                + "existence and uniqueness in the formula. At every integer n at least six, the five preceding indices are positive "
                + "and the stated recurrence holds. Each individual value of g is cast to the integers before any subtraction.",
                DescribeRole.Definition),
            Node("result", "The full A381737 Conjecture 2 recurrence", ClaimBody(),
                "HermiteAbsoluteTieOrders.result supplies the positive, strictly increasing, exhaustive, uniquely indexed enumeration "
                + "b(m)=2m(m+2)+(m+1)(-1)^(m+1) for positive natural m. Define g(n) as the natural value of b(n.toNat). "
                + "Positivity of b at positive indices makes the casts exact. Conversion between positive integer and positive natural "
                + "indices preserves order, existence and uniqueness, so this is the actual enumeration of all qualifying orders. "
                + "For t=n-5, expand b(t+5), b(t+4), b(t+3), b(t+2), b(t+1) and b(t). "
                + "The quadratic part and the alternating linear part each satisfy the displayed recurrence; expansion of powers "
                + "of minus one and polynomial normalization give their sum. This proves the recurrence for every n at least six, "
                + "with no finite cutoff or additional assumption. The recurrence is the assertion named Conjecture 2 in "
                + "OEIS A381737 revision 28, offset 1,1. Its proof is a consequence of the stronger Conjecture 1 enumeration.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a381737-hermite-tie-recurrence"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hermite-tie-recurrence-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Named(s), [.. args]);
    private static Formula Par(Formula a) => Seq(Open,a,Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula Less(Formula a, Formula b) => Seq(a,Sp,Lt,Sp,b);
    private static Formula Leq(Formula a, Formula b) => Seq(a,Sp,Le,Sp,b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a),Sp,Land,Sp,Par(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula Equiv(Formula a, Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall,Sp,F.Id(n),Colon,t,Comma,Sp,b);
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists,Sp,F.Id(n),Colon,t,Comma,Sp,b);
    private static Formula G(Formula n) => new Formula.Apply(F.Id("g"),[n]);
    private static Formula Z(Formula n) => Par(Seq(G(n),Colon,Ints()));
    private static Formula Sub(Formula n, byte j) => Seq(n,Minus,D(j));
    private static Formula Index(Formula k, Formula n) => And(Leq(D(1),n),Equal(k,G(n)));
    private static Formula ClaimBody()
    {
        var n=F.Id("n"); var m=F.Id("m"); var k=F.Id("k");
        var positive=All("n",Ints(),Arrow(Leq(D(1),n),Less(D(0),G(n))));
        var increasing=All("n",Ints(),All("m",Ints(),Arrow(Leq(D(1),n),Arrow(Less(n,m),Less(G(n),G(m))))));
        var unique=Some("n",Ints(),And(Index(k,n),All("m",Ints(),Arrow(Index(k,m),Equal(m,n)))));
        var exhaustive=All("k",Nat(),Equiv(Call("HasExactlyTwo",k),unique));
        var rhs=Seq(Z(Sub(n,1)),Plus,D(2),Cdot,Z(Sub(n,2)),Minus,D(2),Cdot,Z(Sub(n,3)),Minus,Z(Sub(n,4)),Plus,Z(Sub(n,5)));
        var recurrence=All("n",Ints(),Arrow(Leq(D(6),n),Equal(Z(n),rhs)));
        return Some("g",Seq(Ints(),Sp,To,Sp,Nat()),And(positive,And(increasing,And(exhaustive,recurrence))));
    }
}
