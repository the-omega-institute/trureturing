using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class SpiderPowerZeroForcingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/abiadflaggghaseminezhadzeijlemaker2026powers");

    public DocumentDefinition Create()
    {
        var m = V("m"); var k = V("k"); var l = V("l");
        var a = V("a"); var b = V("b"); var i = V("i"); var j = V("j");
        var u = V("u"); var v = V("v");
        var vertex = Call("Vertex", m, l);
        var ai = Call("some", Pair(a,i)); var bj = Call("some", Pair(b,j));
        var center = Call("none");
        var dist = And(Eq(Call("distance",center,center), D(0)),
            And(All("a",Call("Fin",m),All("i",Call("Fin",l),
                And(Eq(Call("distance",center,ai),Add(i,D(1))),
                    Eq(Call("distance",ai,center),Add(i,D(1)))))),
                All("a",Call("Fin",m),All("b",Call("Fin",m),All("i",Call("Fin",l),All("j",Call("Fin",l),
                    Eq(Call("distance",ai,bj),Call("ite",Eq(a,b),Call("NatDist",i,j),Add(Add(i,j),D(2))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The ordinary kth power of the equal-legged spider has zero forcing number (m-1)k.",
            H("Zero forcing powers of equal-legged spiders"),
            Blocks(
                Node("vertices","All original vertices","Vertex",
                    All("m",Nat(),All("l",Nat(),Eq(vertex,Call("Option",Seq(Call("Fin",m),Sp,Times,Sp,Call("Fin",l)))))),
                    "The vertex type has a center none and m legs with l vertices each. The vertex some(a,i) has source leg label a+1 and depth i+1, with zero-based Fin indices. Its cardinality is ml+1.",DescribeRole.Definition),
                Node("distance","Distances in the source tree","distance",
                    All("m",Nat(),All("l",Nat(),dist)),
                    "The center-to-leg distance is depth, same-leg distance is the absolute depth difference, and different-leg distance is the sum of depths. NatDist is the natural absolute difference. These are the three unique-path distances in the spider of section 3.",DescribeRole.Definition),
                Node("power","The ordinary graph power","power",
                    All("m",Nat(),All("k",Nat(),All("l",Nat(),All("u",vertex,All("v",vertex,
                        Iff(Call("Adj",Call("power",m,k,l),u,v),And(Ne(u,v),Le(Call("distance",u,v),k)))))))),
                    "The power joins distinct vertices at distance at most k. It retains the center and every leg vertex and has no loops. Ordinary forcing uses the existing Black, IsZeroForcing and zeroForcingNumber definitions: a black source with exactly one white neighbor forces that neighbor.",DescribeRole.Definition),
                Node("result","Conjecture 10","result",
                    All("m",Nat(),All("k",Nat(),All("l",Nat(),
                        Imp(And(Le(D(2),m),And(Le(D(1),k),Le(Add(k,D(1)),l))),
                            Eq(Call("zeroForcingNumber",Call("power",m,k,l)),Mul(Sub(m,D(1)),k)))))),
                    "For every m at least two, k at least one and l at least k+1, the ordinary zero forcing number is (m-1)k. The same statement includes m=2, k=1 and l=k+1, including their simultaneous boundary case.",DescribeRole.Theorem,
                    AssessedProvenance.FromRepo(Source),
                    new OpenProblemResolutionClaim(ProblemSlugRef.Create("abiad-equal-legged-spider-power-zero-forcing"),ResolutionKind.Proved)),
                Paragraph(Text("For a leg of size n>=1 and an order 0<=r<n, let B have diagonal n-1, upper entry B(i,i+1)=n-1-i and lower entry B(i+1,i)=i+1. Rectangular factors C and D satisfy CD=B and DC=B of size n-1 plus 2I. The recursion P(0,A)=I and P(r+1,A)=(A-2rI)P(r,A) gives P(r,B)=QR with Q of shape n by n-r and R of shape n-r by n. Both factors have nonnegative entries, and their positive entries occupy the intervals a through a+r. Therefore P(r,B)(i,j) is positive exactly when the absolute difference of indices is at most r. Rank-nullity gives dimension ker R at least r, and QR annihilates ker R.")),
                Paragraph(Text("Place these B blocks on the original legs. Give the center diagonal the common parameter t, and give each center-to-first-vertex entry and its reverse the value one. The resulting matrix A(t) is generally nonsymmetric. For W=ker P(k,B), take the subspace of W to the mth power consisting of leg vectors whose sum is zero. Its dimension is at least (m-1)dim W. Appending center coordinate zero injects it into ker P(k,A(t)): the sum cancels the center row and the leg rows intertwine with B. Thus the full matrix has kernel dimension at least (m-1)k for every t.")),
                Paragraph(Text("For 0<=r<ell, work over rational polynomials in t and subtract the constant diagonal leg block from P(r,A). If a center correction has row and column depths d and e, its coefficient of order s vanishes when r<d+e+s and is positive when r=d+e+s. This follows inductively: the center row supplies one extra power of t, and a leg row has exactly one inward neighbor with a positive coefficient. At the constant boundary the center row receives the positive leg-band entry. Outside the kth power both the constant leg block and the correction vanish. Inside it, either the positive constant leg entry remains, or the correction has a positive leading coefficient. When d+e=k, both constant contributions are nonnegative and the correction is positive, so cancellation cannot occur.")),
                Paragraph(Text("Multiply the finitely many nonzero polynomials for ordered edges. A nonzero polynomial of degree d cannot vanish at all d+1 distinct natural numbers viewed as rationals, so one common natural t avoids every edge zero simultaneously. Nonedges are zero independently of t. This produces the same rational matrix with exact off-diagonal support and the proved kernel dimension.")),
                Paragraph(Text("Alon's arbitrary-field row-kernel argument applies to this nonsymmetric matrix. A kernel vector vanishing on an ordinary forcing set vanishes at every Black derivation: in a force row the black source and all other neighbors already have coordinate zero, leaving one nonzero edge coefficient times the target coordinate. Restriction of the kernel to the initial set is injective, hence every such set has cardinality at least (m-1)k. No theorem about symmetric maximum nullity is used.")),
                Paragraph(Text("Proposition 9 supplies the matching upper chronology. Initially color the last k vertices of the first m-1 legs. Descending along each selected leg, depth t+k forces depth t. Then depth k on the first leg forces the center; its depths k-j force depths j on the last leg for 1<=j<k; the center forces depth k there. Finally depth t-k on the last leg forces depth t. All sources are black and all competing neighbors are black. Taking the natural infimum of forcing-set cardinalities yields the equality.")))));
    }

    private static DocumentBlock Node(string id,string title,string name,Formula formula,string prose,
        DescribeRole role,AssessedProvenance? provenance = null,OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("spider-"+id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(formula)),provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))),role,resolution);
    private static Formula V(string x) => F.Id(x);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string x,params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname,Grp(V(x))),[.. args]);
    private static Formula Pair(Formula x,Formula y) => Seq(Open,x,Comma,y,Close);
    private static Formula All(string x,Formula type,Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(x),type,body);
    private static Formula Eq(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Ne(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Le(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula And(Formula x,Formula y) => new Formula.Logic(x,FormulaLogicOperator.And,y);
    private static Formula Imp(Formula x,Formula y) => new Formula.Logic(x,FormulaLogicOperator.Implies,y);
    private static Formula Iff(Formula x,Formula y) => new Formula.Logic(x,FormulaLogicOperator.Iff,y);
    private static Formula Add(Formula x,Formula y) => Seq(x,Plus,y);
    private static Formula Sub(Formula x,Formula y) => Seq(Open,x,Minus,y,Close);
    private static Formula Mul(Formula x,Formula y) => Seq(x,Sp,Times,Sp,y);
}
