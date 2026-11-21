using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a;

internal sealed class HardinA229641StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical two-defect colourings of five-row HDA arrays", H("Canonical two-defect colourings of five-row HDA arrays"), Blocks(
            Paragraph(Text("Colours are introduced in row-major order. At the widths used in the recurrence, each canonical array has six distinct label permutations.")),
            Node("a",Count(),false,"The filter counts all literal five-by-n arrays with exactly two monochromatic horizontal, diagonal or antidiagonal bonds and canonical colour introduction."),
            Node("result",Recurrence(),true,"The order-thirty recurrence holds for every width at least thirty-four. Each natural count is cast to the integers before coefficients are applied."))));

    private static DocumentBlock Node(string name, Formula statement, bool theorem, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name), H(name), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229641")),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            name=="result"?new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229641"), ResolutionKind.Proved):null);

    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i)=>i==0?new[]{Seq(Operatorname,Grp(V(p)))}:new[]{Dot,Seq(Operatorname,Grp(V(p)))}).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula Sub(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Subtract,Parenthesized(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Multiply,Parenthesized(b));
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula AsInt(Formula a) => Typed(a,Q("Int"));
    private static Formula Own(string n,params Formula[] a) => Call("HardinA229641Strip."+n,a);
    private static Formula Count() => All("n",Q("Nat"),
        Eq(Own("a",V("n")),Call("HardinA229538Strip.canonicalCount",N(2),V("n"))));
    private static Formula Recurrence() {
        Formula a(int j)=>AsInt(Own("a",Add(V("n"),N(j))));
        long[] coefficients=[18, -15, -1191, 3468, 31983, -108707, -424479, 1614489, 2851598, -13478352, -7797810, 66347438, -12632640, -190067859, 147888798, 287096430, -412178619, -138135927, 522690894, -168525432, -273411640, 227616084, 9610272, -73617984, 21460464, 7359984, -4611168, 186624, 279936, -46656];
        Formula rhs=Mul(N(coefficients[0]),a(33));
        for(int i=1;i<coefficients.Length;i++)
            rhs=coefficients[i]<0 ? Sub(rhs,Mul(N(-coefficients[i]),a(33-i)))
                : Add(rhs,Mul(N(coefficients[i]),a(33-i)));
        return All("n",Q("Nat"),Eq(a(34),rhs));
    }
}
