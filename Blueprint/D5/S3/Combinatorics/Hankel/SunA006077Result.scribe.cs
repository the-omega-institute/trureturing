using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hankel;

internal sealed class SunA006077ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hankel/SunA006077Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/sun2013a006077");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal finite sum satisfies every clause at every natural index.", H("Sun's complete determinant assertion"),
        Blocks(Paragraph(Text("Nat denotes the nonnegative integers and Z the integers. Matrix.of is displayed with Fin-sized row and column binders and explicit val projections; det of the empty matrix is one. All floor quotients are natural division.")),
            Node("claim","All clauses of the assertion","claim",Iff(V("claim"),ClaimFormula()),"The zero branch and the positive odd integral normalized branch both quantify over every natural n, including n=0. No prime congruence from a later version is included.",DescribeRole.Definition),
            Node("result","The full all-index statement","result",ClaimFormula(),"The odd integral quotients d(m) and e(m) are nonzero, so their positive semidefinite real Hankel matrices are positive definite. Their determinants and therefore d(m),e(m) are positive. At indices 3m and 3m+2 the signed quotients are respectively d(m)e(m)^2 and d(m)e(m+1)^2. Both are positive odd integers; the remaining residue class vanishes. The index zero and empty shifted determinants are included. This states the v5 conjecture for its original finite sum. The zero branch, Rueppel parity evaluations and positive moment ingredients are established prior mathematics; this statement makes no claim of priority for their combination.",DescribeRole.Theorem,
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sun-a006077-hankel-determinants"), ResolutionKind.Proved))), []));
    private static DocumentBlock Node(string id,string title,string decl,Formula formula,string prose,DescribeRole role,AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("sun-a006077-result-"+id),DeclarationHandle.Create(Prefix+decl),
            H(title),StatementSource.FromAuthor(Disp(formula)),provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),role,resolution);
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
    private static Formula Z => new Formula.Integers();
    private static Formula NegOne => new Formula.Negate(N(1));
    private static Formula ClaimFormula()
    {
        var n=V("n"); var z=V("z");
        var r=Eq(new Formula.Modulo(n,N(3)),N(1));
        var exponent=new Formula.Floor(new Formula.Fraction(A(n,N(1)),N(3)));
        return All("n",Nat,And(Imp(r,Eq(C("W",n),N(0))),Imp(new Formula.Not(r),
            Ex("z",Z,And(Lt(N(0),z),And(C("Odd",z),
                Eq(M(P(NegOne,exponent),C("W",n)),M(P(N(6),n),z))))))));
    }
}
