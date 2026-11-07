using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class C117FixedFourteenProjectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/C117FixedFourteenProjection.";
    private static Formula Op(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula App(string s, params Formula[] a) => Seq(Op(s), Open,
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x,Comma,Sp,y)), Close);
    private static Formula Norm(Formula x) => Seq(Vert,x,Vert);
    private static Formula Pow(Formula x, Formula y) => Seq(Open,x,Close,Caret,Grp(y));
    private static Formula S => F.Id("S");
    private static Formula Delta => F.Id("delta");
    private static Formula G => F.Id("g");
    private static Formula Defect => App("defect",F.Id("b"),S,F.Id("s"),F.Id("t"));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete original C117 Lemma 46.2: fourteen cubic residuals yield an ambient orthogonal projection of rank one through twenty-four.",
        H("C117 Fixed Fourteen Projection"),
        Blocks(
            Paragraph(Text("H is any complete complex Hilbert space, including infinite-dimensional and nonseparable H. "
                + "s and t are arbitrary complex-linear isometric equivalences H to H with s t s = t s t. "
                + "Thus every genuine unitary B3 representation supplies such a pair. v is any vector with norm one. "
                + "b is any Hilbert basis, with arbitrary index type beta; its existence imposes no extra restriction on H. "
                + "Set x=(sqrt(5)-1)/2 and a=x^2 in the specified real embedding. "
                + "cubicOperator(a,s) is exactly s^3-a s^2+a s-I on the original H.")),
            Paragraph(Text("wordEval multiplies the letters in their written algebraic order. "
                + "The ordered twenty-four orbit words are: 1; s; s^-1; t; t s; t s^-1; s t; s t s; s t s^-1; "
                + "s^-1 t; s^-1 t s; s^-1 t s^-1; t^-1; t^-1 s; t^-1 s^-1; s t^-1; s t^-1 s; s t^-1 s^-1; "
                + "s^-1 t^-1; s^-1 t^-1 s; s^-1 t^-1 s^-1; t^-1 s t^-1; s t^-1 s t^-1; s^-1 t^-1 s t^-1. "
                + "The synthesis map takes standard basis vector j to wordEval(q_j)v. No linear independence is assumed.")),
            Paragraph(Text("The ordered fourteen tails are exactly: 1; t; t s; t s^-1; t^-1; t^-1 s; t^-1 s^-1; "
                + "t^-1 s t^-1; t^-1 s^-2; t^-2 s^-1; t^-2; t^-1 s^-3; s^-1; t^-2 s^-2. "
                + "delta is the maximum over these fourteen tails of norm(cubicOperator(a,s) wordEval(h)v). "
                + "columns and errors retain all forty-eight source columns and every listed residual triple, "
                + "including all seventeen terms of t column twelve. environment_columns proves these identities "
                + "directly from the braid relation for arbitrary complex a, rather than assuming the source prose.")),
            Paragraph(Text("For S a finite-dimensional subspace of the original H, E=S.starProjection is the actual "
                + "orthogonal projection H to H. projectionDefect(S,g)=g E g^-1-E. "
                + "defect(b,S,s,t) is sqrt((1/2) sum over g=s,t of sum over l in beta of "
                + "norm(projectionDefect(S,g)(b_l))^2). The square sums are summable, and each ambient defect "
                + "is certified Hilbert-Schmidt, so this is the genuine D(E) in the original lemma.")),
            Describe.Lean(DescribeId.Create("c117-condition-free-projection"),
                DeclarationHandle.Create(Prefix + "condition_free_projection"), H("Condition-free bounded-rank projection"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall,Sp,F.Id("b"),InMacro,Sp,App("HilbertBasis",F.Id("beta"),F.Id("H")),Comma,Sp,
                    F.Id("s"),Comma,F.Id("t"),InMacro,Sp,App("Unitary",F.Id("H")),Comma,Sp,
                    F.Id("s"),F.Id("t"),F.Id("s"),Eq,F.Id("t"),F.Id("s"),F.Id("t"),Rightarrow,Sp,
                    Forall,Sp,F.Id("v"),InMacro,Sp,F.Id("H"),Comma,Sp,Norm(F.Id("v")),Eq,D(1),Rightarrow,Sp,
                    Exists,Sp,S,InMacro,Sp,App("Subspace",F.Id("H")),Comma,Sp,
                    App("FiniteDimensional",S),Land,Sp,App("OrthogonalProjection",App("starProjection",S)),Land,Sp,
                    App("range",App("starProjection",S)),Eq,S,Land,Sp,
                    D(1),Le,App("dim",S),Le,D(2,4),Land,Sp,
                    Open,Forall,Sp,G,InMacro,Sp,App("pair",F.Id("s"),F.Id("t")),Comma,Sp,
                    App("IsHilbertSchmidt",App("projectionDefect",S,G)),Land,Sp,
                    App("Summable",App("ambientSquareSum",F.Id("b"),S,G)),Close,Land,Sp,
                    Open,D(0),Lt,Delta,Lt,D(1),Rightarrow,Sp,Defect,Le,
                        D(7,8,5),Pow(Delta,Frac(D(1),D(2,4))),Close,Land,Sp,
                    Open,Delta,Eq,D(0),Rightarrow,Sp,Defect,Eq,D(0),Land,Sp,
                        Forall,Sp,G,InMacro,Sp,App("pair",F.Id("s"),F.Id("t")),Comma,Sp,
                        App("projectionDefect",S,G),Eq,D(0),Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit matrix column coefficient sums are at most thirteen. "
                    + "The at-most-seventeen residual terms per column have coefficients of norm at most one "
                    + "and their right tails all belong to the exact fourteen-tail list. The proved identities "
                    + "give operator bounds norm(M_g)<=85 and norm(gT-TM_g)<=95 delta. "
                    + "FiniteSynthesisSpectralCut selects the first geometric singular gap without a gap hypothesis, "
                    + "normalizes only positive selected singular vectors and estimates their ambient leakage. "
                    + "FiniteRankUnitaryDefect proves the ambient Hilbert-Schmidt square-sum identity and uses "
                    + "eta=(6/5) delta^(1/24), with a separate contraction estimate for large delta, to obtain 785. "
                    + "At delta=0, the nonzero finite synthesis range is invariant; its unitary image has the same "
                    + "finite dimension and therefore equals the range. Its orthogonal projection commutes with both "
                    + "generators. There is no finite ambient, invariant ambient, singular-gap, independent-column "
                    + "or Gram-inverse premise. This proves Lemma 46.2 only; Theorem 46.5 and numerical coercivity "
                    + "remain outside this result. The orbit architecture and parameter tables reuse the supplied "
                    + "Marin cubic-Hecke calculation and are not counted as new mathematical content."))),DescribeRole.Theorem))));
}
