using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class FiniteRankUnitaryDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/FiniteRankUnitaryDefect.";
    private static Formula Op(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula App(string s, params Formula[] a) => Seq(Op(s), Open,
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x,Comma,Sp,y)), Close);
    private static Formula Norm(Formula x) => Seq(Vert,Sp,x,Vert);
    private static Formula Pow(Formula x, Formula y) => Seq(Open,x,Close,Caret,Grp(y));
    private static Formula Sub(Formula x, Formula i) => Seq(x,Underscore,Grp(i));
    private static Formula S => F.Id("S");
    private static Formula U => F.Id("U");
    private static Formula B => F.Id("b");
    private static Formula G => F.Id("g");
    private static Formula T => F.Id("T");
    private static Formula M => F.Id("M");
    private static Formula Delta => F.Id("delta");
    private static Formula Q(Formula u) => App("projectionDefect",S,u);
    private static Formula HS(Formula u) => App("IsHilbertSchmidt",Q(u));
    private static Formula Summable(Formula u) => App("Summable",Seq(F.Id("l"),Mapsto,
        Pow(Norm(Seq(Q(u),Sub(B,F.Id("l")))),D(2))));
    private static Formula PairD => App("D",S,U,B);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-rank unitary projection defects have genuine ambient Hilbert-Schmidt energy and a quantitative finite-synthesis bound.",
        H("Finite Rank Unitary Defect"),
        Blocks(
            Paragraph(Text("H is any complete complex Hilbert space, including infinite-dimensional and "
                + "nonseparable spaces. S is a finite-dimensional subspace of the original H and P_S its "
                + "canonical orthogonal projection. A unitary is a complex-linear isometric equivalence of H. "
                + "The ambient Hilbert basis b may have an arbitrary index type beta. Define "
                + "projectionDefect(S,U) = U P_S U^{-1} − P_S. Its range is finite; summability below "
                + "establishes a genuine ambient Hilbert-Schmidt quantity. No finite-dimensional ambient "
                + "replacement or ambient invariance assumption is used.")),
            Describe.Lean(DescribeId.Create("unitary-projection-defect-has-sum"),
                DeclarationHandle.Create(Prefix + "unitary_projection_defect_hasSum"), H("Exact ambient square sum"),
                StatementSource.FromAuthor(Disp(Seq(Forall,Sp,S,InMacro,Sp,App("Subspace",F.Id("H")),Comma,Sp,
                    App("FiniteDimensional",S),Rightarrow,Sp,
                    Forall,Sp,F.Id("c"),InMacro,Sp,App("OrthonormalBasis",F.Id("iota"),S),Comma,Sp,
                    U,InMacro,Sp,App("Unitary",F.Id("H")),Comma,Sp,
                    B,InMacro,Sp,App("HilbertBasis",F.Id("beta"),F.Id("H")),Comma,Sp,
                    App("HasSum",Seq(F.Id("l"),Mapsto,Pow(Norm(Seq(Q(U),Sub(B,F.Id("l")))),D(2))),
                        Seq(D(2),Sum,Underscore,Grp(F.Id("i"),InMacro,Sp,F.Id("iota")),
                        Pow(Norm(Seq(Sub(F.Id("P"),Seq(S,Caret,Grp(Perp))),U,
                            Sub(F.Id("c"),F.Id("i")))),D(2))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The index type iota is finite; beta is arbitrary. The finite-rank "
                    + "expansion is summed using Hilbert-basis Parseval, including uncountable bases. "
                    + "For two orthonormal families the overlap terms cancel, and the projection Pythagorean "
                    + "identity yields exactly twice the cross-block energy. The same identity on every b "
                    + "also identifies the square sum independently of the ambient basis."))),DescribeRole.Theorem),
            Paragraph(Text("For a pair U indexed by Fin 2, define D(S,U,b) as the square root of "
                + "one half the sum over g of the ambient square sum of projectionDefect(S,U_g) on b. "
                + "Thus D is exactly the root mean square of the two ambient Hilbert-Schmidt norms. "
                + "Write E = EuclideanSpace(C,Fin 24), with its standard Hilbert norm.")),
            Describe.Lean(DescribeId.Create("rank-twentyfour-projection-bound"),
                DeclarationHandle.Create(Prefix + "exists_rank_twentyfour_projection_bound"), H("Rank twenty-four projection bridge"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall,Sp,B,InMacro,Sp,App("HilbertBasis",F.Id("beta"),F.Id("H")),Comma,Sp,
                    T,Colon,F.Id("E"),To,F.Id("H"),Comma,Sp,
                    Open,Exists,Sp,F.Id("z"),InMacro,Sp,F.Id("E"),Comma,Sp,
                    Norm(F.Id("z")),Eq,D(1),Land,Sp,D(1),Le,Norm(Seq(T,F.Id("z"))),Close,
                    Rightarrow,Sp,Forall,Sp,U,Colon,App("Fin",D(2)),To,App("Unitary",F.Id("H")),Comma,Sp,
                    M,Colon,App("Fin",D(2)),To,App("End",F.Id("E")),Comma,Sp,
                    Delta,InMacro,Sp,Seq(Mathbb,Grp(F.Id("R"))),Comma,Sp,D(0),Le,Delta,Rightarrow,Sp,
                    Open,Forall,Sp,G,InMacro,Sp,App("Fin",D(2)),Comma,Sp,
                    Norm(Sub(M,G)),Le,D(8,5),Land,Sp,
                    Norm(Seq(Sub(U,G),T,Minus,T,Sub(M,G))),Le,D(9,5),Delta,Close,
                    Rightarrow,Sp,Exists,Sp,S,InMacro,Sp,App("Subspace",F.Id("H")),Comma,Sp,
                    App("FiniteDimensional",S),Land,Sp,D(1),Le,App("dim",S),Le,D(2,4),Land,Sp,
                    Open,Forall,Sp,G,InMacro,Sp,App("Fin",D(2)),Comma,Sp,HS(Sub(U,G)),Close,Land,Sp,
                    Open,Forall,Sp,G,InMacro,Sp,App("Fin",D(2)),Comma,Sp,Summable(Sub(U,G)),Close,Land,Sp,
                    PairD,Le,D(7,8,5),Pow(Delta,Frac(D(1),D(2,4))),Land,Sp,
                    Open,Delta,Eq,D(0),Rightarrow,Sp,Forall,Sp,G,InMacro,Sp,App("Fin",D(2)),Comma,Sp,
                    Q(Sub(U,G)),Eq,D(0),Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All displayed maps T and M are continuous and complex-linear. "
                    + "The selected spectral cut has no independence, Gram-inverse or assumed-gap premise. "
                    + "For positive delta the cutoff is (6/5) delta^(1/24) when delta^(1/24) < 5/6. "
                    + "The uniform operator leakage bound and the exact ambient square sum give "
                    + "D <= 7(85 eta + 95 delta eta^(-23)); (6/5)^23 >= 10 yields the stated 785. "
                    + "For larger delta a projection contraction gives D <= 7. At delta = 0 the "
                    + "nonzero range of T is finite-dimensional and invariant. A unitary image has the "
                    + "same finite dimension, so invariance is equality and the range projection commutes "
                    + "with both operators. The theorem is valid for every nonnegative delta. "
                    + "C117FixedFourteenProjection consumes this analytic supplier with the exact twenty-four braid "
                    + "words, fourteen tails, polynomial parameter, residual identities and bounds 85 and 95 "
                    + "proved in its source-specific module. Those bounds are explicit hypotheses here "
                    + "and the complete original lemma is stated and proved in that consumer."))),DescribeRole.Theorem))));
}
