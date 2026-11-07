using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class FiniteSynthesisSpectralCutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/FiniteSynthesisSpectralCut.";
    private static Formula Op(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula App(string s, params Formula[] a) => Seq(Op(s), Open, Join(a), Close);
    private static Formula Join(Formula[] a) => a.Length == 0 ? Seq() :
        a.Skip(1).Aggregate(a[0], (x, y) => Seq(x, Comma, Sp, y));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert, Sp);
    private static Formula Pow(Formula x, Formula y) => Seq(Open, x, Close, Caret, Grp(y));
    private static Formula Sub(Formula x, Formula y) => Seq(x, Underscore, Grp(y));
    private static Formula T => F.Id("T");
    private static Formula Eta => F.Id("eta");
    private static Formula K => F.Id("k");
    private static Formula N => F.Id("n");
    private static Formula Z => F.Id("z");
    private static Formula Y => F.Id("y");
    private static Formula S => App("sourceCut", T, K);
    private static Formula V => App("imageCut", T, K);
    private static Formula Sig(Formula i) => App("singular", T, i);
    private static Formula P(Formula v, Formula z) => Seq(Sub(F.Id("P"), v), z);
    private static Formula Premise => Seq(Forall, Sp, T, Colon, F.Id("E"), To,Sp,
        Underscore, Grp(Seq(Mathbb, Grp(F.Id("C")))), F.Id("H"), Comma, Sp,
        Open, Exists, Sp, Z, InMacro, Sp, F.Id("E"), Comma, Sp, Norm(Z), Eq, D(1),
        Land, Sp, D(1), Le,Sp, Norm(Seq(T,Z)), Close, Rightarrow, Sp,
        Forall, Sp, Eta, InMacro, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp,
        D(0), Lt,Sp, Eta, Lt,Sp, D(1), Rightarrow, Sp,
        Exists, Sp, K, InMacro, Sp, App("Fin", N), Comma, Sp);
    private static Formula Rank => Seq(D(1), Le,Sp, App("dim", V), Le,Sp, N);
    private static Formula Power => Pow(Eta, Seq(N, Minus, D(1)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite synthesis into an arbitrary complex Hilbert space admits a data-selected positive spectral cut.",
        H("Finite Synthesis Spectral Cut"),
        Blocks(
            Paragraph(Text("E is any finite-dimensional complex inner-product space, n = dim E, "
                + "and H is any complete complex Hilbert space, with no dimension or separability restriction. "
                + "T is continuous and complex-linear. Singular values and right singular vectors are those "
                + "of T with codomain restricted to its actual finite range. Indexing is zero-based. "
                + "sourceCut(T,k) spans right singular vectors with index at most k; imageCut(T,k) is "
                + "its image in the original H. P denotes the canonical orthogonal projection. "
                + "No column independence, preassigned gap or Gram inverse is assumed.")),
            Describe.Lean(DescribeId.Create("finite-synthesis-exists-spectral-cut"),
                DeclarationHandle.Create(Prefix + "exists_spectral_cut"), H("Selected spectral cut"),
                StatementSource.FromAuthor(Disp(Seq(Premise,
                    Power, Le,Sp, Sig(K), Land, Sp,
                    Sig(Seq(K, Plus, D(1))), Le,Sp, Eta, Sig(K), Land, Sp, Rank, Land, Sp,
                    Open, Forall, Sp, Z, InMacro, Sp, S, Comma, Sp,
                    Sig(K), Norm(Z), Le,Sp, Norm(Seq(T,Z)), Close, Land, Sp,
                    Open, Forall, Sp, Z, InMacro, Sp, F.Id("E"), Comma, Sp,
                    P(V, Seq(T,Z)), Eq, T, P(S,Z), Close, Land, Sp,
                    Open, Forall, Sp, Z, InMacro, Sp, F.Id("E"), Comma, Sp,
                    Norm(Seq(T,Z, Minus, P(V,Seq(T,Z)))), Le,Sp,
                    Sig(Seq(K,Plus,D(1))), Norm(Z), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first geometric singular-value gap is selected by finite search. "
                    + "Preceding failures of the gap inequality yield a positive lower bound. "
                    + "The Gram eigenbasis separates the source cut from its orthogonal complement, "
                    + "giving the exact ambient projection and tail bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-synthesis-cut-intertwining-bound"),
                DeclarationHandle.Create(Prefix + "exists_cut_intertwining_bound"), H("Uniform intertwining leakage"),
                StatementSource.FromAuthor(Disp(Seq(Premise, Rank, Land, Sp,
                    App("Orthonormal", App("cutFrame",T,K)), Land, Sp,
                    Forall, Sp, F.Id("U"), Colon, F.Id("H"), To, Sp, F.Id("H"), Comma, Sp,
                    F.Id("M"), Colon, F.Id("E"), To, Sp, F.Id("E"), Comma, Sp,
                    Y, InMacro, Sp, V, Comma, Sp,
                    Norm(Seq(F.Id("U"),Y,Minus,P(V,Seq(F.Id("U"),Y)))), Le,Sp,
                    Open, Eta,Norm(F.Id("M")),Plus,
                    Pow(Power,Seq(Minus,D(1))),Norm(Seq(F.Id("U"),T,Minus,T,F.Id("M"))),
                    Close,Norm(Y)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("U and M are arbitrary continuous complex-linear operators on H and E, "
                    + "respectively. The same cut works for all of them. cutFrame is the normalized "
                    + "ambient image of each selected right singular vector, indexed by the finite interval "
                    + "of indices at most k. The precise splitting UT = TM + (UT − TM) is estimated "
                    + "after projection onto the orthogonal complement. The lower singular bound is "
                    + "applied only on the selected source subspace. This is an operator-norm leakage "
                    + "estimate; it does not by itself establish C117 Lemma 46.2 or its exact braid residual identities."))),
                DescribeRole.Theorem))));
}
