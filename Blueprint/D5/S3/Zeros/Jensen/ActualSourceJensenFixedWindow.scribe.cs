using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class ActualSourceJensenFixedWindowDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef ThetaSource =
        LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal");
    private static readonly LibraryNoteRef HermiteZeros =
        LibraryNoteRef.Create("D5/L/Analytic/nist2026dlmforthogonalzeros");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized all-mode theta source has a fixed-window actual-node target and an original-disk occurrence target.",
        H("Actual source Jensen fixed window"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-source-jensen-fixed-window"),
            DeclarationHandle.Create(
                "D5/S3/Zeros/Jensen/ActualSourceJensenFixedWindow.actual_source_jensen_fixed_window"),
            H("Fixed windows and arbitrary-order isolating disks"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(ThetaSource, HermiteZeros),
            Blocks(
                Paragraph(Text("Let F be the cosine-square transform of the normalized full theta density, and let f be half the transform of the raw full kernel. Then Z=fullZ>0, 2/Z>0 and F=(2/Z)f at every complex argument. The polynomial p_n is sourceP(n) at the negative argument, complexified. On the real line p_n(t)=originalJ(n,t), and D=fullD(n,t)=-sourceP(n)'(-t).")),
                Paragraph(Text("For every T>0 there is n0 such that every n>=n0 satisfies n>=1, and for every t with 0<t<=T AND originalJ(n,t)=0, D*G>=D^2/2>0. All actual nodes are included; the threshold may depend on T.")),
                Paragraph(Text("At such a node D and G are nonzero and (2n+1)G=2nD-M/2, where M=fullM2(n,t). At ell*t, ell=(n+1)/n, originalJ(n+1) has derivative G with respect to its real argument and value (t/n)*G, which is nonzero. sourceQ(n) has a simple zero at 1/t and a nonzero simple cofactor.")),
                Paragraph(Text("For xi=n/(n+1)/t and q=sourceQ(n+1), xi>0, q'(xi)=0, (n+1)q(xi)=xi^n*G and xi^2*q''(xi)=-n*xi^n*D. Their product is -(n/(n+1))*xi^(2n-2)*D*G. Both q(xi) and q''(xi) are nonzero. The guarded coupling satisfies coupling*D^2=(xi^2/n)*D*G>0.")),
                Paragraph(Text("For every positive zero t0 of F, every exact finite order m>=1 and every original isolating radius delta>0, there are C,d>0 and N such that every n>=N satisfies n>=1 and has injectively indexed positive real nodes nodes:Fin(m)->Real. Each node is an actual originalJ(n) zero and a simple p_n zero strictly inside the original delta disk; |nodes(i)-t0|<=C/sqrt(n), |D(n,nodes(i))|>=d/(sqrt(n))^(m-1), and |M(n,nodes(i))|<=n*|D(n,nodes(i))| for EVERY index.")),
                Paragraph(Text("The original boundary has no polynomial zero. The filtered polynomial root multiset equals the multiset map of all Fin(m) indices under nodes, has cardinality m, and has count one at every nodes(i). Each simple cofactor is nonzero. Every signed, adjacent and reflected consequence is evaluated at nodes(i) for the same n.")),
                Paragraph(Text("The normalized coefficients are a(j)=(-1)^j*mu(j)/(2j)!, where mu(j) is the full theta moment. The coefficients of H=-4z*F''-2F' are (-1)^j*mu(j+1)/(2j)!. Integrating the actual finite polynomial term by term proves that its coefficient polynomial is exactly fullM2, with the same fullZ normalization as F.")),
                Paragraph(Text("The affine polynomial P(n)(t0*(1+u/sqrt(n))) is divided by its actual nonzero real leading Taylor normalizer. Uniform complex convergence to the monic Hermite polynomial gives all m real simple nodes and one derivative margin. For m>=2, H has exact order m-2, and its own scaled estimate bounds fullM2. At m=2 this is order zero. For m=1 a uniform coefficient norm bounds fullM2 directly, without an order or nonvanishing premise on H.")),
                Paragraph(Text("Local Taylor uses sigma=min(delta/2,t0/2,1), while the boundary comparison uses the positive minimum of |F| on the caller's original delta sphere. F(0)=1 rules out every locally zero analytic branch. Its complete real zero set in [0,T] is finite; local disks cover those zeros, and uniform approximation excludes polynomial zeros on the compact remainder. The exact root multiset equality then identifies every arbitrary actual node with a local node.")),
                Paragraph(Text("The full theta source follows Romik's theta/Fourier representation. The Hermite normalization and real simple roots are classical; Mathlib supplies the coefficient convention and the positive-recurrence argument supplies root reality. The analytic-unit and logarithmic-derivative disk argument is the classical argument-principle comparison, proved here with the root multiset and its repetitions. These attributions do not assert a literature originality result.")),
                Paragraph(Text("The unit/logarithm disk comparison retains multiset multiplicities. No RH, simple limiting zero, global hyperbolicity, chosen actual root list, count premise or error premise is included. The threshold is not uniform over growing windows and establishes neither RH nor strict Robin beyond 5040."))),
            DescribeRole.Theorem))));

    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(D(0), Lt, F.Id("Z"), Comma, Sp, D(0), Lt, Frac, Grp(D(2)), Grp(F.Id("Z")), Comma, Sp, F.Id("F"), Eq, Frac, Grp(D(2)), Grp(F.Id("Z")), F.Id("f")),
        Seq(Forall, Sp, F.Id("T"), Gt, D(0), Comma, Sp, Exists, Sp, F.Id("nzero"), Comma,
            Sp, Forall, Sp, F.Id("n"), Ge, Sp, F.Id("nzero"), Comma, Sp, F.Id("n"), Ge, Sp, D(1), Land, Sp, Forall, Sp, F.Id("t"), Comma),
        Seq(D(0), Lt, F.Id("t"), Le, Sp, F.Id("T"), Sp, Land, Sp,
            Call("originalJ", F.Id("n"), F.Id("t")), Eq, D(0), Implies, Sp, F.Id("DG"), Ge, Sp, Frac, Grp(Seq(F.Id("D"), Caret, D(2))), Grp(D(2)), Gt, D(0),
            Sp, Land, Sp, Call("NodeResponse", F.Id("n"), F.Id("t"))),
        Seq(Forall, Sp, F.Id("tzero"), Gt, D(0), Comma, Sp,
            Call("F", F.Id("tzero")), Eq, D(0), Comma, Sp, Forall, Sp, F.Id("m"), Ge, Sp, D(1), Comma),
        Seq(Forall, Sp, F.Id("delta"), Comma, Sp, Call("IsExactRealOrder", F.Id("F"), F.Id("tzero"), F.Id("m")), Sp, Land, Sp,
            Call("IsolatingDisk", F.Id("F"), F.Id("tzero"), F.Id("delta")), Implies, Sp, Call("LocalConclusion", F.Id("tzero"), F.Id("delta"), F.Id("m")))
    ]));
}
