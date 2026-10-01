using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ObservableTrajectoryCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized coordinates of observable trajectories", H("Normalized coordinates of observable trajectories"), Blocks(
            Describe.Lean(DescribeId.Create("observable-trajectory-coordinates"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ObservableTrajectoryCoordinates.observable_trajectory_coordinates"),
                H("Trajectory-image coordinates and the integrated Gramian"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let d and p be any nonnegative integers, E and W the real Euclidean spaces of those dimensions, B:E→E and C:E→W continuous linear maps. Assume that C B^k x=0 for every k<d implies x=0. Fix any T>0 and let H be the real Hilbert space L²((0,T];W) with restricted Lebesgue measure. All adjoints and norms below are Euclidean or Hilbert-space adjoints and induced operator norms.")),
                    Paragraph(Text("There exists a bounded linear map F:E→H whose representatives equal C exp(t B)x almost everywhere for every x. It is injective and its range has dimension d. There exist an orthonormal basis b indexed by Fin d of that actual range, a bounded linear map U:H→E, and a real d by d matrix M. Write P for the actual orthogonal projection onto the range of F. U is the basis-coordinate isometry composed with the projection onto that range, and M represents U F in the standard Euclidean state coordinates.")),
                    Paragraph(Text("For every L² class g and every i<d, the scalar function inner(b(i)(t),g(t)) is interval integrable on [0,T], and U(g)(i) equals its integral. Every representative is allowed; no continuity is imposed on g or the representatives of the basis. U contracts the norm and U*U=P. Also (UF)*(UF)=F*F. The display gives the representative and exact Gramian identities; the integral is the actual Bochner interval integral.")),
                    Paragraph(Text("Here A and D denote the matrices of the given operators B and C, respectively, in the standard Euclidean bases. The matrix identity concerns the actual continuous exponential trajectory Gramian. Empty state or output index sets are permitted; in dimension zero the image basis and coordinate index set are empty.")),
                    Paragraph(Text("Continuous trajectories belong to L² on the finite interval. If a trajectory is zero in L², continuity makes it zero on the interval. Analytic continuation and exponential-series coefficient uniqueness make every C B^k x zero, and finite observability makes x zero. An orthonormal basis of the image then provides the coordinate map. Orthogonal projection and the L² inner-product integral give its contraction and coefficient identities; preservation of trajectory inner products and exchange of a finite-dimensional continuous linear map with the integral give the exact Gramian."))), DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula time = F.Id("T"), t = F.Id("t"), x = F.Id("x");
        Formula f = F.Id("F"), u = F.Id("U"), m = F.Id("M"), b = F.Id("A"), c = F.Id("D");
        Formula adj(Formula z) => Seq(z, Caret, Grp(Star));
        Formula tr(Formula z) => Seq(z, Caret, Grp(F.Id("T")));
        Formula exp(Formula z) => Seq(Exp, Open, z, Close);
        Formula interval(Formula z) => Seq(Int, Underscore, Grp(D(0)), Caret, Grp(time), z, Sp, F.Id("dt"));
        Formula trajectory = Seq(f, Open, x, Close, Open, t, Close, Eq,
            F.Id("C"), exp(Seq(t, Sp, F.Id("B"))), x, Sp, Mathrm, Grp(F.Id("a"), Dot, F.Id("e"), Dot));
        Formula a = Seq(F.Id("C"), exp(Seq(t, Sp, F.Id("B"))));
        Formula grams = Seq(adj(f), f, Eq, interval(Seq(adj(Grp(a)), Grp(a))));
        Formula matrixGram = Seq(tr(m), m, Eq,
            interval(Seq(exp(Seq(t, Sp, tr(b))), tr(c), c, exp(Seq(t, Sp, b)))));
        return Disp(Seq(Exists, Sp, f, Comma, Sp, F.Id("b"), Comma, Sp, u, Comma, Sp, m, Comma, Sp,
            Begin, Grp(F.Id("gathered")), trajectory, RowBreak, Grp(),
            adj(u), u, Eq, F.Id("P"), Comma, Sp, grams, RowBreak, Grp(),
            matrixGram, End, Grp(F.Id("gathered"))));
    }
}
