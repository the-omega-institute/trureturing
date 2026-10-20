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
                    Paragraph(Text("Continuous trajectories belong to L² on the finite interval. If a trajectory is zero in L², continuity makes it zero on the interval. Analytic continuation and exponential-series coefficient uniqueness make every C B^k x zero, and finite observability makes x zero. An orthonormal basis of the image then provides the coordinate map. Orthogonal projection and the L² inner-product integral give its contraction and coefficient identities; preservation of trajectory inner products and exchange of a finite-dimensional continuous linear map with the integral give the exact Gramian."))), DescribeRole.Theorem),
            Paragraph(Text("For the finite observation experiment take d,p>=1. Any externally supplied bounded linear F with the displayed almost-everywhere trajectory representatives equals the F constructed above: equality of those representatives gives equality of their L2 classes for every state. Fix any orthonormal basis b of this same range. Its coordinate map is U=b.repr composed with orthogonal projection, and its matrix M represents UF. Since the projection is the identity on the trajectory range and b.repr is an isometry, (UF)*UF=F*F for this chosen basis as well. Thus M transpose M is the same integrated Gramian G(T), and each coordinate is the stated integral against that basis. The construction does not require replacing the supplied trajectory or its basis.")),
            Paragraph(Text("For finite polynomial moments, fix m>=0 and polynomials ell_0,...,ell_m orthonormal on [0,1], of degrees at most m. Index the q=(m+1)p scalar coordinates by pairs (k,r), and define row (k,r), column j of M to be T to the power -1/2 times the integral from 0 to T of ell_k(t/T) times the r coordinate of C exp(tB)e_j. These continuous integrands are integrable; moving evaluation through the finite-dimensional integral and expanding x in the standard basis gives (Mx)_(k,r)=T to the power -1/2 times the integral of ell_k(t/T)(C exp(tB)x)_r. Hence this is the actual normalized moment map, with Gramian G_mom=M transpose M. Use q independent standard Gaussian noise coordinates, independent of X, and data Y=MX+sigma xi. Applying gaussian_observation_law with this rectangular M gives posterior covariance (beta I+sigma to the power -2 times G_mom) inverse and mean sigma to the power -2 times that covariance times M transpose Y. Its information, all-measurable-estimator Bayes energy risk, centered free energy and known skew-flow future risk follow by the same joint-law and risk arguments in the Gaussian observation narrative. The moment formulas use G_mom; the trajectory-basis formulas use G(T). Neither matrix needs a rank hypothesis for the Gaussian calculation because beta>0 keeps the precision positive definite.")))));

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
