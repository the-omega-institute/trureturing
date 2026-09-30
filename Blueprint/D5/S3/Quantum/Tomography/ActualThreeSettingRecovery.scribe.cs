using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class ActualThreeSettingRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Tomography/ActualThreeSettingRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three actual qubit expectation settings recover a density matrix with a sharp trace-norm noise bound and physical restoration without larger error.",
        H("Actual three-setting qubit recovery"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-three-setting-recovery"),
                DeclarationHandle.Create(Module + "actual_three_setting_recovery"),
                H("Exact reconstruction, sharp noise, and physical projection"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let phi be the real golden ratio, r=1/phi, s=sqrt(r), "
                        + "b=rs, and h=r squared minus r. The actual complex matrices are "
                        + "P=diag(1,0), Q=[[r squared,b],[b,r]], and V=diag(i,1). "
                        + "For 0<=p<=1 and x squared plus y squared at most p(1-p), "
                        + "rho=[[p,x+iy],[x-iy,1-p]] is positive semidefinite with trace one. "
                        + "P and Q are positive semidefinite projections, and V is unitary.")),
                    Paragraph(Text("The three real expectations m0=Re tr(P rho), "
                        + "m1=Re tr(Q rho), and m2=Re tr(Q V rho V adjoint) are the "
                        + "population readouts of the three settings, not individual "
                        + "measurement outcomes. They equal p, r+hp+2bx, and "
                        + "r+hp-2by, respectively. Since b is positive, the displayed "
                        + "inversion recovers all three real state parameters exactly.")),
                    Paragraph(Text("For arbitrary real errors eta0, eta1, eta2 with each absolute "
                        + "value at most epsilon, where epsilon is nonnegative, the raw linear "
                        + "estimate has diagonal entries pHat and 1-pHat and upper off-diagonal "
                        + "entry xHat+i yHat. It is Hermitian and trace one; it need not be "
                        + "positive semidefinite. Its error is measured by the actual matrix "
                        + "traceNorm, not by a replacement coordinate norm.")),
                    Paragraph(Text("The constant sqrt(1+2phi) is attained simultaneously by "
                        + "eta0=eta1=eta2=epsilon at the physical source rho0=I/2. For every "
                        + "positive epsilon at most 1/(2 sqrt(1+2phi)), all three noisy "
                        + "expectations remain in [0,1], the raw output is positive semidefinite, "
                        + "and its half trace-norm error equals the bound. Thus no smaller "
                        + "uniform constant applies even arbitrarily close to I/2.")),
                    Paragraph(Text("Center the raw parameters as (pHat-1/2,xHat,yHat). Multiply "
                        + "this vector by one if its Euclidean radius is at most 1/2, or by "
                        + "(1/2)/radius otherwise, and then restore the first coordinate's "
                        + "center. The resulting matrix is positive semidefinite with trace one. "
                        + "Its actual half trace-norm distance to rho does not exceed the "
                        + "raw distance. These centered coordinates correspond to Bloch "
                        + "coordinates (2x,-2y,2p-1) after scaling and reordering; no Bloch "
                        + "coordinate convention is silently substituted."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        Formula p = F.Id("p"), x = F.Id("x"), y = F.Id("y");
        Formula r = F.Id("r"), b = F.Id("b"), h = F.Id("h");
        Formula eps = F.Id("epsilon"), phi = F.Id("phi");
        Formula m0 = Sub("m", 0), m1 = Sub("m", 1), m2 = Sub("m", 2);
        return Disp(new Formula.Aligned([
            Seq(D(0), Le, Sp, p, Le, D(1), Comma, Sp, Sq(x), Plus, Sq(y), Le,
                Sp, p, Open, D(1), Minus, p, Close),
            Seq(m0, Eq, p, Comma, Sp, m1, Eq, r, Plus, h, p, Plus, D(2), b, x,
                Comma, Sp, m2, Eq, r, Plus, h, p, Minus, D(2), b, y),
            Seq(p, Eq, m0, Comma, Sp, x, Eq,
                Fr(Seq(m1, Minus, r, Minus, h, m0), Seq(D(2), b)), Comma, Sp,
                y, Eq, Fr(Seq(r, Plus, h, m0, Minus, m2), Seq(D(2), b))),
            Seq(D(0), Le, Sp, eps, Comma, Sp,
                Bar, Sub("eta", 0), Bar, Le, Sp, eps, Comma,
                Bar, Sub("eta", 1), Bar, Le, Sp, eps, Comma,
                Bar, Sub("eta", 2), Bar, Le, Sp, eps,
                Longrightarrow, Fr(Seq(F.Id("traceNorm"), Open, F.Id("rhoHat"),
                    Minus, Rho, Close), D(2)), Le,
                Seq(Root(Seq(D(1), Plus, D(2), phi)), eps)),
            Seq(D(0), Lt, eps, Le, Fr(D(1), Seq(D(2), Root(Seq(
                D(1), Plus, D(2), phi)))), Longrightarrow,
                Fr(Seq(F.Id("traceNorm"), Open, F.Id("rhoHat"), Minus,
                    Fr(F.Id("I"), D(2)), Close), D(2)), Eq,
                Seq(Root(Seq(D(1), Plus, D(2), phi)), eps)),
            Seq(F.Id("PSD"), Open, F.Id("rhoProj"), Close, Comma, Sp,
                F.Id("trace"), Open, F.Id("rhoProj"), Close, Eq, D(1), Comma, Sp,
                Fr(Seq(F.Id("traceNorm"), Open, F.Id("rhoProj"), Minus,
                    Rho, Close), D(2)), Le,
                Fr(Seq(F.Id("traceNorm"), Open, F.Id("rhoHat"), Minus,
                    Rho, Close), D(2)))
        ]));
    }

    private static Formula Sq(Formula x) => Seq(x, Caret, Grp(D(2)));
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Sub(string name, int index) =>
        Seq(F.Id(name), Underscore, Grp(D((byte)index)));
    private static Formula Fr(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
}
