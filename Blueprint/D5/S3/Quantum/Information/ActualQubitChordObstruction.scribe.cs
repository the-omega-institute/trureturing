using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualQubitChordObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ActualQubitChordObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two globally exact signal probes force a pure-ended qubit chord, an endpoint overlap bound, and a pointwise spectral QFI lower bound on the original program curve.",
        H("Two signal probes force a qubit chord and a QFI bound"),
        Blocks(
            Paragraph(Text("All matrices are complex. The signal index is Fin 3 and the program index is Fin 2. G is an arbitrary canonical completely positive trace-preserving map from matrices indexed by Fin 3 times Fin 2 to matrices indexed by Fin 3. Its complete positivity includes every finite amplification. The same G is used for both signals and for every parameter.")),
            Paragraph(Text("Write B(r) for the existing blochMatrix(1,r), Bzero(r) for blochMatrix(0,r), and R(M) for the existing bloch(M). Thus B(r) has diagonal entries (1+r2)/2 and (1-r2)/2 and upper off-diagonal entry (r0-i r1)/2. These coordinates retain arbitrary complex qubit states. A density matrix is positive semidefinite with trace one; a pure density matrix is also idempotent.")),
            Describe.Lean(DescribeId.Create("actual-signal-probes"),
                DeclarationHandle.Create(Module + "signalProbe"), H("Two actual signal matrices"),
                StatementSource.FromAuthor(ProbeFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("W0 is the uniform pure signal, and W1 is the balanced pure signal on coordinates zero and two. The formula gives signalProbe at both elements of Fin 2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("two-required-outputs"),
                DeclarationHandle.Create(Module + "probeTarget"), H("The required outputs"),
                StatementSource.FromAuthor(TargetFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a and u, Yk(a,u) denotes probeTarget(a,u,k). These are the two specified signal outputs; no assertion about other signal matrices is included."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("canonical-program-output"),
                DeclarationHandle.Create(Module + "programOutput"), H("Program-to-output maps"),
                StatementSource.FromAuthor(OutputFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("L(k,M) denotes programOutput(G,k,M), regarded as a real linear map on all complex program matrices. The tensor product uses the fixed signal Wk and the input program M."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-bloch-observation"),
                DeclarationHandle.Create(Module + "jointObservation"), H("The joint real observation"),
                StatementSource.FromAuthor(ObservationFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A is jointObservation(G), a real linear map from Euclidean three-space to a pair of complex signal matrices. Both components are observations through the same processor. Let K be its kernel, Q the orthogonal complement of K, and P the orthogonal projection onto Q. P is a real orthogonal projection; no complete positivity of P is asserted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-two-probe-chord-and-qfi"),
                DeclarationHandle.Create(Module + "actual_two_probe_chord_and_qfi"),
                H("The physical affine chord, endpoint overlap, and pointwise QFI"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the statement J is the open interval (2a-1,1), r(u)=c+uv, rhoPlus=B(c+v), rhoMinus=B(c+bv), and s is the real part of tr(rhoPlus rhoMinus). Density(Wk) means PSD(Wk) and tr(Wk)=1. Every quantifier over k ranges over Fin 2. The parameter u in the global affine identities ranges over all real numbers. All chord conclusions follow from density and exactness on J, without continuity, differentiability, purity or fixed rank of the original program family.")),
                    Paragraph(Text("The final conjunction is quantified independently of the existential chord: at every u in J where the original complex matrix curve rho is differentiable over the reals, its spectralQFI is bounded below by (1-a squared)/((1-u)(1+u-2a squared)). Here deriv(rho,u) is its real derivative and hRho(u) is the positive semidefiniteness proof supplied by the density hypothesis. spectralQFI is the support-safe spectral sum: in an eigenbasis of rho, sum 2 times the squared modulus of each derivative entry divided by the sum of the corresponding eigenvalues, with zero denominators contributing zero. No constant-rank premise is needed.")),
                    Paragraph(Text("Projecting the original Bloch vectors onto Q removes the common observation kernel. Two distinct interior parameters determine c and v; the nonzero slope of the second output makes v nonzero. Orthogonal projection decreases the norm, so the line remains in the Bloch ball on J.")),
                    Paragraph(Text("For every physical point on this line, positivity of the first output tested against (1,0,-1) and (1,-2a,1) gives 2a squared minus 1 at most u at most 1. Continuity of the affine line, without any endpoint limit of the original family, forces the upper endpoint to have parameter 1 and norm one. Factoring its norm quadratic supplies the other endpoint b and the exact physical interval.")),
                    Paragraph(Text("Pulling back the second signal projector gives the real linear readout f(M)=Re tr(W1 L(1,M)). Positivity and trace preservation give values between zero and one on every density matrix. In Bloch coordinates it has the form alpha plus the inner product of z and r, with norm(z) at most alpha and alpha plus norm(z) at most one. Its value one at c+v forces z to be norm(z) times c+v. Since norm(z) is at most one half, its value at the other endpoint bounds the pure-state overlap by (1+b)/2.")),
                    Paragraph(Text("Fix an evaluation point u in J and put r=r(u). Since norm(r)<1, the vector ell=v+inner(r,v)/(1-norm(r) squared) times r is nonzero. Normalize it to n. Both r and v lie in Q, so n lies in Q. The two effects N0=B(n) and N1=B(-n) are positive semidefinite and sum to the identity. This is a physical two-outcome measurement, held fixed as the nearby parameter varies.")),
                    new DocumentBlock.DisplayFormula(MeasurementFormula()),
                    Paragraph(Text("For every nearby x in J, orthogonality gives inner(n,R(rho(x)))=inner(n,c+xv). Consequently this fixed measurement on the original curve has strictly positive probabilities at u and locally affine readouts with velocities plus and minus inner(n,v)/2. Applying actual_fisher to t mapped to rho(u+t) bounds the classical Fisher information of this measurement by spectralQFI(rho(u),deriv(rho,u),hRho(u)). No quantum-channel interpretation of the projection is used.")),
                    Paragraph(Text("The classical Fisher information is norm(v) squared plus inner(r,v) squared divided by 1-norm(r) squared. The endpoint identities turn this into (1-s)/((u-b)(1-u)). The overlap bound s at most (1+b)/2 and the endpoint bound b at least 2a squared minus 1 then give the stated QFI lower bound. This is a lower bound on the original program curve; it asserts no attainment, phase classification, or replacement exactness for signals other than the two specified probes."))),
                DescribeRole.Theorem))));

    private static Formula Seq(params Formula[] xs) =>
        F.Seq(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Sp, x }).ToArray());
    private static Formula RhoAt(Formula x) => Seq(Rho, Open, x, Close);
    private static Formula Id(string s) => F.Id(s);
    private static Formula Sub(string s, Formula i) => Seq(Id(s), Underscore, Grp(i));
    private static Formula Sq(Formula x) => Seq(Grp(x), Caret, Grp(Num(2)));
    private static Formula Fr(Formula x, int n) => Seq(Frac, Grp(x), Grp(Num(n)));
    private static Formula Fr(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Cmat(int n) => Seq(Mathbb, Grp(Id("C")), Caret, Grp(Num(n), Times, Num(n)));
    private static Formula Call(string name, params Formula[] args)
    {
        var xs = new List<Formula> { Operatorname, Grp(Id(name)), Open };
        for (int i = 0; i < args.Length; ++i)
        {
            if (i != 0) xs.AddRange([Comma, Sp]);
            xs.Add(args[i]);
        }
        xs.Add(Close);
        return Seq([.. xs]);
    }
    private static Formula Lines(params Formula[] rows)
    {
        var xs = new List<Formula> { Begin, Grp(Id("aligned")) };
        for (int i = 0; i < rows.Length; ++i)
        {
            if (i != 0) xs.Add(RowBreak);
            xs.Add(Amp);
            xs.Add(rows[i]);
        }
        xs.AddRange([End, Grp(Id("aligned"))]);
        return Disp(Seq([.. xs]));
    }
    private static Formula Mat(params Formula[] es) => Seq(Begin, Grp(Id("pmatrix")),
        es[0], Amp, es[1], Amp, es[2], RowBreak,
        es[3], Amp, es[4], Amp, es[5], RowBreak,
        es[6], Amp, es[7], Amp, es[8], End, Grp(Id("pmatrix")));
    private static Formula ProbeFormula() => Lines(
        Seq(Sub("W", Num(0)), Eq, Fr(Num(1), 3),
            Mat(Num(1), Num(1), Num(1), Num(1), Num(1), Num(1), Num(1), Num(1), Num(1))),
        Seq(Sub("W", Num(1)), Eq, Fr(Num(1), 2),
            Mat(Num(1), Num(0), Num(1), Num(0), Num(0), Num(0), Num(1), Num(0), Num(1))));
    private static Formula TargetFormula() => Lines(
        Seq(Call("Y", Num(0), Id("a"), Id("u")), Eq, Fr(Num(1), 3),
            Mat(Num(1), Id("a"), Id("u"), Id("a"), Num(1), Id("a"), Id("u"), Id("a"), Num(1))),
        Seq(Call("Y", Num(1), Id("a"), Id("u")), Eq, Fr(Num(1), 2),
            Mat(Num(1), Num(0), Id("u"), Num(0), Num(0), Num(0), Id("u"), Num(0), Num(1))));
    private static Formula OutputFormula() => Lines(
        Seq(Forall, Sp, Id("k"), InMacro, Sp, Call("Fin", Num(2)), Comma, Sp,
            Call("L", Id("k"), Id("M")), Eq,
            Call("G", Call("tensor", Sub("W", Id("k")), Id("M")))),
        Seq(Call("L", Id("k")), Colon, Cmat(2), To, Underscore, Grp(Real), Cmat(3)));
    private static Formula ObservationFormula() => Lines(
        Seq(Id("A"), Colon, Real, Caret, Num(3), To, Underscore, Grp(Real),
            Open, Cmat(3), Times, Cmat(3), Close),
        Seq(Call("A", Id("r")), Eq, Open,
            Call("L", Num(0), Call("Bzero", Id("r"))), Comma,
            Call("L", Num(1), Call("Bzero", Id("r"))), Close));
    private static Formula MeasurementFormula() => Lines(
        Seq(Id("ell"), Eq, Id("v"), Plus,
            Fr(Call("inner", Id("r"), Id("v")), Seq(Num(1), Minus, Sq(Call("norm", Id("r"))))), Id("r"),
            Comma, Sp, Id("n"), Eq, Fr(Id("ell"), Call("norm", Id("ell")))),
        Seq(Sub("N", Num(0)), Eq, Call("B", Id("n")), Comma, Sp,
            Sub("N", Num(1)), Eq, Call("B", Seq(Minus, Id("n")))),
        Seq(Sub("N", Num(0)), Ge, Num(0), Comma, Sp, Sub("N", Num(1)), Ge, Num(0), Comma, Sp,
            Sub("N", Num(0)), Plus, Sub("N", Num(1)), Eq, Id("I")));
    private static Formula ResultFormula() => Lines(
        Seq(Forall, Sp, Id("a"), InMacro, Sp, Real, Comma, Sp,
            Forall, Sp, Id("G"), InMacro, Sp, Call("CPTP", Seq(Call("Fin", Num(3)), Times, Call("Fin", Num(2))), Call("Fin", Num(3))), Comma),
        Seq(Forall, Sp, Rho, Colon, Real, To, Cmat(2), Comma, Sp, Open,
            Num(0), Lt, Id("a"), Land, Id("a"), Lt, Num(1), Land, Sp,
            Open, Forall, Sp, Id("u"), InMacro, Sp, Id("J"), Comma, Sp,
            Call("PSD", RhoAt(Id("u"))), Land, Call("tr", RhoAt(Id("u"))), Eq, Num(1), Close),
        Seq(Land, Sp, Open, Forall, Sp, Id("u"), InMacro, Sp, Id("J"), Comma, Sp, Forall, Sp, Id("k"), Comma, Sp,
            Call("L", Id("k"), RhoAt(Id("u"))), Eq, Call("Y", Id("k"), Id("a"), Id("u")), Close, Close),
        Seq(Longrightarrow, Sp, Open, Open, Forall, Sp, Id("k"), Comma, Sp, Call("Density", Sub("W", Id("k"))), Close, Land, Sp,
            Open, Exists, Sp, Id("c"), Comma, Id("v"), InMacro, Sp, Real, Caret, Num(3), Comma, Sp, Exists, Sp, Id("b"), InMacro, Sp, Real, Comma, Open),
        Seq(Id("v"), Neq, Sp, Num(0), Land, Num(2), Sq(Id("a")), Minus, Num(1), Le, Id("b"), Le,
            Num(2), Id("a"), Minus, Num(1), Land, Id("b"), Lt, Num(1), Land, Id("c"), Comma, Id("v"), InMacro, Sp, Id("Q")),
        Seq(Land, Sp, Open, Forall, Sp, Id("u"), InMacro, Sp, Id("J"), Comma, Sp,
            Call("P", Call("R", RhoAt(Id("u")))), Eq, Call("r", Id("u")), Close),
        Seq(Land, Sp, Open, Forall, Sp, Id("u"), InMacro, Sp, Real, Comma, Sp, Forall, Sp, Id("k"), Comma, Sp,
            Call("L", Id("k"), Call("B", Call("r", Id("u")))), Eq, Call("Y", Id("k"), Id("a"), Id("u")), Close),
        Seq(Land, Sp, Open, Forall, Sp, Id("u"), InMacro, Sp, Real, Comma, Sp,
            Call("norm", Call("r", Id("u"))), Le, Num(1), Iff, Id("b"), Le, Id("u"), Le, Num(1), Close),
        Seq(Land, Sp, Open, Forall, Sp, Id("u"), InMacro, Sp, Real, Comma, Sp,
            Call("PSD", Call("B", Call("r", Id("u")))), Iff, Id("b"), Le, Id("u"), Le, Num(1), Close),
        Seq(Land, Sp, Open, Forall, Sp, Id("u"), InMacro, Sp, Real, Comma, Sp,
            Call("tr", Call("B", Call("r", Id("u")))), Eq, Num(1), Close),
        Seq(Land, Sp, Open, Forall, Sp, Id("u"), InMacro, Sp, Id("J"), Comma, Sp,
            Call("norm", Call("r", Id("u"))), Lt, Num(1), Close),
        Seq(Land, Call("norm", Seq(Id("c"), Plus, Id("v"))), Eq, Num(1), Land,
            Call("norm", Seq(Id("c"), Plus, Id("b"), Id("v"))), Eq, Num(1)),
        Seq(Land, Sq(Id("rhoPlus")), Eq, Id("rhoPlus"), Land, Sq(Id("rhoMinus")), Eq, Id("rhoMinus")),
        Seq(Land, Num(0), Le, Id("s"), Le, Fr(Seq(Num(1), Plus, Id("b")), 2), Land, Id("s"), Lt, Num(1), Close, Close, Close),
        Seq(Land, Sp, Open, Forall, Sp, Id("u"), InMacro, Sp, Id("J"), Comma, Sp,
            Call("DifferentiableAt", Real, Rho, Id("u")), Longrightarrow),
        Seq(Fr(Seq(Num(1), Minus, Sq(Id("a"))),
                Seq(Open, Num(1), Minus, Id("u"), Close, Open, Num(1), Plus, Id("u"), Minus, Num(2), Sq(Id("a")), Close)),
            Le, Call("spectralQFI", RhoAt(Id("u")), Call("deriv", Rho, Id("u")), Call("hRho", Id("u"))), Close));
}
