using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSNormalizedC9Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical-mass normalization of the raw all-window supplier, with a literal polynomial certificate on full amplitude coordinates and individual mass-one ambiguity witnesses.",
        H("Physical-mass-one all-window reconstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("normalized-c9-physical-mass"),
                DeclarationHandle.Create(Module + ".physicalMass"), H("Physical squared Hilbert mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite chain, M(psi) is the sum over every binary word w of Complex.normSq(psi(w)). It is nonnegative, vanishes exactly at the zero amplitude, is continuous, and obeys M(z psi)=normSq(z) M(psi). In particular a real amplitude multiplier t has mass degree two. The default Pi sup norm is not used."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-c9-mass-one"),
                DeclarationHandle.Create(Module + ".MassOne"), H("The actual physical mass-one subtype"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("MassOne N is the subtype of the literal openBoundaryMPS N image with physicalMass=1. Its topology is the induced topology on that subtype, not a topology on a closure or parameter space. Every inhabitant is nonzero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-c9-result"),
                DeclarationHandle.Create(Module + ".result"), H("One polynomial locus for every individual window"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("In the displayed formula HomogeneousComponentSOS(P) means exactly the finite sum of (homogeneousComponent d P)^2 for d=0 through totalDegree P inclusive. MassOnePrincipalLocus(m,H) means exactly {psi in MassOne(3+m) | eval(realCoordinates(amplitude(psi)),H) is nonzero}, with its induced subtype topology. amplitude(psi) is the underlying function Word(3+m) -> Complex, forgetting both subtype proofs. For every natural m, N=3+m, including m=0, there are literal real polynomials P,H on Word N plus Word N, the independent real and imaginary amplitude coordinates. P is the polynomial supplied directly by OpenBoundaryMPSAllWindowC9.result. H=HomogeneousComponentSOS(P). Both polynomials are nonzero. This exact nonvanishing locus of H on MassOne N is nonempty, relatively open, dense and saturated under every complex scalar of norm one.")),
                    Paragraph(Text("At each target in this same locus, every p,q with p+q=m and every exact equality h:(p+3)+q=N give recovery from rawInterior p 3 q against every actual mass-one competitor, exactly up to one unit phase. For each p+q=m+1, and every exact h:(p+2)+q=N, an actual mass-one competitor has the same individual two-site observation and is not a phase multiple. The corresponding assertion holds separately for every one-site window with p+q=m+2. The existential competitor follows the choice of window; no single competitor shared by windows is asserted.")),
                    Paragraph(Text("The polynomial argument works for an arbitrary real multivariate P without assuming homogeneity, a nonempty variable carrier, positive total degree, or a nonzero input x. The finite homogeneous reconstruction gives the univariate polynomial F_x(T)=sum_d eval_x(P_d) T^d. A coefficient extraction and the real sum-of-squares criterion identify H(x)=0 with F_x=0. The univariate infinite-root theorem then gives H(x) nonzero exactly when P(t x) is nonzero for some positive real t. P=0, constants, an empty variable carrier and x=0 remain in the statement. The scalar t multiplies amplitudes, so raw densities scale by t^2.")),
                    Paragraph(Text("The old P locus is contained in the H locus by t=1, so its density and nonemptiness pass to the saturation. Positive-ray invariance follows from the ray characterization and reciprocal scaling. Unit-phase saturation follows from the old raw phase saturation, commuting phase with positive real scaling. H itself need not be homogeneous. A continuous retraction from the positive-mass actual subtype sends psi to psi/sqrt(M(psi)); it fixes MassOne N. The positive-mass subtype is open. Pulling a nonempty open slice set back through this retraction and using density in that open subtype proves density on the actual mass-one slice. Continuity alone is never used to claim that an arbitrary image is open or dense.")),
                    Paragraph(Text("For all p,k,q, rawInterior has scalar degree two. Its trace is the complex embedding of M(psi), proved by the exact bijection between (window word,left word,right word) and the original full word. Length casts preserve mass and commute with scalar action. Equal same-window observations therefore give equal physical masses, at boundaries and with zero-length exteriors as well as internally. For a normalized target choose t>0 reaching the old P locus. Apply raw all-window recovery and ambiguity there. Scale every raw ambiguity witness back by inverse t: trace equality places that very witness on the same mass-one slice, equality of observations survives, and a hypothetical phase equation would contradict the raw nonphase witness. Recovery scales each arbitrary actual mass-one competitor by t and cancels the same nonzero scalar.")),
                    Paragraph(Text("Continuity of realCoordinates from OpenBoundaryMPSDensityGenericity and the actual_phase scalar-closure property supply the normalization maps and phase action. The reconstruction and gauge results include Haobo Ma and Wenlin Zhang's Conjecture 8 supplier under CC BY 4.0. Together with OpenBoundaryMPSAllWindowC9.result, this establishes the physical-mass-one slice with both target and competitors normalized for the same physical C9 reading. It does not establish independent C9 novelty or priority.")),
                    Paragraph(Text("This theorem supplies neither a joint-window ambiguity witness, a neighborhood ambiguity upgrade, stability, physical recovery dynamics, a time group, energy, clock nor thermodynamics."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var m=Id("m"); var p=Id("p"); var q=Id("q"); var h=Id("h");
        var psi=Id("psi"); var phi=Id("phi"); var z=Id("z"); var poly=Id("P"); var Hpoly=Id("H");
        var n=Add(D(3),m); var actual=Call("MassOne",n);
        var word=Call("Word",n); var indices=Call("Sum",word,word);
        var locus=Call("MassOnePrincipalLocus",m,Hpoly);
        var phase=Some("z",Id("Complex"),And(Eq(Call("norm",z),D(1)),Eq(Call("amplitude",phi),Call("smul",z,Call("amplitude",psi)))));
        Formula Obs(byte k, Formula f) => Call("rawInterior",p,D(k),q,Call("castState",h,Call("amplitude",f)));
        Formula Witness(byte k) => Some("phi",actual,And(Eq(Obs(k,phi),Obs(k,psi)),Negate(phase)));
        Formula Window(byte k, Formula sum, Formula body) => All("p",Id("Nat"),All("q",Id("Nat"),
            Imp(Eq(Add(p,q),sum),All("h",Eq(Add(Add(p,D(k)),q),n),body))));
        var recovery=Window(3,m,All("phi",actual,Iff(Eq(Obs(3,phi),Obs(3,psi)),phase)));
        var pairs=Window(2,Add(m,D(1)),Witness(2));
        var sites=Window(1,Add(m,D(2)),Witness(1));
        var saturation=All("psi",actual,All("z",Id("Complex"),Imp(Eq(Call("norm",z),D(1)),
            Some("phi",actual,And(Eq(Call("amplitude",phi),Call("smul",z,Call("amplitude",psi))),
                Iff(Call("Member",phi,locus),Call("Member",psi,locus)))))));
        return All("m",Id("Nat"),Some("P",Call("MvPolynomial",indices,Id("Real")),
            Some("H",Call("MvPolynomial",indices,Id("Real")),
            And(Ne(poly,D(0)),Eq(Hpoly,Call("HomogeneousComponentSOS",poly)),Ne(Hpoly,D(0)),
                Call("Nonempty",locus),Call("IsOpen",locus),Call("Dense",locus),saturation,
                All("psi",actual,Imp(Call("Member",psi,locus),And(recovery,pairs,sites)))))));
    }
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s),[.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Some(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b)=>new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b)));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Implies,Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Iff,Par(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a, Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula Negate(Formula a) => Seq(Neg,Sp,Par(a));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
}
