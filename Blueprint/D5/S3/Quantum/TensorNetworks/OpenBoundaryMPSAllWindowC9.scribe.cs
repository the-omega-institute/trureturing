using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSAllWindowC9Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw all-window recovery and individual-window ambiguity on the actual MPS image", H("All adjacent windows on the actual MPS image"), Blocks(
            Describe.Lean(DescribeId.Create("openboundarymps-all-window-c9-result"),
                DeclarationHandle.Create(Module + ".result"), H("One common full-amplitude principal locus"),
                StatementSource.FromAuthor(Disp(ResultFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("In the displayed formula FullPrincipalLocus(m,P) denotes exactly {psi in openBoundaryMPS(3+m) | eval(realCoordinates(psi),P) is nonzero}, mk is the subtype constructor, and amplitudes use their underlying functions. For every natural m, N=3+m, there is one nonzero real polynomial P in ALL real and imaginary amplitude coordinates Word(N) plus Word(N). Its nonvanishing locus G in the ENTIRE literal actual openBoundaryMPS(N) image is nonempty, relatively Euclidean open and dense, and U(1) saturated. Every target in G is nonzero. For EVERY natural p,q with p+q=m and EVERY exact length equality h, equality of that ONE complete raw three-site interior with ANY actual competitor is equivalent to a unit-phase relation. For EVERY p+q=m+1 and h there is a nonzero actual nonphase competitor with the same complete raw two-site window. For EVERY p+q=m+2 and h the same assertion holds for the one-site window. Competitors can depend on the window and have no regularity, chart or genericity premise. No collection of jointly observed windows is assumed.")),
                    Paragraph(Text("Write L_R=actualPrincipalLocus(m,R), O=observedPolynomial, and let B be supplied by intrinsic_actual_q2_fiber. T is the intrinsic_interior_recovery polynomial when m>=2 and 1 otherwise; A is the observed_interior_ambiguity polynomial when m>=1 and 1 otherwise. If H is actual-state reversal, G=L_O intersect L_B intersect L_T intersect L_A intersect H inverse(L_O) intersect H inverse(L_B). H is an involutive homeomorphism: reversing the physical word transposes each original core by ORDINARY transpose and swaps the original boundary vectors. No conjugation is used. The finite intersection is dense and open, and has one common ACTUAL witness by successive dense-open intersection. Continuity alone is not used to infer density of a preimage.")),
                    Paragraph(Text("For every observed real polynomial R, lift(R) substitutes the COMPLETE Q3 real and imaginary Gram-coordinate polynomials, summing over every exterior word. Its evaluation at any amplitude is exactly R evaluated on the complete raw prefix Q3. Put L=O B T A and R=O B. The literal full-state polynomial is lift(L) times rename(tau,lift(R)), where tau reverses each real and imaginary word coordinate. Evaluation identifies its nonvanishing locus with G. Evaluation at the same common actual witness proves P nonzero; separate witnesses for its factors would not suffice. Public locus_phase and actual_phase give exactly U(1) saturation, without radial invariance.")),
                    Paragraph(Text("The original prefix recovery supplies the left Q3. Right recovery reverses the target and arbitrary competitor, applies prefix recovery there, and reverses the phase equation. Strict interior recovery uses intrinsic_interior_recovery unchanged. The original prefix-Q2 fiber is reduced definitionally through its public proposition. Its every-neighborhood clause is specialized to the open NONZERO neighborhood of the explicitly nonzero target. Reversal transports that same actual nonzero nonphase witness at the right boundary. The interior two-site supplier already retains all three properties. Two exact adjacent-pair partial-trace identities, with full exterior bijections and value-preserving length casts, give each one-site witness from a containing pair; they preserve the chosen competitor.")),
                    Paragraph(Text("At m=0 (N=3), only the whole-chain Q3 and the two boundary Q2 windows occur, and T=A=1. At m=1 (N=4), both Q3 windows are boundary windows, T=1 and A handles the one internal pair. At m>=2 both internal suppliers apply. Positivity of both exterior lengths forces these thresholds; no supplier is called out of range. Every equality proof h is retained in the result telescope. Word(0) is summed as a singleton, never dropped as an empty exterior.")),
                    Paragraph(Text("Critch and Morton, SIGMA 10 (2014), 095, Conjecture 9, provide the original assertion and raw displayed partial trace. This result is a sufficient strengthening of the raw N>=4 prefix recovery and no-fewer formulation to every N>=3 and every placement. N>=3 and the specific real-principal genericity convention are the formal strengthening, not quoted author wording. The reused suppliers include the Ma--Zhang C8 contribution with its license. Word reversal uses GVHunter.reverse_word_list. Within the bounded accessible literature examined, no exact C9 settlement was identified; this does not establish priority or uniqueness.")),
                    Paragraph(Text("Unit-phase saturation of this raw locus alone does not justify a dense normalized slice. OpenBoundaryMPSNormalizedC9.result supplies a separately proved dense physical-mass-one slice with both target and competitors normalized for the same physical C9 reading. This result makes no closure-only, exceptional-target, jointly known marginal, stability, dynamics, energy or thermodynamic claim."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("critch-morton-2014-open-boundary-mps-raw-c9"), ResolutionKind.Proved,
                    [DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.result")])))));

    private static Formula ResultFormula()
    {
        var m=Id("m"); var p=Id("p"); var q=Id("q"); var h=Id("h");
        var psi=Id("psi"); var phi=Id("phi"); var z=Id("z"); var poly=Id("P");
        var n=Add(D(3),m); var actual=Call("openBoundaryMPS",n);
        var word=Call("Word",n); var indices=Call("Sum",word,word);
        var locus=Call("FullPrincipalLocus",m,poly);
        var phase=Some("z",Id("Complex"),And(Eq(Call("norm",z),D(1)),Eq(phi,Call("smul",z,psi))));
        Formula Obs(byte k, Formula f) => Call("rawInterior",p,D(k),q,Call("castState",h,f));
        Formula Witness(byte k) => Some("phi",actual,And(Ne(phi,D(0)),Eq(Obs(k,phi),Obs(k,psi)),Negate(phase)));
        Formula Window(byte k, Formula sum, Formula body) => All("p",Id("Nat"),All("q",Id("Nat"),
            Imp(Eq(Add(p,q),sum),All("h",Eq(Add(Add(p,D(k)),q),n),body))));
        var recovery=Window(3,m,All("phi",actual,Iff(Eq(Obs(3,phi),Obs(3,psi)),phase)));
        var pairs=Window(2,Add(m,D(1)),Witness(2));
        var sites=Window(1,Add(m,D(2)),Witness(1));
        var saturation=All("psi",actual,All("z",Id("Complex"),Imp(Eq(Call("norm",z),D(1)),
            Some("hz",Call("Member",Call("smul",z,psi),actual),
                Iff(Call("Member",Call("mk",Call("smul",z,psi),Id("hz")),locus),Call("Member",psi,locus))))));
        return All("m",Id("Nat"),Some("P",Call("MvPolynomial",indices,Id("Real")),
            And(Ne(poly,D(0)),Call("Nonempty",locus),Call("IsOpen",locus),Call("Dense",locus),saturation,
                All("psi",actual,Imp(Call("Member",psi,locus),And(Ne(psi,D(0)),recovery,pairs,sites))))));
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
