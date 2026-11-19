using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSInteriorTransversalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every pair of positive exterior lengths has the same actual fixed-sector interior zero with positive definite target environments and an invertible ordinary real derivative.",
        H("An all-length actual real transversality witness"), Blocks(
            Definition("fixedSector", "The fixed sector", "The native Sector is (lambda,mu,a)=(2,0,1), with original parameter z0=1. Thus B=diag(2,0) and G(1) has rows (1,1) and (1,-1)."),
            Definition("leftBoundary", "The actual left boundary", "The original finite left row is l=(1,1)."),
            Definition("rightBoundary", "The actual right boundary", "The original finite right column is r=(1,I)."),
            Describe.Lean(DescribeId.Create("interior-transversality-witness"),
                DeclarationHandle.Create(Module + ".interior_q2_fixed_target_witness"),
                H("The integrated universal witness"),
                StatementSource.FromAuthor(Disp(Endpoint())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every p,q at least one, both native actual targets are positive definite, both trial matrices recover the original rank-one boundary Grams at 1, and the native residual vanishes there. There exist real L,C,R, a continuous real linear equivalence e and integers u,v satisfying the displayed triangular derivative, determinant, scaling and nonzero mod-5 certificates. The only inputs are p,q and their positivity proofs. All targets are fixed outside the trial-parameter lambda.")),
                    Paragraph(Text("Write W=G(1), E=transfer(core(1)), S=dualTransfer(core(1)). The first left target is [[8,4],[4,4]] and E(rr dagger)=[[10,2I],[-2I,2]], both with determinant 16. Kraus congruences give positive semidefiniteness, their nonzero determinants give positive definiteness, and the invertible W congruence plus a positive semidefinite summand preserves strict positivity under every subsequent iterate. G(1)^2=2I, so the actual right target is 4 times E iterated q on rr dagger.")),
                    Paragraph(Text("The proof reuses the native inverseTransfer, inverseDualTransfer, trialLeft, trialRight and residual. At nonzero z the explicit native G inverse has rows (1/2,1/2) and (z inverse/2,-z inverse/2). Joint real derivatives on the pair (z,X) are established before composing with a varying inverse iterate. Conjugation is differentiated as a real linear map. The central inverse-square sandwich uses two product rules, retaining the derivative of each G inverse factor. The parameter-dependent iterates are proved by induction with fixed original targets, without the fixed-point iterate theorem.")),
                    Paragraph(Text("In Hermitian coordinates h(s,d,u,v)=[[ (s+d)/2,(u+Iv)/2 ],[ (u-Iv)/2,(s-d)/2 ]], the determinant is (s squared-d squared-u squared-v squared)/4. Its differentials at the left and right rank-one Grams are delta s-delta u and delta s+delta v. The resulting real derivative is triangular: w maps to L Re(w)+I(C Re(w)+R Im(w)). The left angular entry is zero; C retains the full radial contribution of the right trial matrix.")),
                    Paragraph(Text("OpenBoundaryMPSInteriorTransversalityCertificate supplies the division-free integer recurrences and their nonzero mod-5 product certificate. The recurrences used on the live proof path are a0=(1,0,-1), b0=(1,0,1), x0=(0,1,0), y0=(1,0,0). Set a'=(3a0-2a1,5a2,-2a0+3a1), b'=(3b0+2b1,b2,2b0+3b1), x'=(3x0-2x1,5x2,-2x0+3x1), y'=(3y0+2y2,2y0+3y2,y1). With t(n)=a(n)0 b(n)1+a(n)1 b(n)0, set U0=V0=0, U(n+1)=5Un+2t(n+1), and V(n+1)=5Vn+2(-1)^(n+2)(x(n+1)0+5^(n+1)y(n+2)2). Coordinate inverse-power induction and finite-sum induction prove U(p)=5^p L and V(q)=5^q R after integer-to-real casts.")),
                    Paragraph(Text("Over ZMod 5, induction gives a(n+1)=3^(n+1)(1,0,1), b(n+1)=2^n(3,1,2), and x(n+1)=3^(n+1)(1,0,1). Therefore U(p)=1 and V(q)=2(-1)^(q+1)3^q for every positive p,q. Their nonzero residues imply nonzero integer and real values, hence L and R are nonzero. This certificate is consumed to build e with inverse w maps to Re(w)/L+I((Im(w)-C Re(w)/L)/R). No rational-to-finite-field homomorphism or bounded experiment supplies this inference.")),
                    Paragraph(Text("This closes the explicit derivative premise at one actual all-length witness for the conditional root-to-actual unit. It does not prove the annular boundary signs, endpoint operator limits, polynomial clearance, finite-chart descent, genericity or full C9, and adds zero solved-open-problem credit. The Critch-Morton problem and Ma-Zhang C8 attribution remain as in the owning library note. No normalization, positive physical inverse, clock, dynamics, energy or thermodynamic conclusion is asserted."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("interior-transversality-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Endpoint()
    {
        var p = Id("p"); var q = Id("q"); var w = Id("w");
        var L = Id("L"); var C = Id("C"); var R = Id("R");
        var e = Id("e"); var u = Id("u"); var v = Id("v");
        var s = Id("fixedSector"); var l = Id("leftBoundary"); var r = Id("rightBoundary");
        var P = Call("leftTarget", s, D(1), l, p);
        var Henv = Call("rightTarget", s, D(1), r, q);
        var f = Call("residual", s, p, q, P, Henv);
        var J = Seq(Begin,Grp(Id("pmatrix")),L,Amp,D(0),RowBreak,C,Amp,R,End,Grp(Id("pmatrix")));
        var cert = And(
            All("w", Id("Complex"), Eq(new Formula.Apply(e,[w]),
                Add(Mul(L,Call("re",w)),Mul(Id("I"),Add(Mul(C,Call("re",w)),Mul(R,Call("im",w))))))),
            Call("HasFDerivAt", f, Call("toContinuousLinearMap",e), D(1)),
            Eq(Call("det",J),Mul(L,R)), Ne(Mul(L,R),D(0)),
            Eq(Mul(Pow(D(5),p),L),Call("ofInt",u)),
            Eq(Mul(Pow(D(5),q),R),Call("ofInt",v)),
            Eq(Mul(Pow(D(5),Add(p,q)),Mul(L,R)),Call("ofInt",Mul(u,v))),
            Eq(Call("intCastZMod5",Mul(u,v)),Mul(Mul(D(2),Pow(new Formula.Negate(D(1)),Add(q,D(1)))),Pow(D(3),q))));
        var result = And(Call("PosDef",P),Call("PosDef",Henv),
            Eq(Call("trialLeft",s,p,P,D(1)),Call("vecMulVec",Call("star",l),l)),
            Eq(Call("trialRight",s,q,Henv,D(1)),Call("vecMulVec",r,Call("star",r))),
            Eq(new Formula.Apply(f,[D(1)]),D(0)),
            Some("L",Id("Real"),Some("C",Id("Real"),Some("R",Id("Real"),
            Some("e",Call("ContinuousLinearEquiv",Id("Real"),Id("Complex"),Id("Complex")),
            Some("u",Id("Int"),Some("v",Id("Int"),cert)))))));
        return All("p",Id("Nat"),All("q",Id("Nat"),
            Imp(And(Le(D(1),p),Le(D(1),q)),result)));
    }
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s),[..xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s),t,b);
    private static Formula Some(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s),t,b);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b) => new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a, Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a),b);
}
