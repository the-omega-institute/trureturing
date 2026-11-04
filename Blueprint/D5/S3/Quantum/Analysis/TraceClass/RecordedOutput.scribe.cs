using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class RecordedOutputDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace-class terminal and continuous-record outputs with an exact norming positive decomposition.",
        H("Fixed-block recorded quantum outputs"), Blocks(
            Paragraph(Text("Let H and K be arbitrary complete complex Hilbert spaces, X any measurable space with measure mu, and I a finite mode type. Output is WithLp 1 of TraceClass H times PiLp 1 of the I-indexed Bochner L1(X,mu;TraceClass K) spaces. Its norm is the terminal trace norm plus the sum of the integrated trace norms of the exact record densities. Positivity means operator positivity of the terminal block and almost-everywhere operator positivity of every record block. No separability, countability of the record space, finite-dimensional reference or finite-rank condition is imposed.")),
            Paragraph(Text("traceMass is the continuous real part of the trace pairing with the identity, using the genuine trace-class Banach norm. mass is the continuous real-linear sum of terminal traceMass and each record projection composed with the Bochner integral and traceMass. It equals terminal traceMass plus the integrals of the record traceMass. Positive outputs have norm equal to mass. pack uses Integrable.toL1, so record densities are genuine Bochner-integrable trace-class-valued functions rather than formal pointwise expressions.")),
            Entry("positive-norm", "norm_eq_mass", "The positive cq norm is total trace mass", PositiveNorm(),
                "For every positive q in Output(H,K,I,mu), norm(q)=mass(q). On the terminal and almost every record block, the genuine positive trace norm equals real trace. The WithLp 1 product norm, PiLp 1 finite-mode norm and Bochner L1 norm add exactly these positive masses. This equality supplies the norm law needed by an actual cq target and by both norming parts."),
            Entry("fixed-block-decomposition", "fixed_block_decomposition", "Exact norming positive decomposition", Decomposition(),
                "For self-adjoint trace-class s, positive fixed trace-class blocks A_i, and arbitrary real integrable coefficients h_i, let q=pack(s,(t maps to h_i(t) A_i)). There are positive P,N in the same complete cq carrier with q=P-N and mass(P)+mass(N)=norm(q). The success parts are the existing CFC positive and negative parts, using the original trace-class membership lemmas. Their norm sum is the trace norm of s by the common Hilbert-basis diagonal formula and the CFC identity s-positive+s-negative=abs(s). The record parts are max(h_i,0) A_i and max(-h_i,0) A_i. Scalar positive/negative part integrability and constant scalar multiplication prove their Bochner integrability; the sum of their integrated norms is exactly integral |h_i| norm(A_i). This constructs only the decomposition needed for common fixed positive record blocks. It makes no global operator-valued Jordan measurability or trace-norm Lipschitz assertion."),
            Entry("fixed-block-contraction", "fixed_block_contracts", "Positive mass-nonincreasing joint actions", Contraction(),
                "For any real seminormed target W, target positivity D and real mass v satisfying norm(w)=v(w) on D, let Phi be one real-linear map from this actual cq carrier into W. Suppose every positive q is mapped into D and v(Phi q)<=mass(q). Then norm(Phi(pack(s,h_i A_i)))<=norm(pack(s,h_i A_i)). Apply the exact norming decomposition before Phi, use real linearity and the triangle inequality, identify both positive target norms with their masses, and apply mass nonincrease to both norming parts. Contraction on these differences is derived from these laws; no operator norm bound is a map hypothesis. Mass preservation is a special case. The statement concerns unnormalized outputs; it asserts no normalized-postselection estimate, execution semantics or access permission."))));
    private static DocumentBlock Entry(string id,string declaration,string title,Formula formula,string text) =>
        Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/RecordedOutput."+declaration),
            H(title),StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    private static Formula I(string s)=>F.Id(s);
    private static Formula C(string n,params Formula[] xs)=>new Formula.Apply(I(n),[..xs]);
    private static Formula E(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula L(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula A(Formula x,Formula y)=>new Formula.Logic(x,FormulaLogicOperator.And,y);
    private static Formula P(Formula x,Formula y)=>new Formula.Logic(x,FormulaLogicOperator.Implies,y);
    private static Formula.BoundVariable V(string n,string t)=>new(FormulaIdentifier.Create(n),I(t));
    private static Formula Q(Formula body,params Formula.BoundVariable[] vs)=>new Formula.BindMany(FormulaQuantifier.ForAll,[..vs],body);
    private static Formula PositiveNorm()=>Q(P(C("Positive",I("q")),E(C("norm",I("q")),C("mass",I("q")))),
        V("H","CompleteComplexHilbertSpace"),V("K","CompleteComplexHilbertSpace"),V("X","MeasurableSpace"),V("mu","MeasureX"),V("I","FiniteType"),V("q","Output"));
    private static Formula Decomposition()
    {
        Formula s=I("s"),h=I("h"),a=I("A"),mu=I("mu"),p=I("P"),n=I("N"),q=C("pack",mu,s,C("scalarFixedBlocks",h,a));
        return Q(P(A(C("SelfAdjoint",s),A(C("AllPositive",a),C("AllIntegrable",h,mu))),
            new Formula.BindMany(FormulaQuantifier.Exists,[V("P","Output"),V("N","Output")],
                A(C("Positive",p),A(C("Positive",n),A(E(q,C("subtract",p,n)),
                    E(C("add",C("mass",p),C("mass",n)),C("norm",q))))))),
            V("H","CompleteComplexHilbertSpace"),V("K","CompleteComplexHilbertSpace"),V("X","MeasurableSpace"),V("mu","MeasureX"),V("I","FiniteType"),V("s","TraceClassH"),V("A","ModeTraceClassK"),V("h","ModeRecordRealFunction"));
    }
    private static Formula Contraction()
    {
        Formula q=C("pack",I("mu"),I("s"),C("scalarFixedBlocks",I("h"),I("A")));
        return Q(P(A(C("FixedBlockHypotheses",I("mu"),I("s"),I("A"),I("h")),
            A(C("PositiveTargetNormEqualsMass",I("D"),I("v")),C("PositiveMassNonincreasingRealLinear",I("Phi"),I("D"),I("v")))),
            L(C("norm",C("apply",I("Phi"),q)),C("norm",q))),
            V("H","CompleteComplexHilbertSpace"),V("K","CompleteComplexHilbertSpace"),V("X","MeasurableSpace"),V("mu","MeasureX"),V("I","FiniteType"),V("s","TraceClassH"),V("A","ModeTraceClassK"),V("h","ModeRecordRealFunction"),V("W","RealSeminormedSpace"),V("D","TargetPositivePredicate"),V("v","TargetMassFunction"),V("Phi","RealLinearMap"));
    }
}
