using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class FiniteClosedClassLimitsDocument : IScribeDocumentDefinition
{
  private static Formula Op(string name, params Formula[] args) {
    Formula f = F.Seq(Operatorname, Grp(F.Id(name)), Open);
    for (int i=0; i<args.Length; i++) f = i==0 ? F.Seq(f,args[i]) : F.Seq(f,Comma,Sp,args[i]);
    return F.Seq(f,Close);
  }
  private static Formula All(string x, Formula type, Formula body) =>
    F.Seq(Forall,Sp,F.Id(x),Colon,type,Comma,Sp,Open,body,Close);
  public DocumentDefinition Create() {
    var X=F.Id("X"); var P=F.Id("P"); var C=F.Id("C"); var K=F.Id("K");
    var formula=All("X",F.Id("Type"),F.Seq(
      OpenBracket,Op("Fintype",X),CloseBracket,
      OpenBracket,Op("DecidableEq",X),CloseBracket,
      All("P",Op("Matrix",X,X,F.Seq(Mathbb,Grp(F.Id("R")))),F.Seq(
        Op("RowStochastic",P),Implies,Sp,
        All("C",Op("ClosedClass",P),F.Seq(Exists,Sp,K,Colon,Op("ClassPeriods",P,C),Comma,Sp,Op("Blocks",K),Land,Sp,Op("Nonempty",Op("ClassLimit",K))))))));
    return DocumentDefinition.Create(ScribeNode.Create("FiniteClosedClassLimits",
      H("Closed-class stationary rows and periodic limits"),Blocks(
      Paragraph(Text("For every actual closed class C of an arbitrary finite real row-stochastic matrix P, the theorem constructs its genuine period data K, proves Blocks(K), and supplies ClassLimit(K). Put A=restriction(P,C), p=period(A,K.base) and phi=K.phase. The stationaryRow pi:C->Real is nonnegative, sums to one and satisfies pi vecMul A=pi. It is the unique row with these three properties, and pi(y)>0 for every y in C.")),
      Describe.Lean(DescribeId.Create("actual-limits"),
        DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClassLimits.actual_limits"),
        H("Closed-class stationary rows and periodic limits"),StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(),Blocks(
        Paragraph(Text("For every j in ZMod(p), the sum of pi(y) over the actual phase phi(y)=j is 1/p. For every positive natural d with p dividing d, every natural i, and all starts x and targets y in C, the actual ambient (P^(d*n+i))(x,y) tends as n tends to infinity to p*pi(y) if phi(x)+i=phi(y), and to zero otherwise. No restriction i<d or minimality of d is present. Blocks(K) additionally gives identically zero contributions from starts in distinct actual closed classes.")),
        Paragraph(Text("Stationary existence directly uses FiniteStochasticMixing.stationary_distribution_exists, whose original Cesaro argument consumes the existing native stationary suppliers. Its original multi_step_stationary propagates stationarity to all powers. Each positive return class is nonempty, so this application asserts no normalized row on an empty state type. Positive mass at one state and an actual positive path to any target, combined with power stationarity, prove strict positivity.")),
        Paragraph(Text("The exact phase-row sum is one precisely for the allowed residue and zero otherwise. Applying the stationary equation moves each phase mass to the next phase. Surjective cyclic labels and normalization give equal masses 1/p. Consequently p*pi restricted to each phase is a stationary probability row of its actual p-step block. FiniteStochasticMixing.primitive_convergence on the proved blocks identifies this row, proves phase convergence and yields uniqueness of the original class row.")),
        Paragraph(Text("Write d=p*q with q>0. The identity P^(d*n+i)=P^i P^(p*q*n), restricted to C, expresses each entry as a finite sum over the target phase. Actual block powers give the second factor; primitive convergence along q*n gives p*pi(y). The first factor sums to one or zero by the exact phase-row law, proving the stated ambient limit for every natural i.")),
        Paragraph(Text("These assertions supply the genuine-period, stationary-row and recurrent-start inputs to PH38.2. They do not assert transient-start first-entry convolution, lifted-chain absorption probabilities, a simultaneous arithmetic denominator or its cardinality bound. No denominator depending on d, escape times or minimum positive transitions is introduced. Phase indices are used only for mathematical analysis and establish no clock or installation-cost waiver."))),DescribeRole.Theorem))));
  }
}
