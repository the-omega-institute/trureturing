using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class FiniteStochasticMixingDocument : IScribeDocumentDefinition
{
  private static Formula Op(string name, params Formula[] args) {
    Formula f = F.Seq(Operatorname, Grp(F.Id(name)), Open);
    for (int i=0; i<args.Length; i++) f = i==0 ? F.Seq(f,args[i]) : F.Seq(f,Comma,Sp,args[i]);
    return F.Seq(f,Close);
  }
  private static Formula All(string x, Formula type, Formula body) =>
    F.Seq(Forall,Sp,F.Id(x),Colon,type,Comma,Sp,Open,body,Close);
  private static Formula Prob(Formula x) => F.Seq(
    All("j",F.Id("S"),F.Seq(D(0),Leq,Sp,Op("eval",x,F.Id("j")))),Land,Sp,
    Op("sum",x),Eq,D(1));
  public DocumentDefinition Create() {
    var S=F.Id("S"); var P=F.Id("P"); var m=Mu; var v=Nu;
    var row=F.Seq(S,To,Sp,Mathbb,Grp(F.Id("R")));
    var stationary=F.Seq(Op("vecMul",m,P),Eq,m);
    var unique=All("v",row,F.Seq(Open,Prob(F.Id("v")),Land,Sp,
      Op("vecMul",F.Id("v"),P),Eq,F.Id("v"),Close,Implies,Sp,F.Id("v"),Eq,m));
    var limit=Op("Tendsto",Op("powers",P),Op("atTop"),Op("nhds",Op("constantRows",m)));
    var conclusion=F.Seq(Exists,Sp,m,Colon,row,Comma,Sp,Open,Prob(m),Land,Sp,
      stationary,Land,Sp,unique,Land,Sp,limit,Close);
    var statement=All("S",F.Id("Type"),F.Seq(
      OpenBracket,Op("Fintype",S),CloseBracket,
      OpenBracket,Op("DecidableEq",S),CloseBracket,
      OpenBracket,Op("Nonempty",S),CloseBracket,
      All("P",Op("Matrix",S,S,F.Seq(Mathbb,Grp(F.Id("R")))),F.Seq(
        Op("RowStochastic",P),Land,Sp,Op("IsPrimitive",P),Implies,Sp,conclusion))));
    return DocumentDefinition.Create(ScribeNode.Create(
      "Finite primitive stochastic convergence",H("Finite primitive stochastic convergence"),Blocks(
      Paragraph(Text("RowStochastic(P) means nonnegative real entries and every row summing to one; IsPrimitive(P) is Mathlib's actual positive-power predicate. powers(P) is n ↦ P^n, constantRows(mu) is (i,j) ↦ mu(j), sum is over the finite state type, and eval is function evaluation. The topology in Tendsto is the finite product topology. Thus the matrix limit entails convergence of every entry to the corresponding stationary coordinate.")),
      Describe.Lean(DescribeId.Create("primitive-convergence"),
        DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing.primitive_convergence"),
        H("Convergence to the unique stationary probability row"),StatementSource.FromAuthor(Disp(statement)),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Observer/zhang2025stochastic")),Blocks(
        Paragraph(Text("The stationary probability row exists, is nonnegative and normalized, satisfies mu*P=mu, is unique among normalized nonnegative stationary rows, and attracts every row of P^n. Nonempty is essential only for this probability-row conclusion. On an empty state type the unique matrix is zero and the power sequence is constant; no normalized row is asserted.")),
        Paragraph(Text("The source-preserving supplier uses eventual positivity, Doeblin minorization, l1 contraction on the simplex, uniqueness of a contracting fixed point, and the original geometric estimate C*rho^n for 0<rho<1. Its stationary existence step calls the original repository cesaro_stochastic, pair_cluster, stochastic_limit and cesaro_fixed declarations in NativePaidHistoryCommonRowLimits and selects a row of the stochastic fixed cluster. The return-arithmetic step calls Nat.exists_mem_closure_of_ge and Nat.setGcd machinery. No duplicate stationary, extended-gcd or Frobenius proof is retained.")),
        Paragraph(Text("The primitive bridge proves the supplier's actual return_times predicate, {n | 1<=n and 0<(P^n)(i,i)}: a positive power k and row stochasticity give positive powers k and k+1; their gcd is one. These two real return lengths witness the retained FiniteGCDOne predicate at each state. Positivity of a matrix power is not replaced by an assumed aperiodicity premise.")),
        Paragraph(Text("For the alternating two-state chain, the positive return lengths are exactly the positive multiples of two. Restricting its actual square to the phase containing the first state gives a stochastic primitive block to which this supplier applies. General closed-class decomposition, cyclic labels, first-entry phase probabilities, reducible-chain limits and arithmetic denominator bounds require further results. Phase indexing here is mathematical analysis and establishes no runtime clock or resource waiver."))),DescribeRole.Theorem))));
  }
}
