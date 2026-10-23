using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class FiniteCyclicBlocksDocument : IScribeDocumentDefinition
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
        All("C",Op("ClosedClass",P),F.Seq(Exists,Sp,K,Colon,Op("ClassPeriods",P,C),Comma,Sp,Op("Blocks",K)))))));
    return DocumentDefinition.Create(ScribeNode.Create("FiniteCyclicBlocks",
      H("Actual primitive cyclic blocks"),Blocks(
      Paragraph(Text("ClosedClass(P) denotes the actual closed class of the original finite real row-stochastic matrix. ClassPeriods(P,C) carries its genuine positive return-time gcd p and the surjective cyclic map phi. Phase(K,j) is the subtype of states in C whose label equals j. block(K,j) is the actual restriction of A^p to this subtype, where A=restriction(P,C). It uses Subtype.val in both coordinates.")),
      Describe.Lean(DescribeId.Create("actual-blocks"),
        DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteCyclicBlocks.actual_blocks"),
        H("Actual primitive cyclic blocks"),StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(),Blocks(
        Paragraph(Text("Blocks(K) asserts for every j that Phase(K,j) is nonempty, block(K,j) is row stochastic and Matrix.IsPrimitive, and for every n and x,y in Phase(K,j), (block(K,j)^n)(x,y)=(P^(p*n))(x,y) using both original state projections. For every distinct actual closed class D, every natural n, x in D and y in C, the ambient (P^n)(x,y) is zero.")),
        Paragraph(Text("The residue law forces every p-step transition to stay in its phase. Summing the actual stochastic A^p row over that phase therefore preserves the row sum one. The same zero entries justify each multiplication of restricted blocks and yield their exact ambient power identity. Finite uniformization of the proved eventual allowed-residue positivity gives a strictly positive power of each actual phase block. No primitivity certificate or chosen partition is a premise.")),
        Paragraph(Text("Distinct-class zero entries use the actual disjointness and no-exit fields of FiniteClosedClasses.actual_structure. The period and the matrix restriction come from the original P throughout. These blocks supply the primitive mixing theorem for actual closed-class limits. Transient entry-time convolution and the simultaneous rational denominator remain separate assertions."))),DescribeRole.Theorem))));
  }
}
