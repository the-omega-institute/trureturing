using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class FiniteGenuinePeriodsDocument : IScribeDocumentDefinition
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
        All("C",Op("ClosedClass",P),Op("Nonempty",Op("ClassPeriods",P,C)))))));
    return DocumentDefinition.Create(ScribeNode.Create("FiniteGenuinePeriods",
      H("Genuine return periods and cyclic labels"),Blocks(
      Paragraph(Text("RowStochastic(P) means an arbitrary finite real matrix with nonnegative entries and row sums one. ClosedClass(P) is the actual terminal communicating-class interface. A is restriction(P,C), and returns(A,x) is the set of natural n with n>0 and (A^n)(x,x)>0. period(A,x) is Nat.setGcd of precisely this set; it is not a supplied period or a least-witness proxy. Actual class power entries agree with ambient P powers, so these are exactly the original chain positive return times.")),
      Describe.Lean(DescribeId.Create("actual-periods"),
        DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteGenuinePeriods.actual_periods"),
        H("Genuine return periods and cyclic labels"),StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(),Blocks(
        Paragraph(Text("ClassPeriods(P,C) chooses a state b in C and sets p=period(A,b). Its fields assert p>0; period(A,x)=p for every x in C; and p<=card(C). Its phase map phi:C->ZMod(p) is surjective. Every positive one-step transition satisfies phi(x)+1=phi(y). For every natural n and all x,y in C, positivity of the ambient P^n entry implies phi(x)+n=phi(y). For each x,y there is a threshold N such that every n>=N satisfying this residue equality has a strictly positive ambient P^n entry.")),
        Paragraph(Text("To transport the gcd from x to y, concatenate a positive x-to-y path, a return at y, and a positive y-to-x path. Subtract the common concatenation length using divisibility; exchange x and y. Positive return existence proves the gcd nonzero. Labels are residues of actual positive path lengths from b. Appending the same positive return path proves independence of the selected length, including the base label zero.")),
        Paragraph(Text("Every power of a stochastic matrix has a positive entry in each row. Starting from b at each natural time produces every residue, proving surjectivity. The cardinality of ZMod(p) is p, giving the period bound. Return-length concatenation makes every element of their additive closure an actual positive return. Nat.exists_mem_closure_of_ge supplies all sufficiently large multiples of the genuine gcd. Appending one fixed positive x-to-y path proves eventual positivity for the allowed residues.")),
        Paragraph(Text("The theorem has no nonempty ambient premise. An actual class itself supplies its base state. Empty ambient state spaces have no actual classes, and no normalized probability row is asserted on an empty state type. Phase indices are mathematical analysis and grant no installed clock or runtime resource waiver."))),DescribeRole.Theorem))));
  }
}
