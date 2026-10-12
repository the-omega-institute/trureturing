using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeGroundSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeGroundSeparation", H("NativeGroundSeparation"), Blocks(
            Entry("Term", "Finite Boolean free terms", "Constants and variables have different sum constructors. Terms are finite free ordered full trees, with repeated variable names preserving one shared value.", DescribeRole.Definition),
            Entry("evaluate", "Native ground evaluation", "FreeMagma.lift simultaneously replaces variables by actual Boolean trees and preserves constants and ordered pairs.", DescribeRole.Definition),
            Entry("counts", "Occurrence masses", "Variable and constant occurrences are counted separately, including repetitions. Under a common variable leaf mass M, evaluation has exactly M times the variable count plus the constant count leaves.", DescribeRole.Definition),
            Entry("code", "Equal-mass separating assignments", "The existing comb constructor encodes a finite index by one marked leaf in a common finite shape. Its existing length and equality theorem is reused directly.", DescribeRole.Definition),
            Entry("simultaneous_ground_separation", "All finite disequalities simultaneously", "A finite list of syntactically unequal term pairs admits one simultaneous ground assignment separating every pair. Large common variable masses prevent a variable from colliding with either a ground subterm or a genuine compound containing a variable. The empty variable type is included. This is an existence and feasibility result, not an acquisition of source values.", DescribeRole.Theorem)
        )));
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativegroundseparation-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), Statement(n),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static StatementSource Statement(string n) => n switch
    {
        "simultaneous_ground_separation" => StatementSource.FromAuthor(Disp(All("X", V("Type"), All("I", Call("Fintype", V("X")), All("D", Call("List", Call("Prod", Call("Term", V("X")), Call("Term", V("X")))), IffOf(All("p", Call("Prod", Call("Term", V("X")), Call("Term", V("X"))), Imp(Mem(V("p"), V("D")), NeOf(Call("fst", V("p")), Call("snd", V("p"))))), Some("v", Arr(V("X"), V("Source")), All("p", Call("Prod", Call("Term", V("X")), Call("Term", V("X"))), Imp(Mem(V("p"), V("D")), NeOf(Call("evaluate", V("v"), Call("fst", V("p"))), Call("evaluate", V("v"), Call("snd", V("p"))))))))))))),
        _ => StatementSource.WithoutFormula()
    };
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula NeOf(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
}
