using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class ProgressionSubshiftDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/ProgressionSubshift.";
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(Id(s))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static DocumentBlock.Describe Thm(string key, string decl, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(key), DeclarationHandle.Create(Owner + decl), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact hereditary one-sided progression subshifts, zero-gap mixing and a nonempty periodic-set obstruction.",
        H("Progression-Avoidance Subshifts"), Blocks(
        Paragraph(Text("The alphabet is the existing binary ReturnBit={0,1}. A configuration x is ProgressionLegal(ell,x) when, for every natural start s and every positive natural difference p, some j<ell(p) has x(s+jp)=0. "
            + "Mathlib PiNat.metricSpaceOfDiscreteUniformity supplies exactly the first-disagreement metric d(x,y)=2^(-firstDiff(x,y)), with zero distance on equal points, and the actual product topology and uniformity. "
            + "The arithmetic-progression construction and its use for Meddaugh--Stephens Question 5.6 are attributed to Pro.")),
        Thm("progression-closed", "progression_legal_closed", "Closedness of all progression constraints", St(
            Seq(Forall, Sp, Id("ell"), Colon, Sp, Mathbb, Grp(Id("N")), Sp, To, Sp, Mathbb, Grp(Id("N")), Comma, Sp,
                Call("IsClosed", Seq(OpenBrace, Id("x"), Colon, Sp, Mathbb, Grp(Id("N")), Sp, To, Sp, Id("ReturnBit"), Sp,
                    Mid, Sp, Call("ProgressionLegal", Id("ell"), Id("x")), CloseBrace)))),
            "A fixed progression condition is a finite union of closed coordinate cylinders. Intersect over all starts and positive differences. The finite-alphabet product is compact, hence its closed carrier subtype is compact."),
        Paragraph(Text("All natural shifts preserve the constraints. Prepending a zero yields a legal preimage whenever ell(p)>0 for every positive p, so the continuous left shift is onto. "
            + "Deleting ones preserves every already satisfied constraint. The all-zero point is legal under the same positive-length assumption; the configuration 10-infinity is legal when all lengths are at least two.")),
        Thm("progression-zero-gap", "progression_join_legal", "Zero-gap joining without new forbidden progressions", St(
            Seq(Forall, Sp, Id("ell"), Colon, Sp, Mathbb, Grp(Id("N")), Sp, To, Sp, Mathbb, Grp(Id("N")), Comma),
            Seq(Open, Forall, Sp, Id("p"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp,
                D(0), Lt, Id("p"), Sp, Rightarrow, Sp, D(3), Le, Call("ell", Id("p")), Close, Sp, Rightarrow),
            Seq(Forall, Sp, Id("x"), Comma, Id("y"), Colon, Sp, Mathbb, Grp(Id("N")), Sp, To, Sp, Id("ReturnBit"), Comma, Sp,
                Call("ProgressionLegal", Id("ell"), Id("x")), Sp, Rightarrow, Sp,
                Call("ProgressionLegal", Id("ell"), Id("y")), Sp, Rightarrow),
            Seq(Forall, Sp, Id("a"), Comma, Id("b"), Comma, Id("n"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp,
                Id("a"), Plus, Call("max", Id("a"), Id("b")), Le, Sp, Id("n"), Sp, Rightarrow, Sp,
                Call("ProgressionLegal", Id("ell"), Call("progressionJoin", Id("x"), Id("y"), Id("a"), Id("b"), Id("n"))))),
            "Assume ell(p)>=3 for all positive p. Keep x on [0,a), y shifted to [n,n+b), and put zeros elsewhere. A progression with p<=max(a,b) starting in the first word cannot cross the gap, by induction on its index. "
            + "At p>max(a,b), at most one progression term lies in each word; its first three terms cannot all be supported. A progression starting in the second word contradicts legality of y. "
            + "Thus every sufficiently large n connects any two prescribed prefix cylinders. Metric neighborhoods contain such cylinders, proving open-set mixing in progression_shift_mixing."),
        Thm("progression-periodic-obstruction", "progression_no_invariant_subset", "No nonempty forward invariant subset in the one cylinder", St(
            Seq(Forall, Sp, Id("ell"), Colon, Sp, Mathbb, Grp(Id("N")), Sp, To, Sp, Mathbb, Grp(Id("N")), Comma, Sp,
                Forall, Sp, Id("p"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp, D(0), Lt, Id("p"), Sp, Rightarrow),
            Seq(Forall, Sp, Id("B"), Colon, Sp, Call("Set", Call("ProgressionPoint", Id("ell"))), Comma, Sp,
                Id("B"), Sp, Subseteq, Sp, Call("progressionOneCylinder", Id("ell")), Sp, Rightarrow),
            Seq(Call("MapsTo", Seq(Open, Call("progressionShift", Id("ell")), Close, Caret, Grp(Id("p"))), Id("B"), Id("B")),
                Sp, Rightarrow, Sp, Neg, Sp, Call("Nonempty", Id("B")))),
            "Here Set(T) denotes subsets of T, f^p denotes p-fold iteration, and MapsTo(f,B,B) means that f maps B into B. Choose x in B. Forward invariance gives (progressionShift(ell))^(jp)(x) in B for every natural j, so x(jp)=1 at every such coordinate, contradicting its p-progression condition. "
            + "The cylinder [1] is clopen, and nonempty when ell(p)>=2. Compactness and image equality are unnecessary for this obstruction.")
        )));
}
