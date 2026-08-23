using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints.Reachability;

internal sealed class SafetyDichotomyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A relation-generated least fixed point either certifies all finite paths as safe "
            + "or supplies a finite path to a bad state.",
        H("Reachability Safety Dichotomy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reachability-safety-and-bad-path"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/Reachability/SafetyDichotomy."
                        + "reachability_safety_and_bad_path"),
                H("Safety and finite counterexample paths form a dichotomy"),
                StatementSource.FromAuthor(DichotomyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A transition relation R and initial set I0 construct the reachability "
                            + "operator by adjoining I0 to the direct R-image of the current "
                            + "approximation. Reach is the least fixed point of this operator.")),
                    Paragraph(Text(
                        "If Reach is contained in the safe set S, every finite reflexive-transitive "
                            + "R-path beginning in I0 ends in S. This is the path-level safety "
                            + "clause of the source theorem.")),
                    Paragraph(Text(
                        "If Reach meets the complement of S, finite-stage expansion locates the "
                            + "bad state at a finite iterate. Induction over that iterate constructs "
                            + "an initial state and a finite R-path ending outside S.")),
                    Paragraph(Text(
                        "The proof imports the canonical relation-generated reachability operator "
                            + "and its finite-stage expansion rather than redeclaring either source "
                            + "object. The pinned relation closure constructors supply the exact "
                            + "finite path."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S1/FixedPoints/RelationalReachExpansion"))]));

    private static Formula DichotomyFormula()
    {
        Formula stateType = F.Id("X");
        Formula relation = F.Id("R");
        Formula initial = Seq(F.Id("I"), Underscore, Grp(D(0)));
        Formula safe = F.Id("S");
        Formula start = Seq(F.Id("x"), Underscore, Grp(D(0)));
        Formula target = F.Id("x");
        Formula stateSet = Call("Set", stateType);
        Formula relationType = Call("Set", Seq(stateType, Sp, Times, Sp, stateType));
        Formula reach = Call("lfp", Call("reachStep", relation, initial));
        Formula path = Call("ReflTransGen", relation, start, target);
        Formula badSet = Seq(stateType, Sp, Setminus, Sp, safe);
        Formula safety = Seq(
            reach, Sp, Subseteq, Sp, safe, Sp, Rightarrow, Sp,
            Forall, Sp, start, Sp, InMacro, Sp, initial, Comma, Sp,
            target, Colon, Sp, stateType, Comma, Sp,
            path, Sp, Rightarrow, Sp, target, Sp, InMacro, Sp, safe);
        Formula counterexample = Seq(
            Call("Nonempty", Call("inter", reach, badSet)), Sp,
            Rightarrow, Sp, Exists, Sp,
            start, Sp, InMacro, Sp, initial, Comma, Sp,
            target, Sp, InMacro, Sp, badSet, Comma, Sp, path);

        return Disp(Seq(
            Forall, Sp, stateType, Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(), relation, Colon, Sp, relationType, Comma, Sp,
            initial, Comma, Sp, safe, Colon, Sp, stateSet, Comma,
            RowBreak, Grp(), Open, safety, Close, Sp, Land, Sp,
            RowBreak, Grp(), Open, counterexample, Close, Dot));
    }
}
