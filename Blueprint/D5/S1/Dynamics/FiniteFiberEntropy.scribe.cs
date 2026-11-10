using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class FiniteFiberEntropyDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => s == "π" ? Pi : F.Id(s);
    private static Formula Call(string s, params Formula[] args)
    {
        var name = new List<Formula>();
        foreach (var part in s.Split('.'))
        {
            if (name.Count > 0) name.Add(Dot);
            name.Add(Id(part));
        }
        var items = new List<Formula> { Seq(Operatorname, Grp(Seq([.. name]))), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), Colon, Sp, t, Comma);
    private static Formula Instance(string s, string x) => Seq(OpenBracket, Call(s, Id(x)), CloseBracket);
    private static Formula Fiber => Call("Set.preimage", Id("π"), Call("Set.singleton", Id("y")));
    private static Formula Entropy(string t) => Call("Dynamics.coverEntropy", Id(t), Call("Set.univ"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compact factor map with a uniform bound on its finite fibers preserves topological entropy.",
        H("Finite Fibers Preserve Topological Entropy"), Blocks(
        Paragraph(Text("Let X and Y be compact uniform spaces, with Y Hausdorff. Let S:X→X be continuous, "
            + "and let π:X→Y be a continuous surjection satisfying π∘S=T∘π. Every fiber π⁻¹{y} is finite "
            + "and its cardinality is at most the same natural number M. The covering entropy of S equals that of T. "
            + "This formalizes the classical finite-to-one factor theorem; no literature novelty is claimed.")),
        Describe.Lean(DescribeId.Create("finite-fiber-entropy"),
            DeclarationHandle.Create("D5/S1/Dynamics/FiniteFiberEntropy.finite_fiber_entropy"),
            H("Entropy equality under uniformly finite fibers"),
            StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(All("X", Id("Type")), Sp, All("Y", Id("Type"))),
                Seq(Grp(Instance("UniformSpace", "X"), Sp, Instance("CompactSpace", "X"), Sp,
                    Instance("UniformSpace", "Y"), Sp, Instance("CompactSpace", "Y"), Sp, Instance("T2Space", "Y"), Comma)),
                Seq(All("S", Seq(Id("X"), Sp, To, Sp, Id("X"))), Sp,
                    All("T", Seq(Id("Y"), Sp, To, Sp, Id("Y"))), Sp,
                    All("π", Seq(Id("X"), Sp, To, Sp, Id("Y")))),
                Seq(Call("Continuous", Id("S")), Sp, Rightarrow, Sp,
                    Call("Continuous", Id("π")), Sp, Rightarrow),
                Seq(Call("Function.Surjective", Id("π")), Sp, Rightarrow, Sp,
                    Call("Function.Semiconj", Id("π"), Id("S"), Id("T")), Sp, Rightarrow),
                All("M", Seq(Mathbb, Grp(Id("N")))),
                Seq(Grp(All("y", Id("Y")), Sp, Call("Set.Finite", Fiber), Sp, Land, Sp,
                    Call("Set.ncard", Fiber), Sp, Le, Sp, Id("M")), Sp, Rightarrow),
                Seq(Entropy("S"), Sp, Eq, Sp, Entropy("T"))
            ]))), AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Entropy/bowen1971entropy")), Blocks(
                Paragraph(Text("For a symmetric source entourage U and fixed block length n, the n-step balls "
                    + "centered on a fiber cover that fiber using at most M centers. Since π is a closed map, "
                    + "this cover extends to the inverse image of a neighborhood of the base point. "
                    + "The Lebesgue number lemma makes the base entourage uniform over Y.")),
                Paragraph(Text("Over r consecutive blocks, each base covering orbit has at most M^r center codes. "
                    + "One actual orbit representative from every nonempty code class gives a source cover at entourage U∘U. "
                    + "No continuous selection of fiber points or lifting of a prescribed orbit is assumed. "
                    + "The source covering number at time n*r is at most M^r times the base covering number. "
                    + "Monotonicity permits restriction to these multiples; their extra entropy is log(M)/n, which tends to zero.")),
                Paragraph(Text("The reverse inequality reuses Mathlib's coverEntropy_image_le_of_uniformContinuous. "
                    + "The proof handles empty spaces, M=0 when both spaces are empty, and infinite entropy. "
                    + "It does not require T to be continuous or X to be Hausdorff. Finiteness of fibers is an explicit hypothesis: "
                    + "Set.ncard alone cannot express a finite bound because it is zero on an infinite set. "
                    + "The result supplies the entropy comparison needed by finite symbolic codings of compact dynamical systems; "
                    + "constructing a coding and proving its uniform fiber bound remain application-specific obligations."))),
            DescribeRole.Theorem))));
}
