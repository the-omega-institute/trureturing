using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeComputedEpochPotentialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Computed occurrence potentials for native epoch transport",
        H("Finite occurrence cycles yield a natural epoch potential"), Blocks(
            Paragraph(Text("Finite occurrence positions are enumerated directly from every original equation. The resulting graph keeps loops, parallel edges, repeated occurrences, disconnected states, empty systems, signed exponent differences and equations with undefined heads.")),
            Describe.Lean(DescribeId.Create("computed-occurrence-potential"),
                DeclarationHandle.Create(Prefix + "cycleCondition_iff_potential"),
                H("Cycle criterion and computed potential"),
                StatementSource.FromAuthor(Disp(CycleCriterion())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The graph reverses an occurrence edge so its max-plus potential inequality is exactly the natural difference inequality. A potential telescopes around every closed walk. Conversely, the finite max-plus construction supplies a real potential, integer flooring preserves the integer-weight inequalities, and one finite input-derived offset establishes every nonnegativity and defined-head lower bound. The recursive ShiftLegal predicate is then proved by induction over the actual expression syntax, including ordered pairs and repeated occurrences."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("computed-occurrence-transport"),
                DeclarationHandle.Create(Prefix + "cycleCondition_gives_epoch_transport"),
                H("The computed potential feeds the original solution correspondence"),
                StatementSource.FromAuthor(Disp(TransportCriterion())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under the cycle condition, the computed tuple is passed directly to the existing exact epoch correspondence. Literal transformed evaluation, all state-image filters, every additional filter, undefined states and every original reconstruction therefore remain in the same fixed parameter relation. The independent finite-exception prefix and rigidity clauses are inherited through the existing consumer."))), DescribeRole.Theorem)
        )));

    private static Formula CycleCriterion()
    {
        var I = V("I");
        return All("n", V("Nat"), All("k", V("Nat"), All("m", V("Nat"),
            All("I", Call("EpochInput", V("n"), V("k"), V("m")),
                IffOf(Call("CycleCondition", I), Some("s", Arr(Call("Fin", V("m")), V("Nat")), Call("Potential", I, V("s"))))))));
    }

    private static Formula TransportCriterion()
    {
        var I = V("I");
        var s = V("s");
        var p = V("p");
        var w = V("w");
        var functional = Call("functionalInput", I, s);
        var source = And(Call("Legal", functional, p),
            And(Call("SourceSatisfies", functional, p, w),
                Call("SourcePasses", functional, p, w)));
        var correspondence = Unique("v", Arr(Call("Fin", V("m")), V("CompletionTree")),
            And(Call("OriginalAdmissible", I, p, V("v")),
                Eq(Call("imageValues", s, V("v")), w)));
        var quantified = All("p", Arr(Call("Fin", V("n")), V("Nat")),
            All("w", Arr(Call("Fin", V("m")), V("CompletionTree")),
                IffOf(source, correspondence)));
        var body = Imp(Call("CycleCondition", I), Some("s", Arr(Call("Fin", V("m")), V("Nat")),
            And(Call("Potential", I, s), quantified)));
        return All("n", V("Nat"), All("k", V("Nat"), All("m", V("Nat"),
            All("I", Call("EpochInput", V("n"), V("k"), V("m")), body))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Sp, Land, Sp, b, Close);
    private static Formula IffOf(Formula a, Formula b) => Seq(Open, a, Sp, Iff, Sp, b, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Sp, Implies, Sp, b, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Open, body, Close);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Open, body, Close);
    private static Formula Unique(string name, Formula type, Formula body) =>
        Seq(Exists, Bang, Sp, V(name), Colon, Sp, type, Comma, Sp, Open, body, Close);
}
