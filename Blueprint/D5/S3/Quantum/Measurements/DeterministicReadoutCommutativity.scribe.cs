using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class DeterministicReadoutCommutativityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic readout projections share a diagonal basis, while general quantum observables need not commute.",
        H("Deterministic Readout Commutativity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("deterministic-readout-commutativity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurements/DeterministicReadoutCommutativity."
                        + "deterministic_readout_commutes_and_quantum_counterexample"),
                H("Common-basis projections commute; a qubit pair is noncommuting"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every deterministic interface is represented by diagonal indicators "
                            + "of its readout fibers in one standard basis, so all such projections commute.")),
                    Paragraph(Text(
                        "The reverse inclusion fails: the Pauli qubit pair is self-adjoint, squares "
                            + "to the identity, and has unequal products in the two orders."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula o = F.Id("o");
        Formula op = F.Id("op");
        Formula index = F.Id("I");
        Formula state = F.Id("X");
        Formula outcome = F.Id("O");
        Formula readouts = F.Id("q");
        Formula p = Call("deterministicProjection", Call("q", i), o);
        Formula q = Call("deterministicProjection", Call("q", j), op);
        Formula commute = Seq(p, Sp, Circ, Sp, q, Sp, Eq, Sp, q, Sp, Circ, Sp, p);
        Formula counter = Seq(
            Exists, Sp, F.Id("P"), Comma, Sp, F.Id("Q"), Sp, Colon, Sp,
            Call("QubitMatrix"), Comma, Sp,
            Seq(Operatorname, Grp(F.Id("star")), Open, F.Id("P"), Close), Sp, Eq, Sp, F.Id("P"), Sp, Land, Sp,
            Seq(Operatorname, Grp(F.Id("star")), Open, F.Id("Q"), Close), Sp, Eq, Sp, F.Id("Q"), Sp, Land, Sp,
            Seq(F.Id("P"), Sp, Circ, Sp, F.Id("P")), Sp, Eq, Sp, F.Id("I"), Sp, Land, Sp,
            Seq(F.Id("Q"), Sp, Circ, Sp, F.Id("Q")), Sp, Eq, Sp, F.Id("I"), Sp, Land, Sp,
            Seq(F.Id("P"), Sp, Circ, Sp, F.Id("Q")), Sp, Neq, Sp, Seq(F.Id("Q"), Sp, Circ, Sp, F.Id("P")));
        return Disp(Seq(
            Forall, Sp, Typed(state, type), Comma, Sp,
            Typed(outcome, type), Comma, Sp,
            Typed(index, type), Comma, Sp,
            Instance("Fintype", state), Comma, Sp,
            Instance("DecidableEq", state), Comma, Sp,
            Instance("DecidableEq", outcome), Comma, Sp,
            Typed(readouts, Arrow(index, Arrow(state, outcome))), Sp,
            Rightarrow, Sp,
            Forall, Sp, Typed(i, index), Comma, Sp,
            Typed(j, index), Comma, Sp,
            Typed(o, outcome), Comma, Sp,
            Typed(op, outcome), Comma, Sp,
            commute, Sp, Land, Sp, counter, Dot));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Instance(string name, Formula value) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, value, Close, CloseBracket);
}
