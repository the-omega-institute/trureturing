using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class MaximalUnobservableSubspaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-future readout kernel is the maximal invariant hidden subspace.",
        H("Maximal Unobservable Subspace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-unobservable-invariant-subspace"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace."
                        + "future_kernel_is_maximal_invariant"),
                H("The future kernel is maximal among invariant hidden subspaces"),
                StatementSource.FromAuthor(MaximalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V and Y be finite-dimensional inner-product spaces over a real or "
                            + "complex scalar field. Let T evolve V linearly and let C read V "
                            + "linearly into Y.")),
                    Paragraph(Text(
                        "The hidden subspace is constructed canonically as the intersection of "
                            + "the kernels of C composed with every power of T. This is the "
                            + "source all-future readout test, not a definition by maximality.")),
                    Paragraph(Text(
                        "The public theorem states all maximality clauses: the future kernel lies "
                            + "inside ker(C), T maps it into itself, and every T-invariant subspace "
                            + "inside ker(C) is contained in it.")),
                    Paragraph(Text(
                        "The zero iterate proves current invisibility, shifting an iterate proves "
                            + "invariance, and induction keeps every iterate of a point in any "
                            + "competing invariant subspace."))),
                DescribeRole.Theorem))));

    private static Formula MaximalityFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula index = F.Id("k");
        Formula candidate = F.Id("M");
        Formula hidden = new Formula.Subscript(F.Id("N"), Infty);
        Formula iterate = Seq(evolution, Caret, Grp(index));
        Formula futureReadout = Seq(readout, Sp, Circ, Sp, iterate);
        Formula futureKernel = Call("ker", futureReadout);
        Formula currentKernel = Call("ker", readout);
        Formula construction = Call("iInf", index, futureKernel);
        Formula contained = Seq(hidden, Sp, Subseteq, Sp, currentKernel);
        Formula invariant = Call("MapsTo", evolution, hidden, hidden);
        Formula candidateInvariant = Call("MapsTo", evolution, candidate, candidate);
        Formula maximal = Seq(
            Forall, Sp, candidate, Colon, Sp, Call("Submodule", scalar, state), Comma, Sp,
            Open, candidate, Sp, Subseteq, Sp, currentKernel, Sp, Land, Sp,
            candidateInvariant, Close, Sp, Rightarrow, Sp,
            candidate, Sp, Subseteq, Sp, hidden);

        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateMap = Call("LinearMap", scalar, state, state);
        Formula readoutMap = Call("LinearMap", scalar, state, output);
        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output, Colon, Sp, type,
            Comma, Sp, OpenBracket, Call("RCLike", scalar), CloseBracket, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", state), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", scalar, state), CloseBracket, Comma, Sp,
            OpenBracket, Call("FiniteDimensional", scalar, state), CloseBracket, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", output), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", scalar, output), CloseBracket, Comma, Sp,
            OpenBracket, Call("FiniteDimensional", scalar, output), CloseBracket, RowBreak, Grp(),
            evolution, Colon, Sp, stateMap, Comma, Sp, readout, Colon, Sp, readoutMap,
            Comma, RowBreak, Grp(), hidden, Sp, Colon, Eq, Sp, construction, Semi,
            RowBreak, Grp(), contained, Sp, Land, Sp, invariant, Sp, Land,
            RowBreak, Grp(), maximal, Dot));
    }
}
