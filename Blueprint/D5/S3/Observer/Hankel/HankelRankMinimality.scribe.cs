using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class HankelRankMinimalityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Hankel/HankelRankMinimality."
            + "hankel_rank_eq_reachable_dim_sub_inter_unobservable_dim";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Once both finite horizons reach the state-space dimension, the block Hankel "
            + "rank is the reachable dimension minus the invisible reachable dimension.",
        H("Hankel Rank Minimality"),
        Blocks(Describe.Lean(
            DescribeId.Create("hankel-rank-minimality"),
            DeclarationHandle.Create(Declaration),
            H("Stable Hankel rank counts visible reachable directions"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let A be the state evolution, B the input map, and C the readout of a "
                        + "finite-dimensional linear system over a field. The finite Hankel map "
                        + "has block (i,j) equal to C A^(i+j) B.")),
                Paragraph(Text(
                    "For row and column horizons at least finrank(K,V), its range has dimension "
                        + "equal to the imported reachable subspace dimension minus the dimension "
                        + "of its intersection with the imported all-future kernel."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula input = F.Id("U");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("A");
        Formula control = F.Id("B");
        Formula readout = F.Id("C");
        Formula rows = F.Id("r");
        Formula columns = F.Id("s");
        Formula stateDimension = Call("finrank", scalar, state);
        Formula reachable = Call("reachableSubspace", evolution, control);
        Formula invisible = Call("eventualKernel", readout, evolution);
        Formula hankel = Call(
            "finiteHankel", evolution, control, readout, rows, columns);
        Formula equation = new Formula.Relation(
            Call("finrank", scalar, Call("range", hankel)),
            FormulaRelationOperator.Equal,
            Subtract(
                Call("finrank", scalar, reachable),
                Call("finrank", scalar, Call("inf", reachable, invisible))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, input, Comma, Sp,
            output, Colon, Sp, F.Id("Type"), Comma, RowBreak, Grp(),
            Call("Field", scalar), Sp, Land, Sp,
            Call("AddCommGroup", state), Sp, Land, Sp,
            Call("Module", scalar, state), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, state), Sp, Land, RowBreak, Grp(),
            Call("AddCommGroup", input), Sp, Land, Sp,
            Call("Module", scalar, input), Sp, Land, Sp,
            Call("AddCommGroup", output), Sp, Land, Sp,
            Call("Module", scalar, output), Sp, Land, RowBreak, Grp(),
            evolution, Sp, InMacro, Sp, Call("LinearMap", scalar, state, state), Sp,
            Land, Sp, control, Sp, InMacro, Sp,
            Call("LinearMap", scalar, input, state), Sp,
            Land, Sp, readout, Sp, InMacro, Sp,
            Call("LinearMap", scalar, state, output), Sp, Land, RowBreak, Grp(),
            rows, Comma, Sp, columns, Sp, InMacro, Sp, F.Id("N"), Comma, Sp,
            stateDimension, Sp, Leq, Sp, rows, Sp, Land, Sp,
            stateDimension, Sp, Leq, Sp, columns, Sp,
            Rightarrow, RowBreak, Grp(), equation, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
