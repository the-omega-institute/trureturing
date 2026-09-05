using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class FiniteMemoryHistoryCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Perfectly distinguishable density matrices number at most the memory dimension.",
        H("Finite Memory History Capacity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-memory-history-capacity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity."
                        + "finite_memory_history_capacity"),
                H("Exact history capacity of finite quantum memory"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/barnett2009discrimination")),
                Blocks(
                    Paragraph(Text(
                        "The memory has complex dimension d. Histories are represented by "
                            + "the indexed density matrices rho, and E is one designated POVM. "
                            + "PosSemidef means positive semidefinite, Tr is the complex "
                            + "matrix trace, I is the identity matrix, and if selects its "
                            + "second or third argument according to its first argument.")),
                    Paragraph(Text(
                        "A zero trace pairing of two positive matrices forces their product "
                            + "to vanish, so the state range lies in the effect kernel. "
                            + "Applying this to the positive complement of an effect with "
                            + "unit probability puts its state range in the one-eigenspace.")),
                    Paragraph(Text(
                        "The state ranges are therefore pairwise orthogonal. Trace one "
                            + "makes every state nonzero. Choosing a nonzero vector in each "
                            + "range gives a linearly independent family in dimension d.")),
                    Paragraph(Text(
                        "This bound concerns perfectly distinguishable records, rather than "
                            + "the number of real parameters of a density matrix. Barnett "
                            + "and Croke provide the literature context for discrimination "
                            + "and orthogonal supports; the cited note identifies the scope."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula count = F.Id("N");
        Formula dimension = F.Id("d");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula effects = F.Id("E");
        Formula indices = Call("Fin", count);
        Formula coordinates = Call("Fin", dimension);
        Formula matrices = Call("Matrix", coordinates, coordinates, Seq(Mathbb, Grp(F.Id("C"))));
        Formula state = Seq(Rho, Underscore, Grp(i));
        Formula effect = Seq(effects, Underscore, Grp(j));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, count, Comma, Sp, dimension, Colon, Sp, F.Id("Nat"), Comma),
            Seq(Forall, Sp, Rho, Comma, Sp, effects, Colon, Sp,
                indices, Sp, To, Sp, matrices, Comma),
            Seq(Parenthesized(Seq(Forall, Sp, i, Colon, Sp, indices, Comma, Sp,
                Call("PosSemidef", state), Sp, Land, Sp,
                Call("Tr", state), Sp, Eq, Sp, D(1))), Sp, Rightarrow),
            Seq(Parenthesized(Seq(Forall, Sp, j, Colon, Sp, indices, Comma, Sp,
                Call("PosSemidef", effect))), Sp, Rightarrow),
            Seq(Parenthesized(Seq(Sum, Underscore, Grp(j, Colon, Sp, indices), Sp,
                effect, Sp, Eq, Sp, F.Id("I"))), Sp, Rightarrow),
            Seq(Parenthesized(Seq(Forall, Sp, i, Comma, Sp, j, Colon, Sp, indices, Comma, Sp,
                Call("Tr", Seq(effect, Sp, Cdot, Sp, state)), Sp, Eq, Sp,
                Call("if", Seq(i, Sp, Eq, Sp, j), D(1), D(0)))), Sp, Rightarrow),
            Seq(count, Sp, Leq, Sp, dimension, Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Seq([.. items])));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
