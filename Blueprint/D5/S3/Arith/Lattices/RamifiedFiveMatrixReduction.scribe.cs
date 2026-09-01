using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class RamifiedFiveMatrixReductionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/Lattices/RamifiedFiveMatrixReduction."
            + "ramified_five_matrix_reduction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral matrix that squares to five times the identity is nonnilpotent over "
            + "the integers and invertible over the rationals, but its reduction at the "
            + "ramified prime five is square-zero.",
        H("Ramified Five Matrix Reduction"),
        Blocks(Describe.Lean(
            DescribeId.Create("ramified-five-matrix-reduction"),
            DeclarationHandle.Create(Declaration),
            H("Reduction at five turns an integral square root of five nilpotent"),
            StatementSource.FromAuthor(ReductionFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Mapping the identity J^2=5I_n through the explicit ring homomorphism "
                        + "from the integers to ZMod five sends the right-hand side to zero. "
                        + "Multiplicativity of matrix mapping then gives Jbar^2=0. Standard "
                        + "nilpotent-matrix identities force the characteristic polynomial, "
                        + "trace, and determinant conclusions.")),
                Paragraph(Text(
                    "Taking determinants before reduction gives det(J)^2=5^n, which is "
                        + "nonzero because n is positive. Thus J cannot be nilpotent over "
                        + "the integers, and its determinant remains nonzero over the "
                        + "rationals, where the matrix is invertible. This contrast is the "
                        + "ramification phenomenon captured by the theorem.")),
                Paragraph(Text(
                    "The concrete witness J=((0,5),(1,0)) has determinant -5 and reduces "
                        + "to ((0,0),(1,0)). The Lean module also proves that an integral "
                        + "compatibility relation J^T G=GJ survives reduction and applies "
                        + "the theorem to the integral Hodge matrix on Lambda^2 A4."))),
            DescribeRole.Theorem))));

    private static Formula ReductionFormula()
    {
        Formula n = F.Id("n");
        Formula j = F.Id("J");
        Formula jbar = Call("reduceFive", j);
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula matrices = Call("M", n, integers);
        Formula identity = Call("I", n);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
                n, Sp, Geq, Sp, D(1), Comma, Sp,
                Forall, Sp, j, Sp, InMacro, Sp, matrices, Comma, Sp,
                j, Caret, D(2), Sp, Eq, Sp, D(5), identity, Sp, Rightarrow),
            Seq(
                Grp(), jbar, Caret, D(2), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                Call("IsNilpotent", jbar), Sp, Land),
            Seq(
                Grp(), Call("charpoly", jbar), Sp, Eq, Sp,
                F.Id("X"), Caret, n, Sp, Land, Sp,
                Call("trace", jbar), Sp, Eq, Sp, D(0), Sp, Land),
            Seq(
                Grp(), Call("det", jbar), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                Call("det", j), Caret, D(2), Sp, Eq, Sp, D(5), Caret, n, Sp, Land),
            Seq(
                Grp(), Neg, Call("IsNilpotent", j), Sp, Land, Sp,
                Call("IsUnitOverRationals", j), Dot),
        ]));
    }

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
}
