using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OperatorSystemTowerStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-step stability of a full Hermitian operator-system tower is permanent.",
        H("Permanent Stability of the Operator-System Tower"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("operator-system-tower-one-step-stability-is-permanent"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fibers/OperatorSystemTowerStability."
                        + "operator_system_tower_once_stable_permanently"),
                H("One-step operator-system stability is permanent"),
                StatementSource.FromAuthor(StabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the full real self-adjoint part of the finite complex "
                            + "matrix algebra, rather than its centered trace-zero subspace. "
                            + "An operator system is a real subspace of that carrier containing "
                            + "the identity.")),
                    Paragraph(Text(
                        "The Heisenberg action is supplied by a unital completely positive map. "
                            + "Each prediction step joins the current operator system with its "
                            + "Heisenberg image, and the finite tower is the iteration of this "
                            + "source closure step from the initial operator system.")),
                    Paragraph(Text(
                        "Equality of stages n and n plus one says that stage n is a fixed point "
                            + "of the closure step. Fixed-point iteration then identifies every "
                            + "stage n plus r with stage n."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Stage(Formula map, Formula initial, Formula index) =>
        Call("predictionTower", map, initial, index);

    private static Formula StabilityFormula()
    {
        Formula d = F.Id("d");
        Formula n = F.Id("n");
        Formula r = F.Id("r");
        Formula map = Seq(Phi, Caret, Grp(Star));
        Formula initial = Seq(F.Id("S"), Underscore, Grp(D(0)));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", d, d, complex);
        Formula hermitian = Call("Hermitian", matrix);
        Formula mapType = Call("CompletelyPositiveMap", matrix, matrix);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d, Comma, Sp, Call("Finite", d), Comma, RowBreak, Grp(),
            map, Colon, Sp, mapType, Comma, Sp,
            Apply(map, F.Id("I")), Sp, Eq, Sp, F.Id("I"), Comma, RowBreak, Grp(),
            initial, Colon, Sp, Call("OperatorSystem", hermitian), Comma, Sp,
            n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            Stage(map, initial, n), Sp, Eq, Sp,
            Stage(map, initial, Seq(n, Plus, D(1))), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, r, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Stage(map, initial, Seq(n, Plus, r)), Sp, Eq, Sp,
            Stage(map, initial, n), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
