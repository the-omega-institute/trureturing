using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class FiniteOperatorSystemStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula dimension = F.Id("d");
        Formula map = F.Id("H");
        Formula initial = Seq(F.Id("S"), Underscore, Grp(D(0)));
        Formula stage = F.Id("m");
        Formula offset = F.Id("r");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", dimension, dimension, complex);
        Formula hermitian = Call("Hermitian", matrix);
        Formula mapType = Call("CompletelyPositiveMap", matrix, matrix);
        Formula stageAtM = Call("predictionTower", map, initial, stage);
        Formula stageAtSuccessor = Call(
            "predictionTower", map, initial, Seq(stage, Plus, D(1)));
        Formula stageAtOffset = Call(
            "predictionTower", map, initial, Seq(stage, Plus, offset));
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, dimension, Comma, Sp,
            Call("Finite", dimension), Comma, RowBreak, Grp(),
            map, Colon, Sp, mapType, Comma, Sp,
            Seq(map, Open, F.Id("I"), Close), Sp, Eq, Sp, F.Id("I"), Comma,
            RowBreak, Grp(),
            initial, Colon, Sp, Call("OperatorSystem", hermitian), Comma, Sp,
            stage, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            stageAtM, Sp, Eq, Sp, stageAtSuccessor, Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, offset, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            stageAtOffset, Sp, Eq, Sp, stageAtM, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite operator-system stability at one step persists at every later step.",
            H("Finite Operator-System Stability"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("finite-operator-system-stability-is-permanent"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Fibers/FiniteOperatorSystemStability."
                            + "finite_operator_system_once_stable_permanently"),
                    H("One stable operator-system step is permanently stable"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The finite carrier is the full real self-adjoint part of a "
                                + "complex matrix algebra. The initial operator system and "
                                + "prediction tower are the canonical objects supplied by the "
                                + "operator-system tower family.")),
                        Paragraph(Text(
                            "The Heisenberg action is a unital completely positive map. Each "
                                + "tower step joins the current system with its image under that "
                                + "map, so the tower is constructed from the source channel and "
                                + "initial accessible system.")),
                        Paragraph(Text(
                            "The imported permanent-stability theorem applies directly to "
                                + "equality of stages m and m plus one, yielding equality of "
                                + "every stage m plus r with stage m."))),
                    DescribeRole.Theorem))));
    }
}
