using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WindowAlgebra;

internal sealed class FinitePartitionAlgebraOrderReversalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite state-kernel inclusion reverses real effect-algebra inclusion.",
        H("Finite Partition Algebra Order Reversal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-partition-algebra-order-reversal"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/WindowAlgebra/FinitePartitionAlgebraOrderReversal."
                        + "finite_partition_algebra_order_reversal"),
                H("Smaller state kernels give larger effect algebras"),
                StatementSource.FromAuthor(OrderReversalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be finite and let R1 and R2 be equivalence relations on X. "
                            + "For each relation R, its effect algebra is constructed as the "
                            + "set of real-valued functions constant on every R-class.")),
                    Paragraph(Text(
                        "If R1 is contained in R2, every function constant on R2 is constant "
                            + "on R1. Conversely, the existing finite real partition-algebra "
                            + "reconstruction theorem turns reverse algebra inclusion back into "
                            + "the original relation inclusion.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no exact order-reversal "
                            + "theorem. The proof applies the existing real-carrier reconstruction "
                            + "result directly; no alternate algebra construction is introduced."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula OrderReversalFormula()
    {
        Formula state = F.Id("X");
        Formula firstRelation = Subscript(F.Id("R"), D(1));
        Formula secondRelation = Subscript(F.Id("R"), D(2));
        Formula firstAlgebra = Subscript(F.Id("A"), firstRelation);
        Formula secondAlgebra = Subscript(F.Id("A"), secondRelation);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, firstRelation, Comma, Sp, secondRelation, Comma, Esc,
            F.Id("Finite"), Open, state, Close, Sp, Land, Sp,
            F.Id("Equivalence"), Open, firstRelation, Close, Sp, Land, Sp,
            F.Id("Equivalence"), Open, secondRelation, Close, Sp, Rightarrow, Esc,
            Open, firstRelation, Sp, Subseteq, Sp, secondRelation, Sp,
            Leftrightarrow, Sp, secondAlgebra, Sp, Subseteq, Sp, firstAlgebra, Close, Dot));
    }
}
