using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.Designs;

internal sealed class CollisionConservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite projective two-design component identity contracts to exact collision conservation.",
        H("Collision Conservation from a Two-Design Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-design-contraction-gives-collision-conservation"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/Designs/CollisionConservation."
                    + "collision_sum_eq_one_add_purity"),
                H("Two-design contraction gives collision conservation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("trace")), Open, Rho, Close,
                    Sp, Eq, Sp, D(1), Comma, RowBreak,
                    Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
                    F.Id("c"), Comma, Sp, F.Id("d"), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("x")), Sp,
                    F.Id("P"), Underscore, Grp(F.Id("x")),
                    Open, F.Id("a"), Comma, F.Id("b"), Close,
                    F.Id("P"), Underscore, Grp(F.Id("x")),
                    Open, F.Id("c"), Comma, F.Id("d"), Close,
                    Sp, Eq, Sp,
                    DeltaLower, Underscore, Grp(F.Id("a"), F.Id("b")),
                    DeltaLower, Underscore, Grp(F.Id("c"), F.Id("d")),
                    Plus,
                    DeltaLower, Underscore, Grp(F.Id("a"), F.Id("d")),
                    DeltaLower, Underscore, Grp(F.Id("c"), F.Id("b")),
                    Sp, Rightarrow, RowBreak,
                    Sum, Underscore, Grp(F.Id("x")), Sp,
                    Operatorname, Grp(F.Id("trace")), Open,
                    Rho, Sp, F.Id("P"), Underscore, Grp(F.Id("x")), Close,
                    Caret, Grp(D(2)),
                    Sp, Eq, Sp, D(1), Plus,
                    Operatorname, Grp(F.Id("trace")), Open,
                    Rho, Caret, Grp(D(2)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a real finite square matrix of trace one and let P_x be a "
                        + "finite family of real square matrices. If the summed products of their "
                        + "entries obey the displayed projective two-design component identity, "
                        + "then the sum of the squared trace pairings trace(rho P_x) is exactly one "
                        + "plus trace(rho squared).")),
                    Paragraph(Text(
                        "The proof expands both traces, interchanges finite sums, applies the "
                        + "component identity, and contracts its two Kronecker-delta terms. The "
                        + "first term is the square of trace(rho), while the second is "
                        + "trace(rho squared).")),
                    Paragraph(Text(
                        "This theorem proves only the algebraic implication from the supplied "
                        + "two-design identity to collision conservation. It does not construct "
                        + "mutually unbiased bases or prove that any such family satisfies the "
                        + "two-design identity."))),
                DescribeRole.Theorem))));
}
