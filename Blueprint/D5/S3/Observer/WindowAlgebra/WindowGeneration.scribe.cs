using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WindowAlgebra;

internal sealed class WindowGenerationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite address-reading clock and cyclic address-writing shift generate every "
            + "observable in their full matrix algebra.",
        H("Finite Window Algebra Generation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("window-read-and-write-generate-the-full-matrix-algebra"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/WindowAlgebra/WindowGeneration."
                        + "window_generators_adjoin_top"),
                H("Window read and write generate the full matrix algebra"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc,
                    Operatorname, Grp(F.Id("alg")), Underscore,
                    Grp(Mathbb, Grp(F.Id("C"))), Open,
                    F.Id("C"), Underscore, Grp(F.Id("M")), Comma, Sp,
                    F.Id("S"), Underscore, Grp(F.Id("M")), Close, Sp,
                    Eq, Sp,
                    Operatorname, Grp(F.Id("Mat")), Underscore,
                    Grp(Mathbb, Grp(F.Id("Z")), Slash, F.Id("M"), Mathbb, Grp(F.Id("Z"))),
                    Open, Mathbb, Grp(F.Id("C")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonzero finite cardinality M, the complex subalgebra generated "
                            + "by the frozen address-reading clock and cyclic address-writing "
                            + "shift is the top subalgebra of the full matrix algebra on ZMod M.")),
                    Paragraph(Text(
                        "The proof first exposes the frozen Fourier construction of each matrix "
                            + "unit through subalgebra closure under powers, scalar multiplication, "
                            + "finite sums, and products. The frozen exact matrix-unit certificate "
                            + "then identifies those generated elements with standard single-entry "
                            + "matrices, and the standard finite matrix-unit expansion supplies every "
                            + "matrix. This is a finite-window statement and does not assert a "
                            + "universal crossed-product identification."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("generation-and-prime-power-factorization-hold-together"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/WindowAlgebra/WindowGeneration."
                        + "window_generated_full_matrix_and_prime_power_factors"),
                H("Generation and prime-power factorization hold together"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc,
                    F.Id("A"), Underscore, Grp(F.Id("M")), Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("Mat")), Underscore,
                    Grp(Mathbb, Grp(F.Id("Z")), Slash, F.Id("M"), Mathbb, Grp(F.Id("Z"))),
                    Open, Mathbb, Grp(F.Id("C")), Close, Sp,
                    Land, Sp,
                    Operatorname, Grp(F.Id("bijective")), Open,
                    F.Id("F"), Underscore, Grp(F.Id("M")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The generated-algebra equality is paired with the existing canonical "
                            + "prime-power tensor factorization. The conjunction closes both clauses "
                            + "for the same nonzero window cardinality without reproving or weakening "
                            + "the frozen factorization equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-two-address-window-generates-a-nonzero-off-diagonal-observable"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/WindowAlgebra/WindowGeneration."
                        + "window_two_off_diagonal_generated_witness"),
                H("The two-address window generates a nonzero off-diagonal observable"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("E"), Underscore, Grp(D(0), Comma, D(1)), Sp,
                    InMacro, Sp,
                    Operatorname, Grp(F.Id("alg")), Underscore,
                    Grp(Mathbb, Grp(F.Id("C"))), Open,
                    F.Id("C"), Underscore, Grp(D(2)), Comma, Sp,
                    F.Id("S"), Underscore, Grp(D(2)), Close, Sp,
                    Land, Sp,
                    F.Id("E"), Underscore, Grp(D(0), Comma, D(1)), Sp,
                    Neq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At window cardinality two, the standard single-entry matrix in row zero "
                            + "and column one belongs to the generated algebra and is nonzero. "
                            + "This explicitly exhibits an off-diagonal generated observable, so "
                            + "the result is not witnessed by scalars, diagonal matrices, or an "
                            + "empty generator family."))),
                DescribeRole.Theorem))));
}
