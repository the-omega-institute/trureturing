using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Bogoliubov;

internal sealed class HardyBlockConservationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Bogoliubov/HardyBlockConservation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardy compression and leakage conserve the projected input norm.",
        H("Hardy Block Conservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hardy-blocks-conserve-the-input-projection"),
                DeclarationHandle.Create(Prefix + "hardy_block_conservation"),
                H("Hardy blocks conserve the input projection"),
                StatementSource.FromAuthor(ConservationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P be a finite-dimensional Hermitian idempotent and U an isometry. "
                            + "The compressed block T = PUP and complementary leakage block "
                            + "H = (I-P)UP satisfy the exact Gram identity T* T + H* H = P.")),
                    Paragraph(Text(
                        "The proof uses the conjugate-transpose product, subtraction, and identity "
                            + "laws from Mathlib, then the projection and isometry hypotheses.")),
                    Paragraph(Text(
                        "The source writes I on the right while displaying the blocks as ambient "
                            + "operators. In that ambient representation the correct right side is "
                            + "P; I is recovered only after restricting inputs to the "
                            + "range of P."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conservation-is-the-identity-on-projected-inputs"),
                DeclarationHandle.Create(
                    Prefix + "hardy_block_conservation_on_projected_input"),
                H("Conservation is the identity on projected inputs"),
                StatementSource.FromAuthor(ProjectedInputFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If Pv = v, applying the ambient Gram sum to v gives v. This is the precise "
                        + "finite-dimensional version of the source identity on the selected "
                        + "Hardy input sector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-proper-projection-refutes-the-ambient-identity"),
                DeclarationHandle.Create(Prefix + "ambient_identity_rhs_counterexample"),
                H("A proper projection refutes the ambient identity"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first-coordinate projection on C^2 is nonzero, differs from I, is "
                        + "Hermitian and idempotent, and with U = I makes the Gram sum equal P "
                        + "rather than I. This is a concrete counterexample to the unqualified "
                        + "ambient formulation."))),
                DescribeRole.Theorem))));

    private static Formula Adjoint(Formula value) => Seq(value, Caret, Grp(Star));

    private static Formula GramSum(Formula compression, Formula leakage) => Seq(
        Adjoint(compression), compression, Sp, Plus, Sp,
        Adjoint(leakage), leakage);

    private static Formula ConservationFormula()
    {
        Formula projection = F.Id("P"), isometry = F.Id("U");
        Formula compression = F.Id("T"), leakage = F.Id("H"), identity = F.Id("I");

        return Disp(Seq(
            compression, Sp, Eq, Sp, projection, isometry, projection, Comma, Sp,
            leakage, Sp, Eq, Sp, Grp(identity, Sp, Minus, Sp, projection),
            isometry, projection, Comma, Esc,
            Adjoint(projection), Sp, Eq, Sp, projection, Sp, Land, Sp,
            projection, Caret, Grp(D(2)), Sp, Eq, Sp, projection, Sp, Land, Sp,
            Adjoint(isometry), isometry, Sp, Eq, Sp, identity,
            Sp, Rightarrow, Sp, GramSum(compression, leakage), Sp, Eq, Sp,
            projection, Dot));
    }

    private static Formula ProjectedInputFormula()
    {
        Formula projection = F.Id("P"), vector = F.Id("v");
        Formula compression = F.Id("T"), leakage = F.Id("H");

        return Disp(Seq(
            projection, vector, Sp, Eq, Sp, vector, Sp, Rightarrow, Sp,
            Grp(GramSum(compression, leakage)), vector, Sp, Eq, Sp, vector, Dot));
    }

    private static Formula CounterexampleFormula()
    {
        Formula projection = F.Id("P"), compression = F.Id("T");
        Formula leakage = F.Id("H"), identity = F.Id("I");
        Formula matrices = Seq(Mathcal, Grp(F.Id("M")), Underscore, Grp(D(2)),
            Open, Mathbb, Grp(F.Id("C")), Close);

        return Disp(Seq(
            Exists, Sp, projection, Comma, Sp, compression, Comma, Sp, leakage,
            Sp, InMacro, Sp, matrices, Comma, Esc,
            projection, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            projection, Sp, Neq, Sp, identity, Sp, Land, Sp,
            Adjoint(projection), Sp, Eq, Sp, projection, Sp, Land, Sp,
            projection, Caret, Grp(D(2)), Sp, Eq, Sp, projection, Sp, Land, Sp,
            compression, Sp, Eq, Sp, projection, identity, projection, Sp, Land, Sp,
            leakage, Sp, Eq, Sp, Grp(identity, Sp, Minus, Sp, projection),
            identity, projection, Sp, Land, Sp,
            GramSum(compression, leakage), Sp, Eq, Sp, projection, Sp, Land, Sp,
            GramSum(compression, leakage), Sp, Neq, Sp, identity, Dot));
    }
}
