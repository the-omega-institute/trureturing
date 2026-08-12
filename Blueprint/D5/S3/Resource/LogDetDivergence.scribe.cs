using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class LogDetDivergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The log-determinant barrier and divergence satisfy self-vanishing and the proved Bregman identity with its positive trace remainder.",
        H("The Log-Determinant Divergence"),
        Blocks(
            Paragraph(Text(
                "For finite complex matrices, the barrier height of a positive definite matrix "
                + "is minus the logarithm of the real part of its determinant. The log-det "
                + "divergence of rho from sigma is the real trace of sigma inverse times rho, "
                + "minus the logarithm of the real part of that product's determinant, minus "
                + "the matrix dimension. The source atom cone-v1 definition/11.1 identifies "
                + "this second quantity as the Bregman divergence of the first.")),
            Paragraph(Text(
                "The Bregman link is proved here, and the sign is essential. Because the barrier "
                + "is minus a log determinant, its gradient at sigma is minus sigma inverse. "
                + "Consequently, subtracting the gradient pairing in the Bregman remainder gives "
                + "a plus sign in front of the trace of sigma inverse times rho minus sigma. The "
                + "identity holds with this plus sign; the kernel-checked formula rules out the "
                + "otherwise plausible sign reversal.")),
            Paragraph(Text(
                "Nonnegativity is NOT established in this module. The precise obstacle is that "
                + "sigma inverse times rho is not Hermitian in general, so an eigenvalue argument "
                + "must first pass to the congruence sigma to the minus one half times rho times "
                + "sigma to the minus one half. A route was located but not taken: mathlib supplies "
                + "the square root through the continuous functional calculus CFC.sqrt, not through "
                + "a bespoke Matrix.sqrt. Matrix.PosDef.eigenvalues_pos and "
                + "Matrix.IsHermitian.det_eq_prod_eigenvalues, both in "
                + "Mathlib/Analysis/Matrix/PosDef.lean rather than the similarly named "
                + "Mathlib/LinearAlgebra path where a search naturally lands, then give the "
                + "eigenvalue sum, and Real.log_le_sub_one_of_pos closes it termwise.")),
            Paragraph(Text(
                "These are matrix quantities. No physical or information-theoretic interpretation "
                + "in terms of states, channels, or distinguishability is asserted.")),
            Describe.Lean(
                DescribeId.Create("barrier-height-is-minus-log-determinant"),
                DeclarationHandle.Create("D5/S3/Resource/LogDetDivergence.barrierHeight"),
                H("Barrier height is minus log determinant"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("barrierHeight")), F.Open,
                    F.Rho, F.Close, F.Eq, F.Minus, F.Log, F.Sp, F.Open,
                    F.Re, F.Open, F.Operatorname, F.Grp(F.Id("det")), F.Open,
                    F.Rho, F.Close, F.Close, F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The barrier height takes the negative real logarithm of the determinant's "
                    + "real part. Positive definiteness is imposed by the theorems that use this "
                    + "total definition, not by the definition itself."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("log-det-divergence-is-trace-minus-log-determinant-minus-dimension"),
                DeclarationHandle.Create("D5/S3/Resource/LogDetDivergence.logDetDivergence"),
                H("Log-det divergence is trace minus log determinant minus dimension"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("logDetDivergence")), F.Open,
                    F.Rho, F.Comma, F.Sp, F.SigmaLower, F.Close, F.Eq,
                    F.Re, F.Open, F.Operatorname, F.Grp(F.Id("tr")), F.Open,
                    F.SigmaLower, F.Caret, F.Grp(F.Minus, F.D(1)), F.Sp,
                    F.Rho, F.Close, F.Close, F.Minus, F.Log, F.Sp, F.Open,
                    F.Re, F.Open, F.Operatorname, F.Grp(F.Id("det")), F.Open,
                    F.SigmaLower, F.Caret, F.Grp(F.Minus, F.D(1)), F.Sp,
                    F.Rho, F.Close, F.Close, F.Close, F.Minus, F.Id("d")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The divergence is the real part of the trace of sigma inverse times rho, "
                    + "minus the real logarithm of the real part of its determinant, minus the "
                    + "cardinality of the finite matrix index type."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("positive-definite-matrices-have-zero-self-divergence"),
                DeclarationHandle.Create("D5/S3/Resource/LogDetDivergence.logDetDivergence_self"),
                H("Positive definite matrices have zero self-divergence"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("n"), F.Esc,
                    F.OpenBracket, F.Operatorname, F.Grp(F.Id("Fintype")),
                    F.Open, F.Id("n"), F.Close, F.CloseBracket, F.Sp,
                    F.OpenBracket, F.Operatorname, F.Grp(F.Id("DecidableEq")),
                    F.Open, F.Id("n"), F.Close, F.CloseBracket, F.Comma, F.Sp,
                    F.Forall, F.Sp, F.Rho, F.Colon, F.Sp,
                    F.Operatorname, F.Grp(F.Id("Matrix")), F.Open,
                    F.Id("n"), F.Comma, F.Sp, F.Id("n"), F.Comma, F.Sp,
                    F.Mathbb, F.Grp(F.Id("C")), F.Close, F.Comma, F.Sp,
                    F.Operatorname, F.Grp(F.Id("PosDef")), F.Open,
                    F.Rho, F.Close, F.Sp, F.Rightarrow, F.Sp,
                    F.Operatorname, F.Grp(F.Id("logDetDivergence")), F.Open,
                    F.Rho, F.Comma, F.Sp, F.Rho, F.Close, F.Eq, F.D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A positive definite matrix is invertible, so rho inverse times rho is the "
                    + "identity. Its trace is the dimension, its determinant is one, and the "
                    + "resulting log-det divergence is zero."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("log-det-divergence-is-the-barrier-bregman-remainder"),
                DeclarationHandle.Create("D5/S3/Resource/LogDetDivergence.barrier_bregman_link"),
                H("Log-det divergence is the barrier Bregman remainder"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Begin, F.Grp(F.Id("gathered")),
                    F.Forall, F.Sp, F.Id("n"), F.Esc,
                    F.OpenBracket, F.Operatorname, F.Grp(F.Id("Fintype")),
                    F.Open, F.Id("n"), F.Close, F.CloseBracket, F.Sp,
                    F.OpenBracket, F.Operatorname, F.Grp(F.Id("DecidableEq")),
                    F.Open, F.Id("n"), F.Close, F.CloseBracket, F.Comma, F.Sp,
                    F.Forall, F.Sp, F.Rho, F.Comma, F.Sp, F.SigmaLower,
                    F.Colon, F.Sp, F.Operatorname, F.Grp(F.Id("Matrix")), F.Open,
                    F.Id("n"), F.Comma, F.Sp, F.Id("n"), F.Comma, F.Sp,
                    F.Mathbb, F.Grp(F.Id("C")), F.Close, F.Comma, F.RowBreak,
                    F.Open, F.Operatorname, F.Grp(F.Id("PosDef")), F.Open,
                    F.Rho, F.Close, F.Sp, F.Land, F.Sp,
                    F.Operatorname, F.Grp(F.Id("PosDef")), F.Open,
                    F.SigmaLower, F.Close, F.Close, F.Sp, F.Rightarrow, F.RowBreak,
                    F.Operatorname, F.Grp(F.Id("logDetDivergence")), F.Open,
                    F.Rho, F.Comma, F.Sp, F.SigmaLower, F.Close, F.Eq,
                    F.Operatorname, F.Grp(F.Id("barrierHeight")), F.Open,
                    F.Rho, F.Close, F.Minus,
                    F.Operatorname, F.Grp(F.Id("barrierHeight")), F.Open,
                    F.SigmaLower, F.Close, F.Plus, F.RowBreak,
                    F.Re, F.Open, F.Operatorname, F.Grp(F.Id("tr")), F.Open,
                    F.SigmaLower, F.Caret, F.Grp(F.Minus, F.D(1)), F.Sp,
                    F.Open, F.Rho, F.Minus, F.SigmaLower, F.Close,
                    F.Close, F.Close, F.Dot,
                    F.End, F.Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive definite rho and sigma, determinant multiplicativity and the "
                    + "real logarithm laws identify the log terms, while expanding the trace "
                    + "turns the identity contribution into the dimension. The remainder has a "
                    + "plus sign before the trace term, exactly as dictated by the negative "
                    + "gradient of the barrier."))),
                DescribeRole.Theorem
            ))));
}
