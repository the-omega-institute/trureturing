using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Thermodynamics;

internal sealed class GibbsFenchelYoungDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite Gibbs law satisfies the exact entropy-relative-entropy partition identity.",
        H("The Finite Gibbs Fenchel-Young Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-gibbs-partition-function"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Thermodynamics/GibbsFenchelYoung.gibbsPartition"),
                H("Finite Gibbs partition function"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Z"), Open, F.Id("H"), Close, Colon, Eq,
                    Sum, Underscore, Grp(F.Id("i")),
                    Operatorname, Grp(F.Id("exp")), Open, F.Id("H"), Open, F.Id("i"),
                    Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a real energy profile H on a finite carrier, Z(H) is the sum of " +
                        "exp(H(i)). This sign convention matches the source identity log Tr " +
                        "exp(H), rather than the inverse-temperature convention exp(-H).")),
                    Paragraph(Text(
                        "Every summand is strictly positive. On a nonempty carrier the partition " +
                        "function is therefore strictly positive, so its logarithm and the Gibbs " +
                        "normalization below have nonzero denominators."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-normalized-gibbs-mass"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Thermodynamics/GibbsFenchelYoung.gibbsMass"),
                H("Finite normalized Gibbs mass"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("g"), Underscore, Grp(F.Id("H")), Open, F.Id("i"), Close,
                    Colon, Eq, Frac,
                    Grp(Operatorname, Grp(F.Id("exp")), Open, F.Id("H"), Open,
                        F.Id("i"), Close, Close),
                    Grp(F.Id("Z"), Open, F.Id("H"), Close), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Gibbs reference mass is exp(H(i)) divided by Z(H). The main theorem " +
                        "uses this definition pointwise as the second argument of the repository's " +
                        "existing finite real-valued KL divergence.")),
                    Paragraph(Text(
                        "No second entropy or divergence is introduced. Shannon entropy remains " +
                        "the finite sum owned by MaxEntropy, and KL divergence remains the finite " +
                        "sum owned by ClassicalDPI."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-gibbs-fenchel-young-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Thermodynamics/GibbsFenchelYoung.finite_gibbs_fenchel_young"),
                H("Finite Gibbs Fenchel-Young identity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Rho, Comma, Sp, F.Id("H"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp, D(0), Lt, Sp,
                    Rho, Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Rho, Open, F.Id("i"), Close,
                    Eq, D(1), Close, Sp, Rightarrow, RowBreak,
                    Log, Open, F.Id("Z"), Open, F.Id("H"), Close, Close, Eq,
                    Sum, Underscore, Grp(F.Id("i")), Rho, Open, F.Id("i"), Close,
                    F.Id("H"), Open, F.Id("i"), Close, Plus,
                    F.Id("S"), Open, Rho, Close, Plus,
                    F.Id("D"), Open, Rho, Vert, Sp,
                    F.Id("g"), Underscore, Grp(F.Id("H")), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a strictly positive normalized mass function on a nonempty " +
                        "finite carrier. The logarithm of the Gibbs partition function equals " +
                        "the rho-expectation of H plus Shannon entropy S(rho) plus the finite KL " +
                        "divergence D(rho || g_H).")),
                    Paragraph(Text(
                        "The proof expands each logarithmic ratio with Mathlib's Real.log_div, " +
                        "uses Real.log_exp for the Gibbs numerator, and then sums the pointwise " +
                        "identity. Normalization converts the remaining constant log Z(H) term " +
                        "into exactly one copy of log Z(H).")),
                    Paragraph(Text(
                        "This closes only the finite classical diagonal form of the quantum " +
                        "Fenchel-Young clause in residual appendix E.161. It does not formalize " +
                        "matrix exponentials, density operators, symplectic duality, or the " +
                        "residual's decomposition and monotonicity claims.")),
                    Paragraph(Text(
                        "Strict positivity of rho is an explicit scope restriction. Boundary " +
                        "probability laws with zero masses are not claimed here, even though a " +
                        "support-aware extension can be stated separately."))),
                DescribeRole.Theorem))));
}
