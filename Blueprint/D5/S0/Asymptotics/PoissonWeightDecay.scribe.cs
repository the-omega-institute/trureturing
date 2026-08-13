using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class PoissonWeightDecayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed finite weights times geometric listing decay tend to zero.",
        H("Poisson Weight Decay"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("poisson-weight-tends-to-zero"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/PoissonWeightDecay.poisson_weight_tendsto_zero"),
                H("The Poisson weight tends to zero"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Comma, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")),
                    Comma, Sp, F.Id("n"), Sp, Ge, Sp, D(2), Sp, Land, Sp,
                    F.Id("k"), Sp, Le, Sp, F.Id("n"), Sp, Rightarrow, Sp,
                    Left, Open,
                    Left, Open,
                    Forall, Sp, F.Id("A"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(0), Sp, Le, Sp,
                    F.Id("k"), F.Id("A"), F.Id("n"), Caret, Grp(Minus, F.Id("A")),
                    Sp, Le, Sp,
                    F.Id("A"), F.Id("n"), Caret, Grp(D(1), Minus, F.Id("A")),
                    Sp, Le, Sp,
                    F.Id("A"), D(2), Caret, Grp(D(1), Minus, F.Id("A")),
                    Right, Close,
                    Sp, Land, Sp,
                    Lim, Underscore, Grp(F.Id("A"), To, Infty), Sp,
                    F.Id("k"), F.Id("A"), F.Id("n"), Caret, Grp(Minus, F.Id("A")),
                    Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    Forall, Sp, LambdaLower, InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    LambdaLower, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp, Neg,
                    Left, Open, Lim, Underscore, Grp(F.Id("A"), To, Infty), Sp,
                    F.Id("k"), F.Id("A"), F.Id("n"), Caret, Grp(Minus, F.Id("A")),
                    Sp, Eq, Sp, LambdaLower, Right, Close,
                    Right, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For fixed natural n at least two and k at most n, the weight is nonnegative "
                        + "and lies below A times n to the one minus A, which in turn lies below A "
                        + "times two to the one minus A. The real sequence tends to zero, and "
                        + "uniqueness of real limits excludes convergence to any positive lambda.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies tendsto_self_mul_const_pow_of_lt_one and "
                        + "tendsto_nhds_unique. The Lean declaration is a thin wrapper around "
                        + "that geometric-decay theorem. Elementary ordered-field algebra supplies "
                        + "the source's finite envelope; k at most n is used exactly there.")),
                    Paragraph(Text(
                        "This is a partial closure of clause (iv) of the source corollary. Clauses "
                        + "(i) and (ii), the separately represented escape-ratio limit in clause "
                        + "(iii), and the dense-phase exclusion in clause (v) remain outside this "
                        + "deposit."))),
                DescribeRole.Theorem)),
        []));
}
