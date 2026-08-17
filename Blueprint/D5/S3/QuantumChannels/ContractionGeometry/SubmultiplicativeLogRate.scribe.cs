using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.ContractionGeometry;

internal sealed class SubmultiplicativeLogRateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive submultiplicative profile with a finite lower logarithmic bound has a "
            + "unique asymptotic logarithmic rate.",
        H("Unique Logarithmic Rate from Submultiplicativity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("submultiplicative-profile-has-unique-log-rate"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumChannels/ContractionGeometry/SubmultiplicativeLogRate."
                    + "submultiplicative_profile_has_unique_log_rate"),
                H("A submultiplicative profile has a unique logarithmic rate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("eta"), Colon, Sp, Mathbb, Grp(F.Id("N")), To, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    OpenBracket,
                    Open, Forall, Sp, F.Id("n"), Comma, Sp, D(0), Lt, Sp,
                    F.Id("eta"), Open, F.Id("n"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("m"), Comma, Sp, F.Id("n"), Comma, Sp,
                    F.Id("eta"), Open, F.Id("m"), Plus, F.Id("n"), Close,
                    Sp, Leq, Sp,
                    F.Id("eta"), Open, F.Id("m"), Close, Sp, Cdot, Sp,
                    F.Id("eta"), Open, F.Id("n"), Close, Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("BddBelow")), Open,
                    OpenBrace, Frac,
                    Grp(Log, Sp, F.Id("eta"), Open, F.Id("n"), Close),
                    Grp(F.Id("n")), Sp, Mid, Sp, F.Id("n"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), CloseBrace, Close,
                    CloseBracket,
                    Sp, Rightarrow, Sp,
                    Exists, Bang, Sp, F.Id("gamma"), InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                    Frac,
                    Grp(Log, Sp, F.Id("eta"), Open, F.Id("n"), Close),
                    Grp(F.Id("n")), Sp, Eq, Sp, F.Id("gamma"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Taking logarithms converts positivity and submultiplicativity into "
                            + "subadditivity. Pinned Mathlib provides Fekete's lemma as "
                            + "Subadditive.tendsto_lim, which gives the finite limit from the "
                            + "stated lower-bound hypothesis. Uniqueness follows from uniqueness "
                            + "of limits in the real line.")),
                    Paragraph(Text(
                        "This closes only the Fekete-rate clause in source atom remark/27.684. "
                            + "It does not claim the atom's amplitude-damping rate values, "
                            + "depolarizing rate, fixed-point interpretation, or semigroup "
                            + "classification clauses."))),
                DescribeRole.Theorem))));
}
