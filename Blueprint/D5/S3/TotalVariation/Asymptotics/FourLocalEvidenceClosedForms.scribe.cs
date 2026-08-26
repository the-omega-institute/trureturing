using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class FourLocalEvidenceClosedFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four symmetric Bernoulli local evidence quantities have closed forms on the interior "
            + "bias domain.",
        H("Four Local Evidence Closed Forms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetric-bernoulli-total-variation-closed-form"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms."
                        + "total_variation_closed_form"),
                H("Symmetric Bernoulli total variation closed form"),
                StatementSource.FromAuthor(InteriorFormula(TvFormula(Delta))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The repository defines total variation as one half of the finite L1 distance. "
                        + "For the two Bool coordinates, the absolute gaps are twice the absolute "
                        + "bias, so the result is 2|delta|. The algebraic statement is stronger "
                        + "than the probability-domain interpretation and needs no sign "
                        + "hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-bernoulli-bhattacharyya-closed-form"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms."
                        + "bhattacharyya_closed_form"),
                H("Symmetric Bernoulli Bhattacharyya affinity closed form"),
                StatementSource.FromAuthor(InteriorFormula(AffinityFormula(Delta))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here rho is read as Bhattacharyya affinity, not a correlation coefficient. "
                        + "The two equal square-root products reduce to twice the square root of "
                        + "(one half plus delta)(one half minus delta), which is the displayed "
                        + "square root. The strict interior hypothesis keeps both masses "
                        + "nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-bernoulli-hellinger-closed-form"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms."
                        + "hellinger_sq_closed_form"),
                H("Symmetric Bernoulli squared Hellinger closed form"),
                StatementSource.FromAuthor(InteriorFormula(HellingerFormula(Delta))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen hellingerSq normalization is the unhalved squared Hellinger "
                        + "distance. Its normalized bridge is H^2 = 2(1 - rho), and the preceding "
                        + "affinity calculation supplies rho. Nonnegativity and normalization of "
                        + "both Bool laws are discharged from |delta| < 1/2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-bernoulli-kl-closed-form"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms."
                        + "kl_divergence_closed_form"),
                H("Symmetric Bernoulli KL divergence closed form"),
                StatementSource.FromAuthor(InteriorFormula(KlFormula(Delta))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The repository's finite real-valued klDivergence uses Real.log, so this is "
                        + "the natural-log, or nats, convention. Expanding the two Bool summands, "
                        + "using log of an inverse, and collecting coefficients gives the stated "
                        + "symmetric logarithmic ratio. Strict positivity follows from the "
                        + "interior "
                        + "bias hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-bernoulli-zero-bias-degenerate-case"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms."
                        + "zero_bias_degenerate_case"),
                H("Zero bias gives identical-law evidence values"),
                StatementSource.FromAuthor(ZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At delta = 0 the positive and negative laws coincide. The four quantities "
                        + "therefore evaluate to TV = 0, affinity = 1, squared Hellinger distance "
                        + "= 0, and KL = 0 under the repository's fixed normalizations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-bernoulli-negative-bias-degenerate-case"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms."
                        + "negative_bias_degenerate_case"),
                H("Negative bias satisfies all four closed forms"),
                StatementSource.FromAuthor(NegativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The concrete interior point delta = -1/4 checks the sign audit. The TV "
                        + "absolute value changes sign correctly, while affinity, squared "
                        + "Hellinger distance, and the symmetric KL expression remain valid."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-bernoulli-strict-bias-bound-is-necessary"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms."
                        + "strict_bias_bound_is_necessary"),
                H("The strict bias bound excludes a zero reference mass"),
                StatementSource.FromAuthor(BoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At delta = 1/2 the negative-bias law assigns zero mass to true, so strict "
                        + "positivity needed for the ordinary finite-KL reading fails. The frozen "
                        + "real-valued klDivergence totalizes the zero-denominator expression "
                        + "to 0; "
                        + "this is recorded explicitly and is not claimed to be an extended-real "
                        + "infinite divergence."))),
                DescribeRole.Theorem))));

    private static readonly Formula Delta = DeltaLower;

    private static Formula Law(Formula symbol, Formula delta) =>
        new Formula.Subscript(symbol, delta);

    private static Formula Interior(Formula delta) =>
        Seq(new Formula.Absolute(delta), Sp, Lt, Sp, Frac, Grp(D(1)), Grp(D(2)));

    private static Formula InteriorFormula(Formula conclusion) =>
        Disp(Seq(Forall, Sp, Delta, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Interior(Delta), Sp, Rightarrow, Sp, conclusion, Dot));

    private static Formula TvFormula(Formula delta) =>
        Seq(Operatorname, Grp(F.Id("totalVariation")), Open,
            Law(F.Id("P"), delta), Comma, Sp, Law(F.Id("Q"), delta), Close,
            Eq, Sp, D(2), Sp, new Formula.Absolute(delta));

    private static Formula AffinityFormula(Formula delta) =>
        Seq(Operatorname, Grp(F.Id("bhattacharyya")), Open,
            Law(F.Id("P"), delta), Comma, Sp, Law(F.Id("Q"), delta), Close,
            Eq, Sp, Sqrt, Grp(Seq(D(1), Sp, Minus, Sp, D(4), Sp, delta,
                Caret, Grp(D(2)))));

    private static Formula HellingerFormula(Formula delta) =>
        Seq(Operatorname, Grp(F.Id("hellingerSq")), Open,
            Law(F.Id("P"), delta), Comma, Sp, Law(F.Id("Q"), delta), Close,
            Eq, Sp, D(2), Sp, Open, D(1), Sp, Minus, Sp, Sqrt, Grp(Seq(
                D(1), Sp, Minus, Sp, D(4), Sp, delta, Caret, Grp(D(2)))), Close);

    private static Formula KlFormula(Formula delta) =>
        Seq(Operatorname, Grp(F.Id("klDivergence")), Open,
            Law(F.Id("P"), delta), Comma, Sp, Law(F.Id("Q"), delta), Close,
            Eq, Sp, D(2), Sp, delta, Sp, Log, Sp, Frac,
            Grp(Seq(D(1), Sp, Plus, Sp, D(2), Sp, delta)),
            Grp(Seq(D(1), Sp, Minus, Sp, D(2), Sp, delta)));

    private static Formula ZeroFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("totalVariation")), Open,
            Law(F.Id("P"), D(0)), Comma, Sp, Law(F.Id("Q"), D(0)), Close, Eq, Sp, D(0), Sp,
            Land, Sp, Operatorname, Grp(F.Id("bhattacharyya")), Open,
            Law(F.Id("P"), D(0)), Comma, Sp, Law(F.Id("Q"), D(0)), Close, Eq, Sp, D(1), Sp,
            Land, Sp, Operatorname, Grp(F.Id("hellingerSq")), Open,
            Law(F.Id("P"), D(0)), Comma, Sp, Law(F.Id("Q"), D(0)), Close, Eq, Sp, D(0), Sp,
            Land, Sp, Operatorname, Grp(F.Id("klDivergence")), Open,
            Law(F.Id("P"), D(0)), Comma, Sp, Law(F.Id("Q"), D(0)), Close, Eq, Sp, D(0), Dot));

    private static Formula NegativeFormula() =>
        Disp(Seq(
            Interior(NegQuarter), Sp, Land, Sp, TvFormula(NegQuarter), Sp, Land, Sp,
            AffinityFormula(NegQuarter), Sp, Land, Sp, HellingerFormula(NegQuarter), Sp, Land,
            Sp, KlFormula(NegQuarter), Dot));

    private static Formula BoundaryFormula() =>
        Disp(Seq(
            Law(F.Id("Q"), Half), Open, F.Id("true"), Close, Eq, Sp, D(0), Sp, Land, Sp,
            new Formula.Not(Seq(Forall, Sp, F.Id("b"), Colon, Sp, F.Id("Bool"), Comma, Sp,
                D(0), Lt, Sp, Law(F.Id("Q"), Half), Open, F.Id("b"), Close)), Sp, Land, Sp,
            Operatorname, Grp(F.Id("klDivergence")), Open,
            Law(F.Id("P"), Half), Comma, Sp, Law(F.Id("Q"), Half), Close, Eq, Sp, D(0), Dot));

    private static readonly Formula Half = Seq(Frac, Grp(D(1)), Grp(D(2)));

    private static readonly Formula NegQuarter =
        Seq(Minus, Sp, Frac, Grp(D(1)), Grp(D(4)));
}
