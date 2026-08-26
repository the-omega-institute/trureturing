using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class IndexDoesNotImplyCausalIndependenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct prime addresses can share one mechanism, while separate noise coordinates "
            + "supply the independent control.",
        H("Index Does Not Imply Causal Independence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("causally-independent"),
                DeclarationHandle.Create(Prefix + "CausallyIndependent"),
                H("Crosswise recombination of realized readout values"),
                StatementSource.FromAuthor(CausalIndependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two readouts satisfy the named predicate when every left value and "
                        + "right value realized by possibly different latent states can be "
                        + "realized together by one latent state. This is the minimal "
                        + "fiber-transversality interpretation selected for this module."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shared-noise-module"),
                DeclarationHandle.Create(Prefix + "sharedNoiseModule"),
                H("Every address reads one supplied exogenous mechanism"),
                StatementSource.FromAuthor(SharedNoiseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The address parameter changes only the module's address. Its value is "
                        + "the same supplied noise function at every address, making "
                        + "mechanism sharing explicit rather than inferred from a label."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coordinate-noise-module"),
                DeclarationHandle.Create(Prefix + "coordinateNoiseModule"),
                H("Each address reads its own exogenous coordinate"),
                StatementSource.FromAuthor(CoordinateNoiseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The control family reads coordinate p from a natural-number-indexed "
                        + "noise state. Distinct addresses can therefore be assigned values "
                        + "independently by changing one coordinate and preserving another."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("distinct-prime-indices-can-share-exogenous-noise"),
                DeclarationHandle.Create(
                    Prefix + "distinct_prime_indices_can_share_exogenous_noise"),
                H("Distinct prime addresses can remain causally coupled"),
                StatementSource.FromAuthor(SharedNoiseCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the prime addresses two and three, but let both modules expose "
                            + "the identity function on one Boolean exogenous variable. "
                            + "False from one latent state cannot be combined with true "
                            + "from another, so crosswise recombination fails.")),
                    Paragraph(Text(
                        "Primality certifies that the witnesses are prime addresses but is "
                            + "not used by the coupling argument. The same family of source "
                            + "phenomena also includes directed edges, common environments, "
                            + "shared apparatus disturbance, and other coupled mechanisms.")),
                    Paragraph(Text(
                        "The strict joint-kernel refinement in SamePrimeScaleRedundancy is "
                            + "about discrimination, not generation. It has no premise or "
                            + "conclusion about exogenous noise and does not contradict this "
                            + "mechanism-level counterexample."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "distinct-indices-imply-independence-for-coordinate-noise"),
                DeclarationHandle.Create(
                    Prefix + "distinct_indices_imply_independence_for_coordinate_noise"),
                H("Distinct coordinate-noise addresses are independent"),
                StatementSource.FromAuthor(CoordinateNoiseControlFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Given two latent noise states, overwrite coordinate p of the second "
                        + "with coordinate p of the first. The left value is then retained, "
                        + "and p unequal to q ensures that the right coordinate is unchanged. "
                        + "This is the required positive control."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "index-distinctness-is-necessary-for-coordinate-noise"),
                DeclarationHandle.Create(
                    Prefix + "index_distinctness_is_necessary_for_coordinate_noise"),
                H("Coordinate-noise independence needs unequal addresses"),
                StatementSource.FromAuthor(DistinctnessNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the single prime address two, both readouts inspect the same Boolean "
                        + "coordinate. False and true cannot occur there simultaneously. "
                        + "This concrete theorem proves the control theorem's sole hypothesis "
                        + "necessary and also audits the equal-index mechanism."))),
                DescribeRole.Lemma))));

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(function), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Indexed(Formula symbol, Formula index) =>
        new Formula.Subscript(symbol, index);

    private static Formula EvaluateIndexed(
        Formula symbol,
        Formula index,
        Formula argument) => Seq(Indexed(symbol, index), Open, argument, Close);

    private static Formula CausalIndependenceFormula()
    {
        Formula left = F.Id("L");
        Formula right = F.Id("R");
        Formula eLeft = Indexed(F.Id("e"), F.Id("L"));
        Formula eRight = Indexed(F.Id("e"), F.Id("R"));
        Formula e = F.Id("e");
        return Disp(Seq(
            Call(F.Id("CI"), left, right), Sp, Iff, Sp,
            Forall, Sp, eLeft, Comma, Sp, eRight, Comma, Sp,
            Exists, Sp, e, Comma, Sp,
            Call(left, e), Sp, Eq, Sp, Call(left, eLeft), Sp, Land, Sp,
            Call(right, e), Sp, Eq, Sp, Call(right, eRight), Dot));
    }

    private static Formula SharedNoiseFormula()
    {
        Formula p = F.Id("p");
        Formula e = F.Id("e");
        return Disp(Seq(
            Forall, Sp, p, Comma, Sp, e, Comma, Sp,
            EvaluateIndexed(F.Id("K"), p, e), Sp, Eq, Sp,
            Call(F.Id("h"), e), Dot));
    }

    private static Formula CoordinateNoiseFormula()
    {
        Formula p = F.Id("p");
        Formula e = F.Id("e");
        return Disp(Seq(
            Forall, Sp, p, Comma, Sp, e, Comma, Sp,
            EvaluateIndexed(F.Id("C"), p, e), Sp, Eq, Sp,
            Seq(e, Open, p, Close), Dot));
    }

    private static Formula SharedNoiseCounterexampleFormula()
    {
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula e = F.Id("e");
        Formula k = F.Id("K");
        Formula identityAtBoth = Seq(
            Forall, Sp, e, Comma, Sp,
            EvaluateIndexed(k, p, e), Sp, Eq, Sp, e, Sp, Land, Sp,
            EvaluateIndexed(k, q, e), Sp, Eq, Sp, e);
        return Disp(Seq(
            Exists, Sp, p, Comma, Sp, q, Sp, InMacro, Sp, F.Id("Primes"), Comma,
            RowBreak, Grp(), p, Sp, Neq, Sp, q, Sp, Land, Sp,
            Grp(identityAtBoth), Sp, Land, Sp,
            Neg, Call(F.Id("CI"), Indexed(k, p), Indexed(k, q)), Dot));
    }

    private static Formula CoordinateNoiseControlFormula()
    {
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula c = F.Id("C");
        return Disp(Seq(
            Forall, Sp, p, Comma, Sp, q, Sp, InMacro, Sp,
            Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            p, Sp, Neq, Sp, q, Sp, Rightarrow, Sp,
            Call(F.Id("CI"), Indexed(c, p), Indexed(c, q)), Dot));
    }

    private static Formula DistinctnessNecessityFormula()
    {
        Formula c = F.Id("C");
        Formula two = D(2);
        return Disp(Seq(
            Call(F.Id("Prime"), two), Sp, Land, Sp,
            Neg, Call(F.Id("CI"), Indexed(c, two), Indexed(c, two)), Dot));
    }
}
