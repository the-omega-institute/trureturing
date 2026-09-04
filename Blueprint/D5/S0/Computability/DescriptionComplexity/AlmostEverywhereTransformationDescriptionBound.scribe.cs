using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class AlmostEverywhereTransformationDescriptionBoundDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Computability/DescriptionComplexity/"
        + "AlmostEverywhereTransformationDescriptionBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eventually affordable reverse transformations give an almost-everywhere description bound, while a null point prevents a pointwise inference.",
        H("Almost-Everywhere Transformation Description Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("almost-everywhere-reverse-description-bound"),
                DeclarationHandle.Create(
                    Prefix + "almost_everywhere_reverse_description_bound"),
                H("Eventual reverse costs lift to an almost-everywhere complexity bound"),
                StatementSource.FromAuthor(ReverseBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For almost every sample, suppose the reverse transformation is eventually "
                            + "applicable and its minimum description cost plus the fixed compiler "
                            + "overhead is eventually at most b(Q). The compiled transformation "
                            + "then gives K(w_Q) at most K(T(w_Q)) plus b(Q), eventually on the "
                            + "same full-measure set.")),
                    Paragraph(Text(
                        "The proof applies the existing one-way transformation-description theorem "
                            + "to the reverse compiler and intersects the two almost-everywhere, "
                            + "eventually filters. Natural-number linear arithmetic discharges the "
                            + "final weakening from reverse cost plus overhead to b(Q).")),
                    Paragraph(Text(
                        "This is a conditional abstraction of the source's almost-everywhere reverse "
                            + "claim. The repository and pinned Mathlib contain no decimal-to-continued-"
                            + "fraction cylinder comparison, Borel--Bernstein theorem, Lochs theorem, "
                            + "or Dajani--Fieldsteel height law from which the concrete O(log Q) and "
                            + "height-ratio assertions could honestly be derived; those assertions "
                            + "are therefore not made here.")),
                    Paragraph(Text(
                        "Six-route duplicate search covered keyword and symbol variants, digestion "
                            + "indexes, generalized transformation bounds, and all in-flight math "
                            + "branches. The one-way and bidirectional compiler bounds are proper "
                            + "predecessors, while the existing pointwise/a.e. separation concerns "
                            + "fiber factorization rather than eventual description complexity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("almost-everywhere-bound-not-pointwise"),
                DeclarationHandle.Create(
                    Prefix + "almost_everywhere_bound_does_not_imply_pointwise"),
                H("An almost-everywhere bound need not hold pointwise"),
                StatementSource.FromAuthor(NullPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every proposed natural-number bound g, the witness cost equals "
                            + "g(Q) + 1 at zero and equals zero everywhere else. Mathlib's "
                            + "Lebesgue a.e.-not-equal lemma makes the bound hold almost everywhere, "
                            + "whereas every Q explicitly refutes it at the origin.")),
                    Paragraph(Text(
                        "Lebesgue measure is nonzero, and only its null singleton is exceptional. "
                            + "Thus the separation is not obtained from the vacuous zero measure and "
                            + "it rules out upgrading the first theorem to a pointwise conclusion "
                            + "without additional hypotheses."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S0/Computability/DescriptionComplexity/TransformationDescriptionBound"))]));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ReverseBoundFormula()
    {
        Formula sample = F.Id("x"), height = F.Id("Q"), measure = Mu;
        Formula reverse = Apply(F.Id("v"), sample, height);
        Formula source = Apply(F.Id("w"), sample, height);
        Formula transformed = Apply(F.Id("T"), source);
        Formula allowance = Apply(F.Id("b"), height);
        Formula objectComplexity(Formula value) =>
            Apply(F.Id("K"), F.Id("objects"), value);
        Formula transformationComplexity =
            Apply(F.Id("K"), F.Id("transformations"), reverse);
        Formula applicable = Apply(F.Id("applies"), reverse, transformed, source);
        Formula premise = Seq(
            applicable, Sp, Land, Sp,
            transformationComplexity, Sp, Plus, Sp, F.Id("c"), Sp, Leq, Sp, allowance);
        Formula conclusion = Seq(
            objectComplexity(source), Sp, Leq, Sp,
            objectComplexity(transformed), Sp, Plus, Sp, allowance);

        return Disp(Apply(F.Id("AEEventually"), sample, measure, height,
            Seq(premise, Sp, Rightarrow, Sp, conclusion)));
    }

    private static Formula NullPointFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula bound = F.Id("g"), cost = F.Id("cost");
        Formula sample = F.Id("x"), height = F.Id("Q");
        Formula arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
        Formula boundedAt(Formula point) => Seq(
            Apply(cost, point, height), Sp, Leq, Sp, Apply(bound, height));

        return Disp(Seq(
            Forall, Sp, bound, Colon, Sp, arrow(naturals, naturals), Comma, Sp,
            Exists, Sp, cost, Colon, Sp,
            arrow(reals, arrow(naturals, naturals)), Comma, RowBreak, Grp(),
            Apply(F.Id("AE"), sample, F.Id("Lebesgue"),
                Seq(Forall, Sp, height, Comma, Sp, boundedAt(sample))),
            Sp, Land, Sp,
            Forall, Sp, height, Comma, Sp, Neg, Open, boundedAt(D(0)), Close, Dot));
    }
}
