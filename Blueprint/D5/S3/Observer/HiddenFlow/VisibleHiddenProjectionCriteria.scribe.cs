using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class VisibleHiddenProjectionCriteriaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complementary projections characterize invariant, coinvariant, and reducing subspaces, with a concrete asymmetric leakage witness.",
        H("Visible-Hidden Projection Criteria"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hidden-projection-is-the-complement-of-visible-projection"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria."
                        + "hiddenProjection_eq_one_sub_visibleProjection"),
                H("The hidden projection is identity minus the visible projection"),
                StatementSource.FromAuthor(HiddenProjectionComplementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For complementary subspaces V and R with a chosen complement witness, "
                            + "the projection onto R along V is the identity operator minus the "
                            + "projection onto V along R.")),
                    Paragraph(Text(
                        "This complement identity supplies the algebraic relation between the two "
                            + "projections used in the invariant and reducing criteria below."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("visible-invariance-is-the-vanishing-hidden-visible-block"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria."
                        + "visible_invariant_iff_hidden_visible_block_eq_zero"),
                H("Visible invariance is equivalent to a zero hidden-visible block"),
                StatementSource.FromAuthor(VisibleInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an endomorphism T and a complementary decomposition into visible V "
                            + "and hidden R, V is invariant exactly when the hidden projection "
                            + "after T after the visible projection is the zero map.")),
                    Paragraph(Text(
                        "The block vanishes because T sends every vector of V back into V; "
                            + "conversely, a zero hidden component forces that invariance."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("hidden-invariance-is-the-vanishing-visible-hidden-block"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria."
                        + "hidden_invariant_iff_visible_hidden_block_eq_zero"),
                H("Hidden invariance is equivalent to a zero visible-hidden block"),
                StatementSource.FromAuthor(HiddenInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same complementary decomposition, the hidden subspace R is "
                            + "invariant under T exactly when the visible projection after T "
                            + "after the hidden projection is the zero map.")),
                    Paragraph(Text(
                        "Thus the visible component detects precisely the failure of T to keep "
                            + "vectors from R inside R."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("reducing-decomposition-is-equivalent-to-two-zero-cross-blocks"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria."
                        + "reducing_iff_cross_projection_blocks_eq_zero"),
                H("A reducing decomposition is exactly two vanishing cross blocks"),
                StatementSource.FromAuthor(ReducingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A complementary decomposition reduces T when both V and R are invariant "
                            + "under T. Equivalently, both cross-component maps vanish: the "
                            + "visible-after-T-after-hidden block and the hidden-after-T-after-visible "
                            + "block are zero.")),
                    Paragraph(Text(
                        "The criterion packages the two one-sided invariance equivalences into a "
                            + "single characterization of complete absence of visible-hidden "
                            + "leakage."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("visible-descent-does-not-rule-out-hidden-leakage"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria."
                        + "visible_descent_does_not_prevent_hidden_leakage"),
                H("A vanishing visible-hidden direction can coexist with hidden leakage"),
                StatementSource.FromAuthor(LeakageWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the two-coordinate rational space, the visible and hidden coordinate "
                            + "projections select the first and second axes. The square-zero update "
                            + "sends the visible first coordinate into the hidden second one.")),
                    Paragraph(Text(
                        "The visible-after-update-after-hidden composition is zero, while the "
                            + "opposite hidden-after-update-after-visible composition is nonzero. "
                            + "Therefore a one-sided visible descent test does not exclude hidden "
                            + "leakage."))),
                DescribeRole.Lemma))));

    private static Formula HiddenProjection(Formula visible, Formula hidden, Formula witness) =>
        Call("hiddenProjection", visible, hidden, witness);

    private static Formula VisibleProjection(Formula visible, Formula hidden, Formula witness) =>
        Call("visibleProjection", visible, hidden, witness);

    private static Formula IsInvariant(Formula map, Formula subspace) =>
        Call("IsInvariant", map, subspace);

    private static Formula IsReducing(Formula map, Formula visible, Formula hidden) =>
        Call("IsReducing", map, visible, hidden);

    private static Formula Compose(Formula first, Formula middle, Formula last) =>
        Seq(first, Sp, Circ, Sp, middle, Sp, Circ, Sp, last);

    private static Formula HiddenProjectionComplementFormula()
    {
        Formula visible = F.Id("V");
        Formula hidden = F.Id("R");
        Formula witness = F.Id("h");
        Formula identity = F.Id("I");

        return Disp(Seq(
            HiddenProjection(visible, hidden, witness), Sp, Eq, Sp, identity, Sp, Minus, Sp,
            VisibleProjection(visible, hidden, witness), Dot));
    }

    private static Formula VisibleInvariantFormula()
    {
        Formula map = F.Id("T");
        Formula visible = F.Id("V");
        Formula hidden = F.Id("R");
        Formula witness = F.Id("h");

        return Disp(Seq(
            IsInvariant(map, visible), Sp, Iff, Sp,
            Compose(
                HiddenProjection(visible, hidden, witness),
                map,
                VisibleProjection(visible, hidden, witness)),
            Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula HiddenInvariantFormula()
    {
        Formula map = F.Id("T");
        Formula visible = F.Id("V");
        Formula hidden = F.Id("R");
        Formula witness = F.Id("h");

        return Disp(Seq(
            IsInvariant(map, hidden), Sp, Iff, Sp,
            Compose(
                VisibleProjection(visible, hidden, witness),
                map,
                HiddenProjection(visible, hidden, witness)),
            Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula ReducingFormula()
    {
        Formula map = F.Id("T");
        Formula visible = F.Id("V");
        Formula hidden = F.Id("R");
        Formula witness = F.Id("h");

        Formula visibleHidden = Compose(
            VisibleProjection(visible, hidden, witness),
            map,
            HiddenProjection(visible, hidden, witness));
        Formula hiddenVisible = Compose(
            HiddenProjection(visible, hidden, witness),
            map,
            VisibleProjection(visible, hidden, witness));

        return Disp(Seq(
            IsReducing(map, visible, hidden), Sp, Iff, Sp,
            Open, visibleHidden, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            hiddenVisible, Sp, Eq, Sp, D(0), Close, Dot));
    }

    private static Formula LeakageWitnessFormula()
    {
        Formula visibleProjection = Call("visibleCoordinateProjection");
        Formula hiddenProjection = Call("hiddenCoordinateProjection");
        Formula leak = Call("visibleToHiddenLeak");

        return Disp(Seq(
            Compose(visibleProjection, leak, hiddenProjection), Sp, Eq, Sp, D(0), Sp,
            Land, Sp,
            Compose(hiddenProjection, leak, visibleProjection), Sp, Neq, Sp, D(0), Dot));
    }
}
