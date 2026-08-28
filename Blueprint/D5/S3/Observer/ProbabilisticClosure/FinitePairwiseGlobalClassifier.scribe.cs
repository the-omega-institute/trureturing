using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class FinitePairwiseGlobalClassifierDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite pairwise state separation closes to one finite joint classifier, "
            + "and point readouts on the naturals show that finiteness is sharp.",
        H("Finite Pairwise Global Classifier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pairwise-separating"),
                Handle("PairwiseSeparating"),
                H("Pairwise separating readout family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every pair of distinct states has some readout coordinate on which "
                        + "the two values differ; the coordinate may depend on the pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("has-finite-global-classifier"),
                Handle("HasFiniteGlobalClassifier"),
                H("Existence of a finite global classifier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Some finite subset of indices has an injective dependent joint "
                        + "readout on the state type."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("point-readout"),
                Handle("pointReadout"),
                H("Natural-number point readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Coordinate i returns true exactly at the natural-number state i."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-pairwise-global-classifier-bounded"),
                Handle("finite_pairwise_global_classifier_bounded"),
                H("Finite pairwise separation has a bounded finite classifier"),
                StatementSource.FromAuthor(BoundedClassifierFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose one separating coordinate for each ordered distinct state "
                        + "pair. The image of this finite witness map is a classifier, "
                        + "with cardinality bounded by the distinct-pair universe."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-pairwise-global-classifier"),
                Handle("finite_pairwise_global_classifier"),
                H("Finite pairwise separation closes globally"),
                StatementSource.FromAuthor(FiniteClassifierFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bounded witness set gives a finite selected joint readout that "
                        + "is injective. No finiteness is imposed on indices or outputs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "empty-index-pairwise-separating-iff-no-distinct-pairs"),
                Handle("empty_index_pairwise_separating_iff_no_distinct_pairs"),
                H("Empty index families separate only subsingleton states"),
                StatementSource.FromAuthor(EmptyIndexFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With no coordinate available, the pairwise premise holds exactly "
                        + "when the distinct-state-pair universe is empty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-state-empty-budget-classifier"),
                Handle("empty_state_empty_budget_classifier"),
                H("The empty state type needs no coordinates"),
                StatementSource.FromAuthor(EmptyStateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty joint readout on Fin zero is injective vacuously."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-state-empty-budget-classifier"),
                Handle("singleton_state_empty_budget_classifier"),
                H("A singleton state type needs no coordinates"),
                StatementSource.FromAuthor(SingletonStateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty joint readout on Unit is injective because all states "
                        + "are equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constant-readout-separation-set-empty"),
                Handle("constant_readout_separation_set_empty"),
                H("A constant coordinate separates no state pair"),
                StatementSource.FromAuthor(ConstantReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A coordinate constant across states has empty separation set and "
                        + "cannot occur as a witness in the finite classifier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constant-hypothesis-is-necessary"),
                Handle("constant_hypothesis_is_necessary"),
                H("Constancy is necessary for the empty-separation conclusion"),
                StatementSource.FromAuthor(ConstantNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity Boolean readout separates false from true, so its "
                        + "separation set is nonempty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-readout-singleton-budget-incomplete"),
                Handle("zero_readout_singleton_budget_incomplete"),
                H("The zero readout is incomplete on the naturals"),
                StatementSource.FromAuthor(ZeroReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constant-zero coordinate has empty separation set, and the "
                        + "states zero and one collide in its singleton budget."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("point-readouts-pairwise-separate"),
                Handle("point_readouts_pairwise_separate"),
                H("Natural-number point readouts separate pairwise"),
                StatementSource.FromAuthor(PointPairwiseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For distinct x and y, coordinate x is true at x and false at y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-point-readout-classifier-not-injective"),
                Handle("finite_point_readout_classifier_not_injective"),
                H("No finite point-readout selection classifies the naturals"),
                StatementSource.FromAuthor(FinitePointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two states outside a finite selected set have false values at "
                        + "every selected coordinate and hence collide."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-state-is-necessary"),
                Handle("finite_state_is_necessary"),
                H("State finiteness is necessary"),
                StatementSource.FromAuthor(FiniteStateNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Nat is infinite and its point readouts separate all pairs, yet "
                        + "every finite selected joint readout has a collision."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pairwise-separation-is-necessary"),
                Handle("pairwise_separation_is_necessary"),
                H("Pairwise separation is necessary"),
                StatementSource.FromAuthor(PairwiseNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A constant Unit-valued family on Bool is neither pairwise "
                        + "separating nor finitely classifying."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fpod-principle-227-1"),
                Handle("fpod_principle_227_1"),
                H("Pairwise and global separation close on finite states"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Finite state spaces turn pair-dependent readout certificates "
                            + "into one finite classifier. The point-readout family on "
                            + "Nat is the sharp infinite counterexample.")),
                    Paragraph(Text(
                        "This is dual in scope to Principle 120.1: that theorem concerns "
                            + "infinite-index measure realizability, while this theorem "
                            + "concerns finite-state injective classification.")),
                    Paragraph(Text(
                        "No prime parameter or primality assumption is used."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(DeclarationPrefix + name);

    private static Formula Joint(Formula q, Formula indices) =>
        Call("JointReadout", q, indices);

    private static Formula Injective(Formula formula) =>
        Call("Injective", formula);

    private static Formula BoundedClassifierFormula()
    {
        Formula q = F.Id("q");
        Formula j = F.Id("J");
        Formula premise = Seq(
            Call("Finite", F.Id("X")), Sp, Land, Sp,
            Call("PairwiseSeparating", q));
        Formula conclusion = Seq(
            Exists, Sp, j, Colon, Sp, F.Id("FinsetI"), Comma, Sp,
            Call("card", j), Sp, Leq, Sp,
            Call("card", Call("statePairUniverse", F.Id("X"))), Sp, Land, Sp,
            Injective(Joint(q, j)));
        return Disp(Seq(premise, Sp, Rightarrow, Sp, conclusion, Dot));
    }

    private static Formula FiniteClassifierFormula() =>
        Disp(Seq(
            Call("Finite", F.Id("X")), Sp, Land, Sp,
            Call("PairwiseSeparating", F.Id("q")), Sp, Rightarrow, Sp,
            Call("HasFiniteGlobalClassifier", F.Id("q")), Dot));

    private static Formula EmptyIndexFormula() =>
        Disp(Seq(
            F.Id("I"), Sp, Eq, Sp, Emptyset, Colon, Sp,
            Call("PairwiseSeparating", F.Id("q")), Sp, Iff, Sp,
            Call("statePairUniverse", F.Id("X")), Sp, Eq, Sp, Emptyset, Dot));

    private static Formula EmptyStateFormula() =>
        Disp(Seq(
            F.Id("X"), Sp, Eq, Sp, F.Id("FinZero"), Colon, Sp,
            Injective(Joint(F.Id("q"), Emptyset)), Dot));

    private static Formula SingletonStateFormula() =>
        Disp(Seq(
            F.Id("X"), Sp, Eq, Sp, F.Id("Unit"), Colon, Sp,
            Injective(Joint(F.Id("q"), Emptyset)), Dot));

    private static Formula ConstantReadoutFormula() =>
        Disp(Seq(
            Call("Constant", Call("q", F.Id("i"))), Sp, Rightarrow, Sp,
            Call("observerSeparationSet", F.Id("q"), F.Id("i")),
            Sp, Eq, Sp, Emptyset, Dot));

    private static Formula ConstantNecessityFormula() =>
        Disp(Seq(
            Call("observerSeparationSet", F.Id("idBool"), F.Id("unit")),
            Sp, Neq, Sp, Emptyset, Dot));

    private static Formula ZeroReadoutFormula() =>
        Disp(Seq(
            Call("observerSeparationSet", F.Id("zeroReadout"), F.Id("unit")),
            Sp, Eq, Sp, Emptyset, Sp, Land, Sp,
            Neg, Injective(Joint(F.Id("zeroReadout"), F.Id("singleton"))), Dot));

    private static Formula PointPairwiseFormula() =>
        Disp(Seq(Call("PairwiseSeparating", F.Id("pointReadout")), Dot));

    private static Formula FinitePointFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("J"), Colon, Sp, F.Id("FinsetNat"), Comma, Sp,
            Neg, Injective(Joint(F.Id("pointReadout"), F.Id("J"))), Dot));

    private static Formula FiniteStateNecessityFormula() =>
        Disp(Seq(
            Neg, Call("Finite", F.Id("Nat")), Sp, Land, Sp,
            Call("PairwiseSeparating", F.Id("pointReadout")), Sp, Land, Sp,
            Forall, Sp, F.Id("J"), Colon, Sp, F.Id("FinsetNat"), Comma, Sp,
            Neg, Injective(Joint(F.Id("pointReadout"), F.Id("J"))), Dot));

    private static Formula PairwiseNecessityFormula() =>
        Disp(Seq(
            Neg, Call("PairwiseSeparating", F.Id("constantFamily")),
            Sp, Land, Sp,
            Neg, Call("HasFiniteGlobalClassifier", F.Id("constantFamily")), Dot));

    private static Formula MainFormula()
    {
        Formula finiteSide = Seq(
            Forall, Sp, F.Id("X"), Comma, Sp, F.Id("q"), Comma, Sp,
            Call("Finite", F.Id("X")), Sp, Land, Sp,
            Call("PairwiseSeparating", F.Id("q")), Sp, Rightarrow, Sp,
            Call("HasFiniteGlobalClassifier", F.Id("q")));
        Formula sharpSide = Seq(
            Neg, Call("Finite", F.Id("Nat")), Sp, Land, Sp,
            Call("PairwiseSeparating", F.Id("pointReadout")), Sp, Land, Sp,
            Forall, Sp, F.Id("J"), Colon, Sp, F.Id("FinsetNat"), Comma, Sp,
            Neg, Injective(Joint(F.Id("pointReadout"), F.Id("J"))));
        return Disp(Seq(finiteSide, Sp, Land, Sp, sharpSide, Dot));
    }
}
