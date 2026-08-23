using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.SelfSimilar;

internal sealed class GoldenCompatibleIFSDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden-compatible affine similarities contract compact-set space and determine "
            + "a unique nonempty compact attractor.",
        H("Golden-Compatible Iterated Function Systems"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-branches-are-continuous"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.branch_continuous"),
                H("Golden-compatible branches are continuous"),
                StatementSource.FromAuthor(BranchContinuousFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each branch is an affine map of the complex plane: a positive golden "
                            + "scale followed by a unit-modulus rotation, then a translation. "
                            + "These operations are continuous, so every branch carries compact "
                            + "sets to compact sets."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-branches-have-exact-similarity-ratio"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.branch_dist_eq"),
                H("Each branch has its exact golden similarity ratio"),
                StatementSource.FromAuthor(BranchDistanceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the branch indexed by i, the distance between two images is the "
                            + "original distance multiplied by the inverse golden ratio raised "
                            + "to that branch's exponent.")),
                    Paragraph(Text(
                        "The translation cancels in a difference and the prescribed complex "
                            + "exponential is a rotation of modulus one. Thus only the positive "
                            + "golden scaling factor changes distance."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("positive-exponents-give-strict-contraction-ratios"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.branch_ratio_lt_one"),
                H("Positive exponents give strict contraction ratios"),
                StatementSource.FromAuthor(BranchRatioFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The inverse golden ratio lies strictly between zero and one. Since every "
                            + "branch exponent is positive, its corresponding power remains "
                            + "strictly below one, so no branch is merely nonexpansive."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("compact-branch-map-is-lipschitz"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS."
                        + "compactBranch_lipschitz"),
                H("Each compact-set branch map has the common Lipschitz bound"),
                StatementSource.FromAuthor(CompactBranchLipschitzFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Mapping nonempty compact sets through a single branch increases their "
                            + "Hausdorff distance by at most the inverse golden ratio. The sharper "
                            + "branch-specific power is bounded by this common constant because "
                            + "all exponents are positive.")),
                    Paragraph(Text(
                        "Nearest-point comparisons in both directions transfer the pointwise "
                            + "distance estimate to Hausdorff distance, yielding a uniform bound "
                            + "independent of the branch index."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("finite-hutchinson-unions-are-lipschitz"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS."
                        + "finite_hutchinson_lipschitz"),
                H("Finite unions preserve the common Lipschitz bound"),
                StatementSource.FromAuthor(FiniteHutchinsonLipschitzFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any nonempty finite collection of branches, the union of their "
                            + "compact images is Lipschitz with the same inverse-golden constant. "
                            + "Taking a finite union combines component errors by their maximum, "
                            + "so it introduces no larger factor.")),
                    Paragraph(Text(
                        "Induction over the branch collection lifts the single-branch estimate "
                            + "to the finite Hutchinson union without weakening the bound."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("hutchinson-operator-is-contracting"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.hutchinson_contracting"),
                H("The Hutchinson operator is a strict contraction"),
                StatementSource.FromAuthor(HutchinsonContractingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite nonempty golden-compatible system, the Hutchinson operator "
                            + "takes the union of all branch images of a nonempty compact set. Its "
                            + "Lipschitz constant is at most the inverse golden ratio.")),
                    Paragraph(Text(
                        "Because that constant is strictly below one, the finite-union estimate "
                            + "upgrades directly to a contraction on the Hausdorff metric space of "
                            + "nonempty compact subsets of the complex plane."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-compatible-ifs-has-unique-attractor"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS."
                        + "golden_compatible_ifs_has_unique_attractor"),
                H("Every finite nonempty golden-compatible IFS has a unique attractor"),
                StatementSource.FromAuthor(UniqueAttractorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every finite nonempty golden-compatible planar iterated function system "
                            + "has exactly one nonempty compact set fixed by its Hutchinson "
                            + "operator. Equivalently, this attractor is the union of its images "
                            + "under all branches.")),
                    Paragraph(Text(
                        "The space of nonempty compact subsets of the complex plane is complete "
                            + "in the Hausdorff metric. The strict Hutchinson contraction therefore "
                            + "has a fixed point, and contraction uniqueness identifies every "
                            + "compact solution of the invariance equation with that point."))),
                DescribeRole.Theorem))));

    private static Formula BranchContinuousFormula()
    {
        Formula system = F.Id("S");
        Formula index = F.Id("i");

        return Disp(Seq(
            Forall, Sp, system, Comma, Sp, index, Comma, Sp,
            Call("Continuous", Call("branch", system, index)), Dot));
    }

    private static Formula BranchDistanceFormula()
    {
        Formula system = F.Id("S");
        Formula index = F.Id("i");
        Formula first = F.Id("x");
        Formula second = F.Id("y");

        return Disp(Seq(
            Forall, Sp, system, Comma, Sp, index, Comma, Sp,
            first, Comma, Sp, second, Comma, Sp,
            Call("dist", Branch(system, index, first), Branch(system, index, second)),
            Sp, Eq, Sp,
            Multiply(GoldenPower(system, index), Call("dist", first, second)), Dot));
    }

    private static Formula BranchRatioFormula()
    {
        Formula system = F.Id("S");
        Formula index = F.Id("i");

        return Disp(Seq(
            Forall, Sp, system, Comma, Sp, index, Comma, Sp,
            GoldenPower(system, index), Sp, Lt, Sp, D(1), Dot));
    }

    private static Formula CompactBranchLipschitzFormula()
    {
        Formula system = F.Id("S");
        Formula index = F.Id("i");
        Formula first = F.Id("K");
        Formula second = F.Id("L");

        return Disp(Seq(
            Forall, Sp, system, Comma, Sp, index, Comma, Sp,
            first, Comma, Sp, second, Comma, Sp,
            HausdorffDistance(
                Call("compactBranch", system, index, first),
                Call("compactBranch", system, index, second)),
            Sp, Leq, Sp,
            Multiply(GoldenInverse(), HausdorffDistance(first, second)), Dot));
    }

    private static Formula FiniteHutchinsonLipschitzFormula()
    {
        Formula system = F.Id("S");
        Formula branches = F.Id("s");
        Formula first = F.Id("K");
        Formula second = F.Id("L");

        return Disp(Seq(
            Forall, Sp, system, Comma, Sp, branches, Comma, Sp,
            first, Comma, Sp, second, Comma, Sp,
            Call("Nonempty", branches), Sp, Rightarrow, Sp,
            HausdorffDistance(
                Call("finiteHutchinson", system, branches, first),
                Call("finiteHutchinson", system, branches, second)),
            Sp, Leq, Sp,
            Multiply(GoldenInverse(), HausdorffDistance(first, second)), Dot));
    }

    private static Formula HutchinsonContractingFormula()
    {
        Formula system = F.Id("S");

        return Disp(Seq(
            Forall, Sp, system, Comma, Sp,
            Call("FiniteNonemptyGoldenIFS", system), Sp, Rightarrow, Sp,
            Call("ContractingWith", GoldenInverse(), Call("hutchinson", system)), Dot));
    }

    private static Formula UniqueAttractorFormula()
    {
        Formula system = F.Id("S");
        Formula attractor = F.Id("F");
        Formula compactSpace = Call("NonemptyCompacts", F.Id("C"));

        return Disp(Seq(
            Forall, Sp, system, Comma, Sp,
            Call("FiniteNonemptyGoldenIFS", system), Sp, Rightarrow, Sp,
            Exists, Bang, Sp, attractor, Sp, InMacro, Sp, compactSpace, Comma, Sp,
            attractor, Sp, Eq, Sp, Call("hutchinson", system, attractor), Dot));
    }

    private static Formula Branch(
        Formula system,
        Formula index,
        Formula point) =>
        Call("branch", system, index, point);

    private static Formula HausdorffDistance(Formula first, Formula second) =>
        Call("hausdorffDist", first, second);

    private static Formula GoldenPower(Formula system, Formula index) =>
        Seq(Varphi, Caret, Grp(Minus, Call("exponent", system, index)));

    private static Formula GoldenInverse() =>
        Seq(Varphi, Caret, Grp(Minus, D(1)));
}
