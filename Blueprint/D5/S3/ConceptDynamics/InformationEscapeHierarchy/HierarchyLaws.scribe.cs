using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeHierarchy;

internal sealed class HierarchyLawsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hasse paths characterize chain hierarchies, strict chains obey the sharp finite bound, and E1 realizes the four-node diamond.",
        H("Generated-Kernel Hierarchy Laws"),
        Blocks(
            Definition("generated-kernel-cover", "IsCover",
                "Generated-kernel cover", CoverFormula(),
                "A cover is the Mathlib covering relation in the generated-kernel refinement order."),
            Definition("hasse-path", "HasHassePath",
                "Hasse path", HassePathFormula(),
                "The Hasse graph is connected and has at most one cover above and below each node."),
            Definition("generators-comparable-after-closure",
                "GeneratorsComparableAfterClosure",
                "Generators comparable after closure", GeneratorComparableFormula(),
                "Every two singleton generator kernels are comparable after quotienting by exact kernel equality."),
            Theorem("hasse-path-iff-chain", "hasse_path_iff_chain",
                "Hasse paths characterize chains", HasseChainFormula(),
                "Finite generated lattices have path-shaped Hasse graphs exactly when every pair of nodes is comparable."),
            Theorem("strict-generator-dag-shortcut-not-cover",
                "strict_generator_dag_shortcut_not_cover",
                "Strict generator edges need not be covers", ShortcutFormula(),
                "A constant, first-coordinate, and identity catalog forms a chain while its direct identity step skips the middle cover level."),
            Theorem("strict-chain-length-le-card-sub-one",
                "strict_chain_length_le_card_sub_one",
                "Strict chain length is bounded by arena size", ChainBoundFormula(),
                "Each strict step increases the finite kernel-profile range, so at most one fewer step than states is possible."),
            Theorem("nested-flat-coarse-zero", "nested_flat_coarse_zero",
                "Nested coarser generators have zero flat capture", NestedZeroFormula(),
                "The shared-arena refinement law is applied to singleton generated kernels."),
            Theorem("e1-four-node-escape-counts", "e1_four_node_escape_counts",
                "E1 has four extensional nodes", E1CountsFormula(),
                "Kernel reflection checks four quotient classes with escape counts twelve, four, four, and zero."),
            Theorem("e1-diamond-strict-steps", "e1_diamond_strict_steps",
                "E1 forms a strict diamond", E1DiamondFormula(),
                "The coordinate kernels are incomparable; both coordinate paths and the direct identity shortcut are strict."),
            Theorem("e1-schedule-increment-counts", "e1_schedule_increment_counts",
                "E1 schedule increments", E1SchedulesFormula(),
                "The coordinate-first and identity-first classified schedules have the two specified increment vectors."),
            Theorem("e1-unique-capture-and-spectrum",
                "e1_unique_capture_and_spectrum",
                "E1 flat capture and multiplicity spectrum", E1SpectrumFormula(),
                "All three leave-one-out unique sets are empty and the four multiplicity buckets are zero, zero, eight, and four."))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, Formula formula, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, string title, Formula formula, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula C() => F.Id("C");
    private static Formula P() => F.Id("P");
    private static Formula Q() => F.Id("Q");
    private static Formula I() => F.Id("i");
    private static Formula J() => F.Id("j");

    private static Formula CoverFormula() => Seq(
        Call("IsCover", C(), Q(), P()), Sp, Iff, Sp, Call("CovBy", Q(), P()));

    private static Formula HassePathFormula() => Seq(
        Call("HasHassePath", C()), Sp, Iff, Sp,
        And(Call("Preconnected", Call("Hasse", C())),
            And(Call("UniqueCoverAbove", C()), Call("UniqueCoverBelow", C()))));

    private static Formula GeneratorComparableFormula() => Seq(
        Call("GeneratorsComparableAfterClosure", C()), Sp, Iff, Sp,
        Call("PairwiseComparableSingletonKernels", C()));

    private static Formula HasseChainFormula() => And(
        Seq(Call("HasHassePath", C()), Sp, Iff, Sp, Call("Chain", C())),
        Seq(Call("Chain", C()), Sp, Iff, Sp,
            Call("GeneratorsComparableAfterClosure", C())));

    private static Formula ShortcutFormula() => And(
        Call("Chain", Call("ShortcutCatalog")),
        And(Call("StrictIdentityStep", Call("ShortcutCatalog")),
            Seq(Neg, Sp, Call("IsCover", Call("IdentityShortcut")))));

    private static Formula ChainBoundFormula() => Seq(
        Call("length", Call("chain")), Sp, Leq, Sp,
        Call("card", Call("arena")), Sp, Minus, Sp, D(1));

    private static Formula NestedZeroFormula() => ImpliesFormula(
        And(Seq(I(), Sp, Neq, Sp, J()),
            Call("Refines", Call("singletonKernel", J()),
                Call("singletonKernel", I()))),
        Seq(Call("uniqueCapturePairs", C(), I()), Sp, Eq, Sp, Emptyset));

    private static Formula E1CountsFormula() => And(
        Seq(Call("kernelClassCount", Call("E1")), Sp, Eq, Sp, D(4)),
        Seq(Call("escapeCounts", Call("E1")), Sp, Eq, Sp,
            Call("quadruple", D(1, 2), D(4), D(4), D(0))));

    private static Formula E1DiamondFormula() => And(
        Call("Incomparable", Call("Kfst"), Call("Ksnd")),
        And(Call("StrictGeneratorStep", Call("Kempty"), Call("Kfst"), Call("fst")),
            And(Call("StrictGeneratorStep", Call("Kfst"), Call("Kfull"), Call("snd")),
                And(Call("StrictGeneratorStep", Call("Kempty"), Call("Ksnd"), Call("snd")),
                    And(Call("StrictGeneratorStep", Call("Ksnd"), Call("Kfull"), Call("fst")),
                        Call("StrictGeneratorStep", Call("Kempty"), Call("Kfull"),
                            Call("identity")))))));

    private static Formula E1SchedulesFormula() => And(
        Seq(Call("increments", Call("fstSndId")), Sp, Eq, Sp,
            Call("triple", D(8), D(4), D(0))),
        Seq(Call("increments", Call("idFstSnd")), Sp, Eq, Sp,
            Call("triple", D(1, 2), D(0), D(0))));

    private static Formula E1SpectrumFormula() => And(
        Seq(Call("uniqueCaptureVector", Call("E1")), Sp, Eq, Sp,
            Call("triple", Emptyset, Emptyset, Emptyset)),
        Seq(Call("spectrum", Call("E1")), Sp, Eq, Sp,
            Call("quadruple", D(0), D(0), D(8), D(4))));
}
