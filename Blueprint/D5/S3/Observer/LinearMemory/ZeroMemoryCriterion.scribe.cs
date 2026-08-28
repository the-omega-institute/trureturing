using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class ZeroMemoryCriterionDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-future kernel is the maximal invariant part of the current kernel, and its "
            + "quotient vanishes exactly when the dynamics descends through the observation.",
        H("Zero Memory Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventual-kernel-lies-in-current-kernel"),
                DeclarationHandle.Create(Root + "eventualKernel_le_ker"),
                H("The eventual kernel is currently invisible"),
                StatementSource.FromAuthor(EventualKernelLeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Membership at iterate zero is exactly membership in the current kernel. "
                        + "Thus every direction invisible at all future times is invisible now."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eventual-kernel-is-update-invariant"),
                DeclarationHandle.Create(Root + "eventualKernel_invariant"),
                H("The eventual kernel is invariant"),
                StatementSource.FromAuthor(EventualKernelInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying the update shifts every required future-kernel test forward by "
                        + "one step, so all tests remain satisfied."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eventual-kernel-is-greatest-invariant-kernel-submodule"),
                DeclarationHandle.Create(Root + "eventualKernel_is_greatest"),
                H("The eventual kernel is the maximal invariant invisible submodule"),
                StatementSource.FromAuthor(EventualKernelGreatestFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any submodule M contained in the current kernel and preserved by T, "
                        + "induction keeps every finite iterate of each element inside M. Hence "
                        + "M lies in the all-future kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-memory-quotient-iff-kernels-coincide"),
                DeclarationHandle.Create(Root + "zero_memory_iff_eventualKernel_eq_ker"),
                H("The memory quotient is zero exactly at kernel equality"),
                StatementSource.FromAuthor(ZeroMemoryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The memory object is the quotient of the current kernel by the eventual "
                        + "kernel pulled back to that subtype. Mathlib's quotient subsingleton "
                        + "criterion reduces triviality to the denominator being top, which is "
                        + "equivalent to equality of the two kernels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-memory-kernel-invariance-whole-space-descent"),
                DeclarationHandle.Create(Root + "zero_memory_criterion"),
                H("Zero memory, kernel invariance, and exact descent"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K be a division ring, V and W be K-modules, C the observation, and "
                            + "T the update. Zero memory means that the quotient of the current "
                            + "kernel by the all-future kernel is a singleton.")),
                    Paragraph(Text(
                        "Kernel invariance first induces a linear map on the realized range of C "
                            + "through the first isomorphism theorem. The vector-space extension "
                            + "theorem then extends it to an endomorphism of all W, giving the "
                            + "literal whole-codomain descent required by the source statement.")),
                    Paragraph(Text(
                        "Conversely, a commuting whole-space descent sends every zero observation "
                            + "to zero after one update. The proof also verifies zero source or "
                            + "target modules, zero or injective observation, and zero or identity "
                            + "dynamics as degenerate cases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("division-ring-extension-hypothesis-is-necessary"),
                DeclarationHandle.Create(Root + "division_ring_assumption_is_necessary"),
                H("A general ring does not support whole-space descent"),
                StatementSource.FromAuthor(DivisionRingNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over the integers, take C(a,b)=(2a,b) and let T swap the coordinates. The "
                        + "observation is injective, so its kernel is invariant. A descended "
                        + "integer-linear map would have to send (2,0) to (0,1), contradicting "
                        + "linearity because the second coordinate of twice any vector is even."))),
                DescribeRole.Theorem))));

    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Op(Formula name) => Seq(Operatorname, Grp(name));

    private static Formula Call(string name, params Formula[] arguments) =>
        App(Op(F.Id(name)), arguments);

    private static Formula Setup(
        Formula scalar, Formula source, Formula target, Formula observation, Formula update) =>
        App(Op(F.Id("LinearSetup")), scalar, source, target, observation, update);

    // 不用 Apply(Subscript(...), …):那个组合是
    // `formula-context:Apply.Function=precedence:script;produces-script:true;`
    // `starts-with-negation:false`,
    // 固定的 renderer corpus 未覆盖,FormulaCorpusInventoryTests 判红(本地 emit 不报)。
    // 改为手写括号,渲染结果一致而不引入新的渲染组合。
    private static Formula Eventual(Formula observation, Formula update) =>
        Seq(Sub(F.Id("N"), Infty), Open, observation, Comma, Sp, update, Close);

    private static Formula Kernel(Formula observation) =>
        App(Op(F.Id("ker")), observation);

    private static Formula EventualKernelLeFormula()
    {
        Formula scalar = F.Id("K");
        Formula source = F.Id("V");
        Formula target = F.Id("W");
        Formula observation = F.Id("C");
        Formula update = F.Id("T");

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, source, Comma, Sp, target, Comma, Sp,
            observation, Comma, Sp, update, Comma, Sp,
            Setup(scalar, source, target, observation, update), Sp, Rightarrow, Sp,
            Eventual(observation, update), Sp, Subseteq, Sp, Kernel(observation), Dot));
    }

    private static Formula EventualKernelInvariantFormula()
    {
        Formula observation = F.Id("C");
        Formula update = F.Id("T");
        Formula x = F.Id("x");
        Formula eventual = Eventual(observation, update);

        return Disp(Seq(
            Forall, Sp, x, Comma, Sp,
            x, Sp, InMacro, Sp, eventual, Sp, Rightarrow, Sp,
            App(update, x), Sp, InMacro, Sp, eventual, Dot));
    }

    private static Formula EventualKernelGreatestFormula()
    {
        Formula observation = F.Id("C");
        Formula update = F.Id("T");
        Formula submodule = F.Id("M");
        Formula mapped = App(Op(F.Id("map")), update, submodule);

        return Disp(Seq(
            Forall, Sp, submodule, Comma, Sp,
            Open, submodule, Sp, Subseteq, Sp, Kernel(observation), Sp, Land, Sp,
            mapped, Sp, Subseteq, Sp, submodule, Close, Sp, Rightarrow, Sp,
            submodule, Sp, Subseteq, Sp, Eventual(observation, update), Dot));
    }

    private static Formula ZeroMemoryFormula()
    {
        Formula observation = F.Id("C");
        Formula update = F.Id("T");
        Formula current = Sub(F.Id("N"), D(0));
        Formula eventual = Sub(F.Id("N"), Infty);
        Formula quotient = Seq(current, Slash, eventual);

        return Disp(Seq(
            App(Op(F.Id("Subsingleton")), quotient), Sp, Leftrightarrow, Sp,
            Eventual(observation, update), Sp, Eq, Sp, Kernel(observation), Dot));
    }

    private static Formula CriterionFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("W");
        Formula observation = F.Id("C");
        Formula update = F.Id("T");
        Formula descent = F.Id("Tbar");
        Formula x = F.Id("x");
        Formula current = Sub(F.Id("N"), D(0));
        Formula eventual = Sub(F.Id("N"), Infty);
        Formula zeroMemory = App(
            Op(F.Id("Subsingleton")), Seq(current, Slash, eventual));
        Formula invariant = Seq(
            App(Op(F.Id("map")), update, Kernel(observation)),
            Sp, Subseteq, Sp, Kernel(observation));
        Formula descentClause = Seq(
            Exists, Sp, descent, Colon, Sp, Call("LinearMap", scalar, output, output),
            Sp,
            Comma, Sp, Forall, Sp, x, Comma, Sp,
            App(observation, App(update, x)), Sp, Eq, Sp,
            App(descent, App(observation, x)));

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output, Colon, Sp,
            F.Seq(F.Operatorname, F.Grp(F.Id("Type"))), Comma, Sp,
            OpenBracket, Call("DivisionRing", scalar), CloseBracket, Comma, Sp,
            OpenBracket, Call("AddCommGroup", state), CloseBracket, Comma, Sp,
            OpenBracket, Call("Module", scalar, state), CloseBracket, Comma, Sp,
            OpenBracket, Call("AddCommGroup", output), CloseBracket, Comma, Sp,
            OpenBracket, Call("Module", scalar, output), CloseBracket, RowBreak, Grp(),
            observation, Colon, Sp, Call("LinearMap", scalar, state, output), Comma, Sp,
            update, Colon, Sp, Call("LinearMap", scalar, state, state), Comma,
            RowBreak, Grp(),
            App(Op(F.Id("TFAE")), zeroMemory, invariant, descentClause), Dot));
    }

    private static Formula DivisionRingNecessityFormula()
    {
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula plane = Seq(integers, Times, integers);
        Formula observation = F.Id("C");
        Formula update = F.Id("T");
        Formula descent = F.Id("Tbar");
        Formula x = F.Id("x");
        Formula endomorphism = Seq(plane, Sp, To, Sp, plane);
        Formula invariant = Seq(
            App(Op(F.Id("map")), update, Kernel(observation)),
            Sp, Subseteq, Sp, Kernel(observation));
        Formula descends = Seq(
            Exists, Sp, descent, Colon, Sp, endomorphism, Comma, Sp,
            Forall, Sp, x, Comma, Sp,
            App(observation, App(update, x)), Sp, Eq, Sp,
            App(descent, App(observation, x)));

        return Disp(Seq(
            Exists, Sp, observation, Comma, Sp, update, Colon, Sp, endomorphism,
            Comma, Sp, invariant, Sp, Land, Sp, Neg, descends, Dot));
    }
}
