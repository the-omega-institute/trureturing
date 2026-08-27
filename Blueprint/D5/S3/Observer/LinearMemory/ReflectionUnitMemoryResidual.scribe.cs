using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class ReflectionUnitMemoryResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dynamical reflection adds the current kernel modulo its maximal invariant core.",
        H("Reflection Unit Memory Residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflection-unit-is-the-memory-residual"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/LinearMemory/ReflectionUnitMemoryResidual."
                        + "reflection_unit_memory_residual"),
                H("The reflection unit is the canonical kernel residual"),
                StatementSource.FromAuthor(ResidualFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The imported eventualKernel is constructed by requiring every finite "
                            + "update iterate to remain in the observation kernel. It is therefore "
                            + "contained in the current kernel, preserved by the update, and "
                            + "contains every other invariant submodule of that kernel.")),
                    Paragraph(Text(
                        "The imported memoryQuotient is the quotient of the current kernel by "
                            + "that eventual kernel viewed inside it. The final public clause "
                            + "exposes the canonical quotient map directly: a current-kernel "
                            + "direction maps to zero exactly when it belongs to the eventual kernel."))),
                DescribeRole.Theorem))));

    private static Formula ResidualFormula()
    {
        Formula scalar = F.Id("K"), source = F.Id("V"), target = F.Id("W");
        Formula observation = F.Id("C"), update = F.Id("T");
        Formula x = F.Id("x"), submodule = F.Id("M");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula linearMap = Call("LinearMap", scalar, source, target);
        Formula endomorphism = Call("LinearMap", scalar, source, source);
        Formula current = Call("ker", observation);
        Formula eventual = Call("eventualKernel", observation, update);
        Formula unit = Seq(eventual, Sp, Subseteq, Sp, current);
        Formula invariant = Seq(
            Forall, Sp, x, Colon, Sp, source, Comma, Sp,
            x, Sp, InMacro, Sp, eventual, Sp, Rightarrow, Sp,
            new Formula.Apply(update, [x]), Sp, InMacro, Sp, eventual);
        Formula submoduleType = Call("Submodule", scalar, source);
        Formula submoduleInvariant = Seq(
            Forall, Sp, x, Colon, Sp, source, Comma, Sp,
            x, Sp, InMacro, Sp, submodule, Sp, Rightarrow, Sp,
            new Formula.Apply(update, [x]), Sp, InMacro, Sp, submodule);
        Formula greatest = Seq(
            Forall, Sp, submodule, Colon, Sp, submoduleType, Comma, Sp,
            Open, submodule, Sp, Subseteq, Sp, current, Sp, Land, Sp,
            submoduleInvariant, Close, Sp, Rightarrow, Sp,
            submodule, Sp, Subseteq, Sp, eventual);
        Formula quotient = Call("memoryQuotient", observation, update);
        Formula quotientZero = Seq(
            Forall, Sp, x, Colon, Sp, current, Comma, Sp,
            Open, Call("QuotientMk", observation, update, x), Colon, Sp,
            quotient, Close, Sp, Eq, Sp, D(0), Sp, Iff, Sp,
            Call("coe", x), Sp, InMacro, Sp, eventual);

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, source, Comma, Sp, target,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            Call("Ring", scalar), Comma, Sp,
            Call("AddCommGroup", source), Comma, Sp,
            Call("Module", scalar, source), Comma, RowBreak, Grp(),
            Call("AddCommGroup", target), Comma, Sp,
            Call("Module", scalar, target), Comma, RowBreak, Grp(),
            observation, Colon, Sp, linearMap, Comma, Sp,
            update, Colon, Sp, endomorphism, Comma, RowBreak, Grp(),
            unit, Sp, Land, RowBreak, Grp(),
            Open, invariant, Close, Sp, Land, RowBreak, Grp(),
            Open, greatest, Close, Sp, Land, RowBreak, Grp(),
            Open, quotientZero, Close, Dot));
    }
}
