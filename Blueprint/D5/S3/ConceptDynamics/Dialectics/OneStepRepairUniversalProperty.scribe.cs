using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Dialectics;

internal sealed class OneStepRepairUniversalPropertyDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The one-step interface is the coarsest interface deciding two successive readouts.",
        H("One-Step Repair Universal Property"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-step-repair-universal"),
                DeclarationHandle.Create(DeclarationPrefix + "one_step_repair_universal"),
                H("One-step factorization"),
                StatementSource.FromAuthor(FactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If q and q after F both factor through r, pairing the two supplied "
                        + "factors gives a factorization of the one-step interface through r. "
                        + "The proof needs no inhabitedness, finiteness, or type-class data."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-step-repair-factor-unique-on-range"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "one_step_repair_factor_unique_on_range"),
                H("Factor uniqueness on the realized image"),
                StatementSource.FromAuthor(UniquenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any two paired factors inducing the same one-step interface agree on "
                        + "the realized range of r. Values outside that range remain "
                        + "unconstrained unless r is surjective."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-step-repair-kernel-contains"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "one_step_repair_kernel_contains"),
                H("Reverse kernel containment"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every equality in the kernel of r forces equality of both the current "
                        + "and next readouts. Thus the kernel of the one-step interface "
                        + "contains the kernel of every interface deciding both values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("current-factorization-hypothesis-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "current_factorization_hypothesis_is_necessary"),
                H("Current factorization is necessary"),
                StatementSource.FromAuthor(CurrentNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A Boolean identity readout with a constant update has a next readout "
                        + "factoring through Unit, while its current readout does not. The "
                        + "claimed paired factorization therefore fails."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("next-factorization-hypothesis-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "next_factorization_hypothesis_is_necessary"),
                H("Next factorization is necessary"),
                StatementSource.FromAuthor(NextNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a pair of Booleans, the first projection factors through itself, but "
                        + "swapping coordinates makes the next readout depend on the hidden "
                        + "second coordinate. The paired factorization then fails."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        DefinitionDsl.Call(name, arguments);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Pair(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula FactorizationFormula()
    {
        Formula xType = F.Id("X");
        Formula bType = F.Id("B");
        Formula cType = F.Id("C");
        Formula q = F.Id("q");
        Formula update = F.Id("F");
        Formula r = F.Id("r");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula current = Seq(q, Sp, Eq, Sp, Compose(a, r));
        Formula next = Seq(Compose(q, update), Sp, Eq, Sp, Compose(b, r));
        Formula conclusion = Seq(
            Call("oneStepInterface", q, update), Sp, Eq, Sp,
            Compose(Pair(a, b), r));

        return Disp(Seq(
            Forall, Sp, xType, Comma, Sp, bType, Comma, Sp, cType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            q, Colon, Sp, Arrow(xType, bType), Comma, Sp,
            update, Colon, Sp, Arrow(xType, xType), Comma, Sp,
            r, Colon, Sp, Arrow(xType, cType), Comma, Sp,
            a, Comma, Sp, b, Colon, Sp, Arrow(cType, bType), Comma, RowBreak, Grp(),
            current, Sp, Land, Sp, next, Sp, Rightarrow, Sp, conclusion, Dot));
    }

    private static Formula UniquenessFormula()
    {
        Formula q = F.Id("q");
        Formula update = F.Id("F");
        Formula r = F.Id("r");
        Formula a1 = F.Id("a1");
        Formula b1 = F.Id("b1");
        Formula a2 = F.Id("a2");
        Formula b2 = F.Id("b2");
        Formula oneStep = Call("oneStepInterface", q, update);
        Formula firstFactor = Pair(a1, b1);
        Formula secondFactor = Pair(a2, b2);
        Formula first = Seq(oneStep, Sp, Eq, Sp, Compose(firstFactor, r));
        Formula second = Seq(oneStep, Sp, Eq, Sp, Compose(secondFactor, r));
        Formula range = Call("range", r);

        return Disp(Seq(
            first, Sp, Land, Sp, second, Sp, Rightarrow, Sp,
            Call("EqOn", firstFactor, secondFactor, range), Dot));
    }

    private static Formula KernelFormula()
    {
        Formula q = F.Id("q");
        Formula update = F.Id("F");
        Formula r = F.Id("r");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula oneStep = Call("oneStepInterface", q, update);

        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            At(r, x), Sp, Eq, Sp, At(r, y), Sp, Rightarrow, Sp,
            At(oneStep, x), Sp, Eq, Sp, At(oneStep, y), Dot));
    }

    private static Formula CurrentNecessityFormula()
    {
        Formula q = F.Id("q");
        Formula update = F.Id("F");
        Formula r = F.Id("r");
        Formula a = F.Id("a");
        Formula b = F.Id("b");

        return Disp(Seq(
            Exists, Sp, q, Comma, Sp, update, Comma, Sp, r, Comma, Sp, a, Comma,
            Sp, b, Comma, RowBreak, Grp(),
            Compose(q, update), Sp, Eq, Sp, Compose(b, r), Sp, Land, Sp,
            Call("oneStepInterface", q, update), Sp, Neq, Sp,
            Compose(Pair(a, b), r), Dot));
    }

    private static Formula NextNecessityFormula()
    {
        Formula q = F.Id("q");
        Formula update = F.Id("F");
        Formula r = F.Id("r");
        Formula a = F.Id("a");
        Formula b = F.Id("b");

        return Disp(Seq(
            Exists, Sp, q, Comma, Sp, update, Comma, Sp, r, Comma, Sp, a, Comma,
            Sp, b, Comma, RowBreak, Grp(),
            q, Sp, Eq, Sp, Compose(a, r), Sp, Land, Sp,
            Call("oneStepInterface", q, update), Sp, Neq, Sp,
            Compose(Pair(a, b), r), Dot));
    }
}
