using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class FiniteKernelStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite predictive kernel chains stabilize within their class-count budget.",
        H("Finite Kernel Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-kernel-chain-stability"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Refinement/FiniteKernelStability."
                        + "finite_kernel_chain_stability"),
                H("Finite predictive kernels stabilize"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be a finite nonempty state space, let F update its states, and "
                            + "let q map X surjectively onto the initial readout classes O. "
                            + "Write E_m for the kernel of the prediction word through depth m, "
                            + "c_m for its number of classes, and N for the least depth where "
                            + "two consecutive kernels agree.")),
                    Paragraph(Text(
                        "The kernels form a decreasing chain. At N the chain becomes permanently "
                            + "constant, while every transition before N is strict. Consequently "
                            + "the number N of strict refinements is at most c_N minus c_0, and "
                            + "that class gain is at most the unused finite-state budget "
                            + "card(X) minus c_0. Surjectivity identifies c_0 with card(O).")),
                    Paragraph(Text(
                        "Equality at the finite depth N is equivalent to equality of every future "
                            + "readout. Thus all distinctions visible in the infinite future have "
                            + "appeared after a finite, system-dependent depth.")),
                    Paragraph(Text(
                        "The proof directly applies the repository's exact finite observation "
                            + "refinement bound and permanent partition-stability theorem. The "
                            + "new declaration is only the thin kernel-chain wrapper required by "
                            + "this source statement."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula RelationAt(Formula index) =>
        new Formula.Subscript(F.Id("E"), index);

    private static Formula CountAt(Formula index) =>
        new Formula.Subscript(F.Id("c"), index);

    private static Formula Cardinality(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula index = F.Id("m");
        Formula offset = F.Id("r");
        Formula depth = F.Id("N");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula time = F.Id("k");
        Formula current = RelationAt(index);
        Formula successor = RelationAt(Seq(index, Plus, D(1)));
        Formula stable = RelationAt(depth);
        Formula later = RelationAt(Seq(depth, Plus, offset));
        Formula classGain = Seq(CountAt(depth), Sp, Minus, Sp, CountAt(D(0)));
        Formula stateBudget = Seq(
            Cardinality(state), Sp, Minus, Sp, CountAt(D(0)));
        Formula iteratedLeft = Apply(
            new Formula.Power(update, time), left);
        Formula iteratedRight = Apply(
            new Formula.Power(update, time), right);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Comma, Sp,
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, RowBreak,
            Open, Forall, Sp, index, Comma, Sp,
            successor, Sp, Subseteq, Sp, current, Close, Sp, Land, RowBreak,
            Open, Forall, Sp, offset, Comma, Sp,
            later, Sp, Eq, Sp, stable, Close, Sp, Land, RowBreak,
            Open, Forall, Sp, index, Sp, Lt, Sp, depth, Comma, Sp,
            successor, Sp, Neq, Sp, current, Close, Sp, Land, RowBreak,
            CountAt(D(0)), Sp, Eq, Sp, Cardinality(output), Sp, Land, RowBreak,
            depth, Sp, Leq, Sp, classGain, Sp, Leq, Sp, stateBudget, Sp, Land,
            RowBreak,
            Open, left, Comma, Sp, right, Close, Sp, InMacro, Sp, stable,
            Sp, Iff, Sp,
            Open, Forall, Sp, time, Comma, Sp,
            Apply(readout, iteratedLeft), Sp, Eq, Sp,
            Apply(readout, iteratedRight), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
