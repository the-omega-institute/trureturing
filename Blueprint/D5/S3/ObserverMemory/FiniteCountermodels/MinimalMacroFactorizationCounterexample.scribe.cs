using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FiniteCountermodels;

internal sealed class MinimalMacroFactorizationCounterexampleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A deterministic three-state process need not descend through a two-class readout.",
        H("Minimal Failure of Macroscopic Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("deterministic-three-state-process-has-no-macro-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/FiniteCountermodels/"
                        + "MinimalMacroFactorizationCounterexample."
                        + "deterministic_three_state_process_has_no_macro_factorization"),
                H("A deterministic process can fail to descend through observation"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The microscopic domain is Fin 3. The named observation map sends zero "
                            + "and one to class A and two to class B. The named total process fixes "
                            + "zero and sends one and two to two, so determinism is represented by "
                            + "an ordinary function rather than an extra hypothesis.")),
                    Paragraph(Text(
                        "Zero and one have the same present observation, while their next "
                            + "observations are A and B. Any proposed macroscopic map would therefore "
                            + "send A to both A and B, which is impossible.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Function.FactorsThrough and factorsThrough_iff. "
                            + "The proof first refutes fiber constancy at zero and one and then uses "
                            + "that exact bridge to rule out every factor map. Repository searches "
                            + "found adjacent factorization machinery but no equal finite model."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula CounterexampleFormula()
    {
        Formula q = F.Id("q");
        Formula process = F.Id("F");
        Formula macro = Seq(Overline, Grp(process));
        Formula a = F.Id("A");
        Formula b = F.Id("B");

        Formula Q(Formula x) => Apply(q, x);
        Formula Step(Formula x) => Apply(process, x);

        return Disp(Seq(
            Q(D(0)), Eq, Q(D(1)), Eq, a, Comma, Sp, Q(D(2)), Eq, b, Semi, RowBreak,
            Step(D(0)), Eq, D(0), Comma, Sp,
            Step(D(1)), Eq, D(2), Comma, Sp,
            Step(D(2)), Eq, D(2), Semi, RowBreak,
            Q(Step(D(0))), Eq, a, Sp, Neq, Sp, b, Eq, Q(Step(D(1))), Semi, RowBreak,
            Neg, Sp, Exists, Sp, macro, Colon, Sp,
            F.Id("O"), Sp, To, Sp, F.Id("O"), Comma, Esc,
            q, Circ, Sp, process, Sp, Eq, Sp, macro, Circ, Sp, q, Dot));
    }
}
