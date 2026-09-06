using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class DynamicIrrationalObserverDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/Dynamics/DynamicIrrationalObserver.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dynamic irrational observer has a contractive ratio and an infinite higher jet.",
        H("Dynamic Irrational Observer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dynamic-irrational-observer"),
                DeclarationHandle.Create(DeclarationPrefix + "Observer"),
                H("Contractive observer with an infinite jet"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The observer records a completed value, a contraction ratio, a linear "
                            + "coefficient, and a genuinely infinite family of higher coefficients "
                            + "indexed directly by every natural number from two onward.")),
                    Paragraph(Text(
                        "A thread realizes these data when the higher-order terms have the stated "
                            + "infinite sum at every time. This explicit HasSum relation does not "
                            + "silently assign a real value to a non-summable formal series.")),
                    Paragraph(Text(
                        "The zeroth readout is the completed value, the first readout is the linear "
                            + "coefficient, and every readout from order two is the corresponding "
                            + "higher coefficient.")),
                    Paragraph(Text(
                        "The golden first observation class is inhabited. Its completed value is "
                            + "the golden ratio, its contraction is minus the inverse golden ratio "
                            + "squared, its linear coefficient is one, and all higher coefficients "
                            + "vanish; the thread is the golden ratio plus the nth power of the "
                            + "contraction.")),
                    Paragraph(Text(
                        "The source's full-jet reconstruction sentence is not asserted as "
                            + "injectivity: the displayed readout sequence omits the contraction "
                            + "ratio, and the source gives no convergence condition for arbitrary "
                            + "higher coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-dynamic-irrational-observer-exists"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "exists_golden_dynamic_irrational_observer"),
                H("The golden dynamic irrational observer exists"),
                StatementSource.FromAuthor(GoldenObserverFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There exists an observer in the golden first-observation class with "
                            + "thread n mapped to the golden ratio plus the nth power of the "
                            + "golden projective multiplier.")),
                    Paragraph(Text(
                        "Its zeroth readout is the golden ratio, its first readout is one, and "
                            + "every readout at an explicitly quantified order k at least two "
                            + "is zero."))),
                DescribeRole.Theorem))));

    private static Formula GoldenObserverFormula()
    {
        Formula observer = F.Id("observer");
        Formula time = F.Id("n");
        Formula order = F.Id("k");
        Formula golden = Call("goldenRatio");
        Formula multiplier = F.Id("goldenProjectiveMultiplier");
        Formula thread = Parenthesized(Seq(
            time, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Mapsto, Sp,
            golden, Sp, Plus, Sp, new Formula.Power(multiplier, time)));
        Formula higherReadouts = Seq(
            Forall, Sp, order, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            D(2), Sp, Leq, Sp, order, Sp, Rightarrow, Sp,
            Call("readout", observer, order), Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Exists, Sp, observer, Colon, Sp, F.Id("Observer"), Comma, RowBreak, Grp(),
            Call("IsGoldenFirstObservationClass", observer), Sp, Land, Sp,
            Call("HasThread", observer, thread), Sp, Land, RowBreak, Grp(),
            Call("readout", observer, D(0)), Sp, Eq, Sp, golden, Sp, Land, Sp,
            Call("readout", observer, D(1)), Sp, Eq, Sp, D(1), Sp, Land, RowBreak, Grp(),
            Parenthesized(higherReadouts), Dot));
    }

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
}
