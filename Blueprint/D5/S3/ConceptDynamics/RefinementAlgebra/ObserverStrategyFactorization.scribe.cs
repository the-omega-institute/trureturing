using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class ObserverStrategyFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observer strategy factorization is equivalent to reverse kernel inclusion.",
        H("Observer Strategy Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observer-strategy-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/RefinementAlgebra/"
                        + "ObserverStrategyFactorization.observer_strategy_factorization"),
                H("An effective interface implements exactly its fiber-constant policies"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The observer interface is surjective onto its declared coordinate "
                            + "carrier, matching the source convention that interfaces use only "
                            + "realized values. The policy readout need not be surjective.")),
                    Paragraph(Text(
                        "A factorization makes the policy constant on every interface fiber. "
                            + "Conversely, a section of the effective interface constructs the "
                            + "policy implementation from the kernel-inclusion premise.")),
                    Paragraph(Text(
                        "The repository's existing effective-kernel theorem assumes both "
                            + "readouts are surjective, so applying it here would add a premise "
                            + "absent from the source."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.AddRange([Comma, Sp]);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula observationType = F.Id("O");
        Formula policyType = F.Id("Policy");
        Formula observer = F.Id("q");
        Formula policy = F.Id("Pi");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula conclusion = Seq(
            Call("Refines", policy, observer), Sp, Iff, Sp,
            Call("ker", observer), Sp, Subseteq, Sp, Call("ker", policy));

        return Disp(Seq(
            Forall, Sp, Typed(state, type), Comma, Sp,
            Typed(observationType, type), Comma, Sp,
            Typed(policyType, type), Comma, RowBreak, Grp(),
            Typed(observer, Arrow(state, observationType)), Comma, Sp,
            Typed(policy, Arrow(state, policyType)), Comma, RowBreak, Grp(),
            Call("Surjective", observer), Sp, Rightarrow, Sp,
            Open, conclusion, Close, Dot));
    }
}
