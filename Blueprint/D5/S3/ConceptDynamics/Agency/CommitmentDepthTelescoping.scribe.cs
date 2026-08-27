using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class CommitmentDepthTelescopingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commitment depth is the finite telescoping loss of compatible future-plan capacity.",
        H("Commitment Depth Telescoping"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-plan-commitment-depth-telescopes"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Agency/CommitmentDepthTelescoping."
                        + "finite_plan_commitment_depth_telescopes"),
                H("Commitment depth telescopes along a finite history"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source object is a finite sequence of compatible future-plan "
                            + "spaces. At each step, commitment depth is constructed as the "
                            + "decrease in its base-two log-cardinality.")),
                    Paragraph(Text(
                        "The finite sum cancels every intermediate plan-space capacity, leaving "
                            + "only the initial capacity minus the terminal capacity. The result "
                            + "also holds for an empty plan space under Lean's total real logarithm."))),
                DescribeRole.Proposition))));

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

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula plan = F.Id("Plan");
        Formula horizon = F.Id("n");
        Formula time = F.Id("t");
        Formula planSpace = F.Id("Omega");
        Formula naturals = F.Id("Nat");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula planSpaceType = Arrow(naturals, Call("Finset", plan));
        Formula depth = Seq(
            Call("log2", Call("card", Apply(planSpace, time))), Sp, Minus, Sp,
            Call("log2", Call("card", Apply(planSpace, Seq(time, Sp, Plus, Sp, D(1))))));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, plan, Colon, Sp, type, Comma, Sp,
                horizon, Colon, Sp, naturals, Comma),
            Seq(planSpace, Colon, Sp, planSpaceType, Comma),
            Seq(
                Sum, Underscore, Grp(Seq(time, Sp, InMacro, Sp, Call("range", horizon))),
                Sp, Grp(depth), Sp, Eq),
            Seq(
                Call("log2", Call("card", Apply(planSpace, D(0)))), Sp, Minus, Sp,
                Call("log2", Call("card", Apply(planSpace, horizon))), Dot),
        ]));
    }
}
