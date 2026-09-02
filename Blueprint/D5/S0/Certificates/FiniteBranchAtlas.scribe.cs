using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteBranchAtlasDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exhaustive refutations of every branch in a finite covering atlas "
            + "exclude all admissible candidates.",
        H("Finite Branch Atlases"),
        Blocks(Describe.Lean(
            DescribeId.Create("branchwise-exhaustive-refutation-excludes-every-admissible-candidate"),
            DeclarationHandle.Create(
                "D5/S0/Certificates/FiniteBranchAtlas.no_admissible_of_all_branch_checks"),
            H("Branchwise exhaustive refutation excludes every admissible candidate"),
            StatementSource.FromAuthor(Disp(Seq(
                Open, Forall, Sp, F.Id("b"), Comma, Sp,
                Call("branchEmptyCheck", F.Id("A"), F.Id("p"), F.Id("b")),
                Sp, Eq, Sp, F.Id("true"), Close,
                Sp, Rightarrow, Sp,
                Neg, Sp, Exists, Sp, F.Id("x"), Comma, Sp,
                F.Id("p"), Open, F.Id("x"), Close,
                Sp, Eq, Sp, F.Id("true"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Every candidate is assigned to at least one branch by a finite Boolean atlas.")),
                Paragraph(Text(
                    "For each branch, the finite exhaustion checker certifies that no candidate is simultaneously in that branch and admissible.")),
                Paragraph(Text(
                    "Coverage selects a branch for any alleged admissible candidate, and the corresponding branch certificate supplies the contradiction. This is the reusable logical shell for Hadamard classification, finite automata exclusion, and finite causal-polytope searches."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Certificates/FiniteExhaustion")),
        ]));

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
}
