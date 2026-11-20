using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Recurrence;

internal sealed class VasilyevForceDivergenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/vasilyev2026upordown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "There is a set of positive integers that forces divergence in every superset but contains no all-up tail.",
        H("Vasilyev's force-divergence question"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("vasilyev-force-divergence-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Question 7.7"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let P be the positive integers. At x in P the up and down steps are the "
                        + "ceilings of 3x/2 and x/2, respectively. The map T for a set S takes "
                        + "the up step at members of S and the down step elsewhere.")),
                    Paragraph(Text(
                        "A subset A of P is force-divergent if, for every S with A contained in S "
                        + "and S contained in P, some positive starting vertex has an orbit under T "
                        + "that never enters a periodic cycle. A contains a tail if the whole "
                        + "forward up orbit of some positive vertex lies in A, including time zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vasilyev-force-divergence-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A force-divergent set without a chain tail"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Start with b(0) = 3. Define b(n + 1) to be the 2b(n)-th up iterate of n + 1. "
                        + "Omit exactly the values b(n + 1) from P to obtain A. Each positive vertex "
                        + "n + 1 then has an up iterate outside A.")),
                    Paragraph(Text(
                        "Each up step increases a positive value by at least one, so b(n + 1) > 2b(n). "
                        + "For m = b(n + 1), the ceiling bounds put both D(m) and U(D(m)) strictly "
                        + "between b(n) and m. The gap contains no omitted value. Thus, for any superset "
                        + "S, an orbit at a positive vertex in S grows after one up step. At a vertex "
                        + "outside S, that vertex is an omitted m and its next three steps are down, up, up. "
                        + "The endpoint is at least 9m/8, which exceeds m.")),
                    Paragraph(Text(
                        "Concatenating these blocks gives unbounded orbit values from every positive start "
                        + "under each allowed S. An eventually periodic orbit has only finitely many "
                        + "values. The same A therefore forces divergence and excludes every all-up tail."))),
                DescribeRole.Theorem))));

    private static Formula ClaimFormula()
    {
        var a = F.Id("A");
        Formula subsets = new Formula.Apply(Seq(Operatorname, Grp(F.Id("Set"))),
            [Seq(Mathbb, Grp(F.Id("N")))]);
        Formula positive = new Formula.Relation(a, FormulaRelationOperator.SubsetOf, F.Id("P"));
        Formula force = new Formula.Apply(Seq(Operatorname, Grp(F.Id("ForceDivergent"))), [a]);
        Formula tail = new Formula.Apply(Seq(Operatorname, Grp(F.Id("ContainsTail"))), [a]);
        Formula assertion = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("A"),
            subsets, new Formula.Logic(positive, FormulaLogicOperator.Implies,
                new Formula.Logic(force, FormulaLogicOperator.Implies, tail)));
        return new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, assertion);
    }
}
