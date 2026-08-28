using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming.Conservation;

internal sealed class TestingTowerMembershipDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite tables and program codes admit a primary height with finite sublevels.",
        H("Testing Tower Membership"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-table-and-program-name-carrier"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/Conservation/TestingTowerMembership.TestingName"),
                H("Names are finite tables or program codes"),
                StatementSource.FromAuthor(NameCarrierFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A name is either a function on a self-selected finite support or a "
                    + "natural-number code for a program-based test."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("testing-tower-is-a-multi-filtration-naming-system"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/Conservation/TestingTowerMembership."
                    + "testing_tower_is_multi_filtration"),
                H("Binary description length supplies the primary filtration"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "TestingName O is the disjoint sum of finite functional tables on "
                        + "self-selected finite supports and natural-number program codes. "
                        + "The theorem keeps this source carrier public rather than replacing "
                        + "it with a prepackaged naming-system witness.")),
                    Paragraph(Text(
                        "An injective self-delimiting Boolean code is the algorithmic height, "
                        + "while execution cost is an arbitrary secondary height. Choosing the "
                        + "code coordinate reduces every bounded sublevel to the injective "
                        + "preimage of the finite set of Boolean lists of bounded length.")),
                    Paragraph(Text(
                        "Repository body-shape searches found only the raw-program special case. "
                        + "Pinned Mathlib supplies List.finite_length_le, which is applied "
                        + "directly to establish the finite-level-set clause."))),
                DescribeRole.Lemma)),
        []));

    private static Formula NameCarrierFormula()
    {
        Formula output = F.Id("O");
        Formula support = F.Id("S");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finiteSupport = Call("Finset", naturals);
        Formula finiteTables = Seq(
            SigmaLower, Underscore, Grp(Seq(support, Colon, Sp, finiteSupport)), Sp,
            Open, support, Sp, To, Sp, output, Close);

        return Disp(Seq(
            Forall, Sp, output, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Call("TestingName", output), Sp, Eq, Sp,
            Call("Sum", finiteTables, naturals), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula output = F.Id("O");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula booleanType = F.Id("Bool");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula names = Call("TestingName", output);
        Formula code = F.Id("code");
        Formula executionCost = F.Id("hC");
        Formula name = F.Id("a");
        Formula primary = F.Id("i");
        Formula budget = F.Id("Q");
        Formula codeType = Seq(names, Sp, To, Sp, Call("List", booleanType));
        Formula costType = Seq(names, Sp, To, Sp, naturals);
        Formula selectedHeight = Call(
            "ite",
            primary,
            Call("hC", name),
            Call("length", Call("code", name)));
        Formula boundedNames = new Formula.SetBuilder(
            Seq(selectedHeight, Sp, Leq, Sp, budget),
            name,
            names);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, output, Colon, Sp, type, Comma, RowBreak, Grp(),
            Forall, Sp, code, Colon, Sp, codeType, Comma, Sp,
            Forall, Sp, executionCost, Colon, Sp, costType, Comma, RowBreak, Grp(),
            Call("Injective", code), Sp, Rightarrow, Sp,
            Exists, Sp, primary, Colon, Sp, booleanType, Comma, Sp,
            Forall, Sp, budget, Colon, Sp, naturals, Comma, RowBreak, Grp(),
            Call("Finite", boundedNames), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
