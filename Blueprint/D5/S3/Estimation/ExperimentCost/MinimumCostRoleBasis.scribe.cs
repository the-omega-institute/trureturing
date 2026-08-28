using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ExperimentCost;

internal sealed class MinimumCostRoleBasisDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cost-ordered independence scanning finds minimum-cost finite linear-role bases.",
        H("Minimum-Cost Role Bases"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("role-basis"),
                Handle("IsRoleBasis"),
                H("Role basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A finite role set is independent and spans all available role vectors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("linear-role-matroid"),
                Handle("linearRoleMatroid"),
                H("Linear role matroid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The independent sets are exactly the labels of linearly independent "
                        + "role vectors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("greedy-role-scan-from"),
                Handle("greedyRoleScanFrom"),
                H("Greedy role scan from a chosen set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each scanned label is inserted exactly when independence is preserved."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("greedy-role-scan"),
                Handle("greedyRoleScan"),
                H("Greedy role scan"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The public algorithm discards duplicate scan labels and starts from "
                        + "the empty chosen set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("set-cover"),
                Handle("IsSetCover"),
                H("Set cover"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A chosen finite family covers when its union contains the ground set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("set-cover-example"),
                Handle("setCoverExample"),
                H("Set-cover counterexample family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Three explicit subsets of a six-element ground set witness greedy "
                        + "suboptimality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("linear-role-matroid-independence"),
                Handle("linearRoleMatroid_indep_iff"),
                H("Matroid independence is linear independence"),
                StatementSource.FromAuthor(IndependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constructed matroid exposes precisely the original linear "
                        + "independence predicate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("linear-role-matroid-bases"),
                Handle("linearRoleMatroid_isBase_iff"),
                H("Matroid bases are role bases"),
                StatementSource.FromAuthor(BaseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Maximal matroid independence is equivalent to independence together "
                        + "with spanning every available role vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("greedy-role-scan-minimum-cost"),
                Handle("greedy_role_scan_is_minimum_cost_basis"),
                H("Greedy scanning gives a minimum-cost role basis"),
                StatementSource.FromAuthor(GreedyMinimumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an exhaustive scan in nondecreasing cost order, the output is a "
                        + "role basis whose real total cost is no larger than any other role "
                        + "basis. No finiteness or duplicate-free hypothesis is exposed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-costs-preserve-optimality"),
                Handle("negative_costs_preserve_greedy_optimality"),
                H("Negative costs preserve greedy optimality"),
                StatementSource.FromAuthor(NegativeCostFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A one-role family with cost minus one instantiates the general theorem. "
                        + "Thus nonnegativity is not a necessary hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-cost-bases"),
                Handle("equal_cost_role_bases_have_equal_total"),
                H("Equal-cost role bases have equal totals"),
                StatementSource.FromAuthor(EqualCostFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All bases of the linear role matroid have equal cardinality, so a "
                        + "constant role cost gives every basis the same total."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-role-scan"),
                Handle("empty_role_scan_degenerate"),
                H("Empty role scan"),
                StatementSource.FromAuthor(EmptyRoleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the empty role type, the greedy result is empty and is the unique "
                        + "minimum-cost role basis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-zero-role"),
                Handle("singleton_zero_role_is_skipped"),
                H("A singleton zero role is skipped"),
                StatementSource.FromAuthor(SingletonZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero vector cannot extend the empty independent set; omitting its "
                        + "label still spans the available zero role."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-nonzero-role"),
                Handle("singleton_nonzero_role_is_selected"),
                H("A singleton nonzero role is selected"),
                StatementSource.FromAuthor(SingletonNonzeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A lone nonzero rational vector is accepted and forms the singleton "
                        + "role basis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exhaustive-scan-necessary"),
                Handle("exhaustive_scan_is_necessary"),
                H("Exhaustive scanning is necessary"),
                StatementSource.FromAuthor(ExhaustivenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An empty scan on a single nonzero role returns empty, which cannot span "
                        + "that role. Thus coverage of every label is a genuine premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sorted-scan-necessary"),
                Handle("sorted_scan_is_necessary"),
                H("Cost order is necessary"),
                StatementSource.FromAuthor(SortedNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two equal nonzero vectors have costs one and zero. Scanning the dearer "
                        + "label first selects cost one, although the other singleton basis "
                        + "has cost zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixed-zero-role"),
                Handle("zero_role_among_nonzero_roles_is_skipped"),
                H("A mixed zero role is skipped"),
                StatementSource.FromAuthor(MixedZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In a two-role family containing zero and one, the zero vector is skipped "
                        + "and the nonzero singleton is a basis for all available roles."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("greedy-set-cover-suboptimal"),
                Handle("greedy_set_cover_can_be_suboptimal"),
                H("Greedy set cover can be suboptimal"),
                StatementSource.FromAuthor(SetCoverFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The unique largest set is chosen first and then needs both remaining "
                        + "sets, while those two sets alone already cover the ground set."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(Prefix + name);

    private static Formula IndependenceFormula()
    {
        Formula vectors = F.Id("v");
        Formula roles = F.Id("S");
        return Disp(Seq(
            Call("Indep", Call("linearRoleMatroid", vectors), roles),
            Sp, Iff, Sp, Call("LinearIndepOn", vectors, roles), Dot));
    }

    private static Formula BaseFormula()
    {
        Formula vectors = F.Id("v");
        Formula roles = F.Id("S");
        return Disp(Seq(
            Call("IsBase", Call("linearRoleMatroid", vectors), roles),
            Sp, Iff, Sp, Call("IsRoleBasis", vectors, roles), Dot));
    }

    private static Formula GreedyMinimumFormula()
    {
        Formula vectors = F.Id("v");
        Formula cost = F.Id("c");
        Formula scan = F.Id("L");
        Formula roles = F.Id("B");
        Formula greedy = Call("greedyRoleScan", vectors, scan);
        return Disp(Seq(
            Call("Exhaustive", scan), Sp, Land, Sp,
            Call("Nondecreasing", cost, scan), Sp, Rightarrow, RowBreak,
            Call("IsRoleBasis", vectors, greedy), Sp, Land, Sp,
            Forall, Sp, roles, Comma, Sp,
            Call("IsRoleBasis", vectors, roles), Sp, Rightarrow, Sp,
            Call("totalCost", cost, greedy), Sp, Leq, Sp,
            Call("totalCost", cost, roles), Dot));
    }

    private static Formula NegativeCostFormula()
    {
        Formula vectors = F.Id("v");
        Formula cost = F.Id("c");
        Formula scan = F.Id("L");
        Formula role = F.Id("e");
        Formula greedy = Call("greedyRoleScan", vectors, scan);
        return Disp(Seq(
            Exists, Sp, role, Comma, Sp, Call("cost", cost, role), Sp, Lt, Sp, D(0),
            Sp, Land, Sp, Call("MinimumCostBasis", cost, greedy), Dot));
    }

    private static Formula EqualCostFormula()
    {
        Formula vectors = F.Id("v");
        Formula value = F.Id("a");
        Formula first = new Formula.Subscript(F.Id("B"), D(1));
        Formula second = new Formula.Subscript(F.Id("B"), D(2));
        return Disp(Seq(
            Call("IsRoleBasis", vectors, first), Sp, Land, Sp,
            Call("IsRoleBasis", vectors, second), Sp, Rightarrow, RowBreak,
            Call("constantTotal", value, first), Sp, Eq, Sp,
            Call("constantTotal", value, second), Dot));
    }

    private static Formula EmptyRoleFormula()
    {
        Formula vectors = F.Id("v");
        Formula cost = F.Id("c");
        return Disp(Seq(
            Call("greedyRoleScan", vectors, Call("emptyScan")), Sp, Eq, Sp, Emptyset,
            Sp, Land, Sp, Call("IsRoleBasis", vectors, Emptyset), Sp, Land, Sp,
            Call("MinimumCostBasis", cost, Emptyset), Dot));
    }

    private static Formula SingletonZeroFormula()
    {
        Formula zeroRole = Call("zeroRole");
        Formula singletonScan = Call("singletonScan", D(0));
        return Disp(Seq(
            Call("greedyRoleScan", zeroRole, singletonScan), Sp, Eq, Sp, Emptyset,
            Sp, Land, Sp, Call("IsRoleBasis", zeroRole, Emptyset), Dot));
    }

    private static Formula SingletonNonzeroFormula()
    {
        Formula unitRole = Call("unitRole");
        Formula singleton = Call("singleton", D(0));
        Formula singletonScan = Call("singletonScan", D(0));
        return Disp(Seq(
            Call("greedyRoleScan", unitRole, singletonScan), Sp, Eq, Sp, singleton,
            Sp, Land, Sp, Call("IsRoleBasis", unitRole, singleton), Dot));
    }

    private static Formula ExhaustivenessFormula()
    {
        Formula vectors = Call("unitRole");
        Formula greedy = Call("greedyRoleScan", vectors, Call("emptyScan"));
        return Disp(Seq(
            greedy, Sp, Eq, Sp, Emptyset, Sp, Land, Sp,
            Neg, Call("IsRoleBasis", vectors, Emptyset), Dot));
    }

    private static Formula SortedNecessaryFormula()
    {
        Formula family = Call("equalVectorPair");
        Formula cost = Call("costPair", D(1), D(0));
        Formula scan = Call("scan", D(0), D(1));
        Formula dear = Call("singleton", D(0));
        Formula cheap = Call("singleton", D(1));
        return Disp(Seq(
            Neg, Call("Nondecreasing", cost, scan), Sp, Land, Sp,
            Call("greedyRoleScan", family, scan), Sp, Eq, Sp, dear, Sp, Land, RowBreak,
            Call("IsRoleBasis", family, cheap), Sp, Land, Sp,
            Call("totalCost", cost, cheap), Sp, Lt, Sp,
            Call("totalCost", cost, dear), Dot));
    }

    private static Formula MixedZeroFormula()
    {
        Formula family = Call("zeroUnitPair");
        Formula singleton = Call("singleton", D(1));
        Formula scan = Call("scan", D(0), D(1));
        return Disp(Seq(
            Call("greedyRoleScan", family, scan), Sp, Eq, Sp, singleton,
            Sp, Land, Sp, Call("IsRoleBasis", family, singleton), Dot));
    }

    private static Formula SetCoverFormula()
    {
        Formula family = F.Id("A");
        Formula ground = F.Id("U");
        return Disp(Seq(
            Call("uniqueLargestFirst", family), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Call("greedyCoverSize", ground, family), Sp, Eq, Sp, D(3), Sp, Land, Sp,
            Call("optimalCoverSize", ground, family), Sp, Eq, Sp, D(2), Dot));
    }
}
