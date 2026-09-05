using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeCounting;

internal sealed class FusedCorrectnessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fused catalog census agrees with every frozen reference field.",
        H("Fused Counting Correctness"),
        Blocks(
            Thm("fused-pair-classification", "fusedPairClassification",
                "Saturated pair classification", PairClassification(),
                "Content. The live escape witness is the singleton scan theorem, which " +
                    "identifies the sole disagreement and proves all other indices agree."),
            Thm("fused-full-correct", "fusedFull_eq_escapeNumerator",
                "Fused full count is exact", FullCorrect(), FoldWitness()),
            Thm("fused-unique-correct", "fusedUnique_eq_uniqueCaptureCount",
                "Every fused unique count is exact", UniqueCorrect(), FoldWitness()),
            Thm("fused-without-correct", "fusedWithout_eq_escapeNumerator_without",
                "Derived leave-one-out count is exact", WithoutCorrect(),
                "Bind-only companion. It rewrites full and unique correctness through the " +
                    "frozen leave-one-out addition law."),
            Thm("fused-role-bin-correct", "fusedRoleBins_eq_roleHistogram",
                "Every fused role bin is exact", RoleCorrect(), FoldWitness()),
            Thm("fused-role-bins-complete", "fusedRoleBins_sum_eq_unique",
                "Fused role bins are complete", RoleSumCorrect(),
                "Content. Pointwise fused correctness stays live, and the new bucket-signature " +
                    "bijection transports the frozen histogram partition."),
            Thm("fused-positive-transport", "uniqueCaptureCount_pos_of_fused",
                "Fused positivity transports", PositivityTransport(),
                "Bind-only companion. It rewrites by fused unique-count correctness."))));

    private static readonly Formula B = F.Id("b");
    private static readonly Formula C = F.Id("C");
    private static readonly Formula E = F.Id("E");
    private static readonly Formula I = F.Id("i");
    private static readonly Formula L = F.Id("x");
    private static readonly Formula R = F.Id("y");
    private static readonly Formula S = F.Id("S");

    private static Formula Counts() => Call("fusedCounts", C, S, E);

    private static Formula PairClassification() => Seq(
        Eq(Call("pairScan", C, E, L, R), F.Id("none")), Sp,
        Leftrightarrow, Sp,
        Call("indistinguishable", C, Call("fullIndexSet", C), L, R));

    private static Formula FullCorrect() => Eq(
        Call("full", Counts()), Call("escapeNumerator", C, Call("fullIndexSet", C)));

    private static Formula UniqueCorrect() => Eq(
        Call("unique", Counts(), I), Call("uniqueCaptureCount", C, I));

    private static Formula WithoutCorrect() => Eq(
        Call("without", Counts(), I), Call("escapeNumerator", C, Call("without", C, I)));

    private static Formula RoleCorrect() => Eq(
        Call("roleBins", Counts(), I, B),
        Call("roleHistogram", C, I, Call("roleSignatureOfBucket", B)));

    private static Formula RoleSumCorrect() => Eq(
        Call("sum", B, Call("roleBins", Counts(), I, B)), Call("unique", Counts(), I));

    private static Formula PositivityTransport() => Implies(
        Lt(D(0), Call("unique", Counts(), I)),
        Lt(D(0), Call("uniqueCaptureCount", C, I)));

    private static string FoldWitness() =>
        "Content. The live fusedCounts_value fold invariant counts each pair class once; " +
        "the pair classifier then identifies the matching frozen finset.";

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string title, Formula formula, string accounting) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(accounting))), DescribeRole.Theorem);

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

    private static Formula Eq(Formula left, Formula right) =>
        Seq(left, Sp, F.Eq, Sp, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
