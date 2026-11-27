using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.CosetActions;

internal sealed class FixedCosetBranchingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/FiniteGroups/CosetActions/FixedCosetBranching";

    private static Formula Card(Formula set) => Seq(Lvert, Sp, set, Sp, Rvert);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nonempty(Formula set) => Seq(set, Sp, Neq, Sp, Emptyset);

    public DocumentDefinition Create()
    {
        var fixedCosets = F.Id("X");
        var conjugatesIn = F.Id("Y");
        var subgroup = F.Id("K");
        var centralizer = F.Id("C");

        return DocumentDefinition.Create(ScribeNode.Create(
            "Fixed left cosets are supported on conjugacy classes meeting the subgroup. "
            + "Two counts of their representatives give the weighted cardinality identity.",
            H("Support and cardinality of fixed left cosets"),
            Blocks(
                Paragraph(Text("Let G be a group, K a subgroup, and g an element of G. "
                    + "Write X for the left cosets in G/K fixed by left multiplication by g, "
                    + "Y for the intersection of the conjugacy class of g with K, "
                    + "and C for the centralizer of g in G.")),
                Describe.Lean(
                    DescribeId.Create("fixed-coset-branching-support"),
                    DeclarationHandle.Create(Module + ".fixedCosets_nonempty_iff"),
                    H("Nonempty support"),
                    StatementSource.FromAuthor(Disp(
                        new Formula.Logic(Nonempty(fixedCosets), FormulaLogicOperator.Iff,
                            Nonempty(conjugatesIn)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("No finiteness assumption is needed. The representatives "
                        + "whose inverse conjugation sends g into K map onto both X and Y."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("fixed-coset-branching-count"),
                    DeclarationHandle.Create(Module + ".card_fixedCosets_mul_card_subgroup"),
                    H("Cardinality for finite G"),
                    StatementSource.FromAuthor(Disp(new Formula.Relation(
                        Mul(Card(fixedCosets), Card(subgroup)), FormulaRelationOperator.Equal,
                        Mul(Card(centralizer), Card(conjugatesIn))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Assume G is finite. Over a fixed coset with representative x, "
                        + "the quotient fiber is xK. Over the conjugate given by x, "
                        + "the conjugation fiber is Cx. The two fiber counts give the displayed equation."))),
                    DescribeRole.Theorem),
                Paragraph(Text("In Davydov and Simmons, On Lagrangian algebras in group-theoretical "
                    + "modular categories, use K for the paper's H. In equation (25) the degree-g "
                    + "summand for xK comes from degree x inverse times g times x of the twisted "
                    + "group algebra of K. It is one-dimensional when that conjugate belongs to K "
                    + "and zero otherwise. Equivalently, Theorem 4.8 evaluated at degree g and "
                    + "acting element 1 counts X, since each contributing term is 1. The passage "
                    + "from the categorical algebra to a VOA extension uses an external correspondence. "
                    + "https://arxiv.org/abs/1603.04650")))));
    }
}
