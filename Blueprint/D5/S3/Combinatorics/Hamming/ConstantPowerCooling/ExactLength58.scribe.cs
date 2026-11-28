using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming.ConstantPowerCooling;

internal sealed class ExactLength58Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hamming/ConstantPowerCooling/ExactLength58.";
    private const string Paper = "D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact optimum is 57 information classes at length 58, weight six and deletion size two.",
        H("The exact cooling-code optimum at length 58"),
        Blocks(
            Describe.Lean(DescribeId.Create("no-group-divisible-design"),
                DeclarationHandle.Create(Prefix + "no_group_divisible_design"),
                H("Obstruction to the group divisible design"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Call("Nonempty",
                    Call("GroupDivisibleDesign", Call("Fin", D(5, 8)), D(8), D(2)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Paper)),
                Blocks(Paragraph(Text(
                    "There is no group divisible design on 58 points with blocks of size eight and groups of size two. "
                    + "Every point lies in eight blocks because each of its 56 cross-group pairs occurs once and "
                    + "each incident block contributes seven such pairs. Counting incidences gives 58 blocks. "
                    + "For the square integer point-by-block incidence matrix A, the Gram matrix is "
                    + "8I + J − P, where J is the all-ones matrix and P records membership in the same group, "
                    + "including on the diagonal. The matrix 8I − P has 29 two-by-two diagonal blocks of determinant 48 "
                    + "and acts on the all-ones column by multiplication by six. The rank-one update by J "
                    + "multiplies the determinant by 1 + 58/6. Thus det(AAᵀ) = 2¹²¹ · 3²⁸. "
                    + "Its odd exponent of two contradicts det(AAᵀ) = det(A)² over the integers."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("support-optimum"),
                DeclarationHandle.Create(Prefix + "support_optimum"),
                H("Exactly 57 information classes"),
                StatementSource.FromAuthor(OptimumStatement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Paper)),
                Blocks(Paragraph(Text(
                    "In the support model every word has size six, every two-point deletion leaves a word "
                    + "in each class, and supports in different classes meet in at most one point. For weight "
                    + "six this intersection condition is equivalent to the cross-class Hamming distance "
                    + "being at least nine, as required for correction radius four. The projective plane over "
                    + "the field with seven elements has 57 points and 57 lines. Embed the points into 58 "
                    + "coordinates with one unused coordinate. Each line has eight points and supplies one "
                    + "class of all six-subsets of its points. Removing two coordinates leaves at least six "
                    + "points on each line, and distinct lines meet in at most one point. The finite bound "
                    + "gives at most 58 classes. Attaining 58 would force the design excluded above by the "
                    + "even-residue design criterion. Hence 57 is attained and bounds every valid family "
                    + "for these parameters. Section 5's question also includes other parameter choices."))),
                DescribeRole.Theorem)),
        []));

    private static Formula OptimumStatement()
    {
        Formula m = F.Id("m");
        Formula p = F.Id("P");
        Formula familyType = new Formula.TypeArrow(
            Call("Fin", m), Call("Finset", Call("Finset", Call("Fin", D(5, 8)))));
        Formula family = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("P"),
            familyType, Call("IsSupportFamily", p, D(6), D(2)));
        Formula attained = Seq(OpenBrace, m, Colon, Sp, Mathbb, Grp(F.Id("N")),
            Sp, Bar, Sp, family, CloseBrace);
        return Disp(Call("IsGreatest", attained, D(5, 7)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
