using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class CentralizingInvolutionTranslationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Translation by an involution centralizing the code in the same Cayley sum graph.",
        H("The sufficient same-graph repair"),
        Blocks(Describe.Lean(DescribeId.Create("centralizing-involution-translation"),
            DeclarationHandle.Create("D5/S3/Combinatorics/CayleySumCodes/CentralizingInvolutionTranslation.result"),
            H("Preserving the open-neighbor code"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/GraphInvariants/manikandishzhang2026sumcodes")),
            Blocks(
                Paragraph(Text(
                    "For a normal connection subset Y of a group G, a code subset C, and b with "
                    + "b*b=1 which commutes with every member of C, C is a total perfect code "
                    + "if and only if its right translate Cb is a total perfect code in the same "
                    + "loopless CS(G,Y). Finite subgroup codes are included. The proof also "
                    + "holds without finiteness or subgroup closure of C.")),
                Paragraph(Text(
                    "For h in C, (g*b)*h=g*(h*b), and g*b differs from h precisely when g "
                    + "differs from h*b. Right multiplication by b is its own inverse, so these "
                    + "incidence bijections transport both existence and uniqueness. It is "
                    + "enough that b centralizes C; no commutation with every ambient vertex "
                    + "is assumed.")),
                Paragraph(Text(
                    "This is the sufficient repair in section 2.1 of the revised public source, "
                    + "DOI 10.5281/zenodo.23375144. The original version's altered connection "
                    + "set and missing involution hypothesis are not used. Merely normalizing "
                    + "a subgroup is insufficient, as shown by the source's order-32 example. "
                    + "That example and a necessary-and-sufficient classification of all "
                    + "code-preserving translations are separate obligations."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion"))]));
}
