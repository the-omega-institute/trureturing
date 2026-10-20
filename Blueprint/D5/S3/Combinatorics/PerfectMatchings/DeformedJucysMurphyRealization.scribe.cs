using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class DeformedJucysMurphyRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRealization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every partition is realized by an actual native matching with its complete coset type.",
        H("Actual Matching Representatives for Every Partition"),
        Blocks(
            Describe.Lean(DescribeId.Create("matching-realization"),
                DeclarationHandle.Create(Prefix + "matching_realization"),
                H("All Partitions Have Native Representatives"),
                StatementSource.FromAuthor(Disp(All("k", V("Nat"),
                    All("rho", Call("Partition", V("k")),
                        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("p"),
                            Call("P", V("k")), Equal(Call("ct", V("p")), V("rho"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose a permutation with the prescribed parts at least two "
                    + "as its ordinary cycle type. The full SameCycle partition also contains every "
                    + "fixed singleton orbit. Its nontrivial blocks correspond bijectively to cycle "
                    + "factor supports. A positive multiset is reconstructed from those blocks and "
                    + "its total sum, restoring exactly the required singleton multiplicity. The "
                    + "canonical oriented construction turns the permutation into a fixed-point-free "
                    + "involutive partner map on Fin(2k); the existing ct_oriented theorem identifies "
                    + "its complete type. The argument includes k=0 and all repeated parts."))),
                DescribeRole.Theorem))));
    private static Formula V(string s) => F.Id(s);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
