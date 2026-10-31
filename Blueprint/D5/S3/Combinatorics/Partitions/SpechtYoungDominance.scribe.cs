using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtYoungDominanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dominance for genuine Specht intertwiners", H("Dominance for genuine Specht intertwiners"), Blocks(
            Paragraph(Text("A partition mu dominates nu when every prefix sum of the decreasing parts of nu is at most the corresponding prefix sum of mu. For a Young diagram D, S(D) is the existing rational polytabloid span inside its Young permutation module, shape(D) is its literal row partition, and M(nu) is the rational permutation representation on cosets of youngSubgroup nu. Intertwiner(S(D),M(nu)) denotes the full vector space of equivariant rational linear maps. A nonzero such map is injective by the existing atomicity of the Specht span. A preimage of a polytabloid under its column antisymmetrizer then yields the row and column counting inequality. The diagonal and dominance zero statements below consume this implication.")),
            Describe.Lean(DescribeId.Create("dominates-of-intertwining-map-ne-zero"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtYoungDominance.dominates_of_intertwiningMap_ne_zero"),
                H("A nonzero intertwiner forces dominance"), StatementSource.FromAuthor(Disp(All("D", Call("YoungDiagram"), All("nu", Part(Call("card", Id("D"))), All("f", Call("Intertwiner", Call("S", Id("D")), Call("M", Id("nu"))), Imp(Ne(Id("f"), D(0)), Call("Dominates", Call("shape", Id("D")), Id("nu")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation has the meanings specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula Part(Formula n) => Call("Partition", n);
}
