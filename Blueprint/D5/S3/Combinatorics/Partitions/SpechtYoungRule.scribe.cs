using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtYoungRuleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Specht Hom dimensions are Kostka numbers", H("Actual Specht Hom dimensions are Kostka numbers"), Blocks(
            Paragraph(Text("Multiplicity(mu,nu) is the complex dimension of Hom from the independently constructed same-shape polytabloid Specht representation to the literal Young permutation representation. Actual character orthogonality and completeness give its Gram matrix. The complete homogeneous coefficient gives the same Gram matrix for Kostka numbers. Both matrices are unitriangular for dominance. Descending induction in the finite partial order identifies their entries, so the resulting character equality refers to the actual representations.")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtYoungRule.finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_kostkaNumber"),
                H("Young rule for actual Hom spaces"), StatementSource.FromAuthor(Disp(All("n", Nat(), All("mu", Part(Id("n")), All("nu", Part(Id("n")), Eq(Call("finrankComplexHom", Call("spechtModuleComplex", Id("mu")), Call("permutationModuleComplex", Id("nu"))), Call("K", Id("mu"), Id("nu")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Nat() => Call("Nat");
    private static Formula Part(Formula n) => Call("Partition", n);
}
