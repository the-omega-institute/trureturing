using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtYoungTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shape distinction and orthogonality of actual ordinary Specht traces", H("Shape distinction and orthogonality of actual ordinary Specht traces"), Blocks(
            Paragraph(Text("Here SComplex(mu) is exactly the existing complex scalar extension of the rational polytabloid representation for YoungDiagram.ofPartition mu. MComplex(nu) is the existing complex representation on cosets of the literal Young subgroup. The complex Hom dimensions vanish outside dominance and equal one on the diagonal, by the rational multiplicity calculation and equality of the actual character pairings under the rational to complex map. An isomorphism of two Specht modules would preserve those Hom dimensions, forcing dominance in both directions and hence equality of the literal partition labels. The pinned finite group character orthogonality theorem then uses the established simplicity of these same representations. trace(mu,pi) means LinearMap.trace over Complex of the existing action rho of SComplex(mu) at pi. The sum includes all permutations, including fixed points; the inverse is the group inverse. No ordinary character is defined by a polynomial coefficient.")),
            Describe.Lean(DescribeId.Create("specht-module-complex-iso-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtYoungTrace.spechtModuleℂ_iso_iff"),
                H("The actual modules retain their shape labels"), StatementSource.FromAuthor(Disp(All("n", Nat(), All("mu", Part(Id("n")), All("nu", Part(Id("n")), Call("Iff", Call("Nonempty", Call("Iso", Call("SComplex", Id("mu")), Call("SComplex", Id("nu")))), Eq(Id("mu"), Id("nu")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation has the meanings specified above."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-specht-trace-mul-specht-trace-inv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtYoungTrace.sum_spechtTrace_mul_spechtTrace_inv"),
                H("Ordinary trace row orthogonality"), StatementSource.FromAuthor(Disp(All("n", Nat(), All("mu", Part(Id("n")), All("nu", Part(Id("n")), Eq(Call("sumPerm", Id("n"), Call("traceProductWithInverse", Id("mu"), Id("nu"))), Call("ifThenElse", Eq(Id("mu"), Id("nu")), Call("complexNatCast", Call("factorial", Id("n"))), D(0)))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation has the meanings specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Part(Formula n) => Call("Partition", n);
    private static Formula Nat() => Call("Nat");
}
