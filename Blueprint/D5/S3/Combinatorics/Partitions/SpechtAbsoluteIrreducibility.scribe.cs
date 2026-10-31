using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtAbsoluteIrreducibilityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Specht AbsoluteIrreducibility",
        H("Specht AbsoluteIrreducibility"),
        Blocks(
            Paragraph(Text("The invariant orthogonal decomposition gives a preimage of each polytabloid inside the Specht subspace under its column antisymmetrizer. An equivariant endomorphism commutes with this operator, whose image is a single polytabloid line. It acts by one scalar on that polytabloid. The orbit spans the entire Specht space, forcing the same scalar everywhere. Transport to the original partition identifies rational Specht intertwining endomorphisms with the rational field.")),
            Paragraph(Text("EndIntertwiner denotes the algebra of equivariant endomorphisms of the indicated representation; rationalScalarMap sends a rational number to its scalar endomorphism. The final algebra equivalence is the inverse of that bijective scalar map. columnAntisymmetrizerAction is the group-algebra action of the displayed tableau column antisymmetrizer on the rational permutation space.")),
            Describe.Lean(DescribeId.Create("exists-mem-asalgebrahom-columnantisymmetrizer-eq-polytabloid"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid"),
                H("exists mem asAlgebraHom columnAntisymmetrizer eq polytabloid"), StatementSource.FromAuthor(Disp(Tableau(E("e", C("permutationSpace", C("shapePartition", I("mu"))), B(C("member", I("e"), C("spechtSubspace", I("mu"))), Q(C("columnAntisymmetrizerAction", I("t"), I("e")), C("polytabloid", I("t")))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("algebramap-intertwiningmap-spechtsubrepresentation-bijective"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.algebraMap_intertwiningMap_spechtSubrepresentation_bijective"),
                H("algebraMap intertwiningMap spechtSubrepresentation bijective"), StatementSource.FromAuthor(Disp(Shape(C("Bijective", C("rationalScalarMap", C("EndIntertwiner", C("spechtSubrepresentation", I("mu")))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("algebramap-intertwiningmap-spechtmodule-bijective"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.algebraMap_intertwiningMap_spechtModule_bijective"),
                H("algebraMap intertwiningMap spechtModule bijective"), StatementSource.FromAuthor(Disp(Part(C("Bijective", C("rationalScalarMap", C("EndIntertwiner", C("spechtModule", I("mu")))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spechtmoduleintertwiningendalgequiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.spechtModuleIntertwiningEndAlgEquiv"),
                H("spechtModuleIntertwiningEndAlgEquiv"), StatementSource.FromAuthor(Disp(Part(Q(C("spechtModuleIntertwiningEndAlgEquiv", I("mu")), C("inverseRationalScalarAlgebraEquivalence", C("spechtModule", I("mu"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Definition))));

    private static Formula I(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(I(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(I(name))), [.. args]);
    private static Formula A(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula E(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Q(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula B(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Shape(Formula body) => A("mu", C("YoungDiagram"), body);
    private static Formula Tableau(Formula body) => Shape(A("t", C("YoungTableau", I("mu")), body));
    private static Formula Part(Formula body) => A("n", C("Nat"), A("mu", C("Partition", I("n")), body));
}
