using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtFrobeniusPairingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Specht traces paired with Young permutation characters", H("Actual Specht traces paired with Young permutation characters"), Blocks(
            Paragraph(Text("The complex Specht module is the independently constructed scalar extension of the literal YoungDiagram.ofPartition polytabloid span. Its character is the trace of its existing action. The Young permutation module is the representation on cosets of the literal Young subgroup. The existing finite-character pairing identifies their pairing with the dimension of the corresponding equivariant Hom space. Inversion preserves a permutation's full cycle partition, so the actual Specht trace takes the same value at a permutation and its inverse.")),
            Paragraph(Text("For n a natural number, mu and nu partitions of n, and pi a permutation of Fin(n), write trace(mu,pi) for the complex trace of the Specht action and fixedTabloids(nu,pi) for the natural cardinality of fixed cosets of youngSubgroup(nu). HomDimension(mu,nu) is the complex finrank of Hom(spechtModuleComplex(mu),permutationModuleComplex(nu)). The displayed finite sum uses every permutation, including those with one-cycles. No character is defined through a polynomial coefficient.")),
            Describe.Lean(DescribeId.Create("sum-specht-trace-mul-card-fixed-points"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtFrobeniusPairing.sum_spechtTrace_mul_card_fixedPoints"),
                H("Trace pairing with the actual Young permutation representation"), StatementSource.FromAuthor(Pairing()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("SpechtYoungTrace and SpechtThreeRowMixed consume this identity on the proof route to the literal same-shape trace comparison and both full ordinary weighted endpoints. The exact list-to-partition power-sum transport is also consumed by SpechtThreeRowVirtual and retains repeated parts and every one-cycle. Two former unconsumed polynomial-comparison wrappers are retired. This supplier has no standalone first-freeze claim. The remaining public-declaration audit is tracked at https://github.com/the-omega-institute/trureturing/issues/24542."))),
                DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Pairing()
    {
        Formula n = Id("n"), mu = Id("mu"), nu = Id("nu"), pi = Id("pi");
        Formula term = Seq(Call("trace", mu, pi), Sp, Call("natCast", Call("fixedTabloids", nu, pi), Call("Complex")));
        Formula lhs = Seq(new Formula.Subscript(Sum, Seq(pi, Colon, Sp, Call("Perm", Call("Fin", n)))), Sp, Grp(term));
        Formula rhs = Seq(Call("natCast", Call("factorial", n), Call("Complex")), Sp,
            Call("natCast", Call("HomDimension", mu, nu), Call("Complex")));
        return Disp(All("n", Call("Nat"), All("mu", Call("Partition", n), All("nu", Call("Partition", n),
            new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs)))));
    }
}
