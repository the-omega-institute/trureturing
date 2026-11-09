using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class AliabadiQuotientObstructionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/aliabadi2026nonabeliantwist");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite nonabelian group has a multiset satisfying the abelianization obstruction which is not a multiset of right quotients of two bijective enumerations.",
        H("Abelianization does not characterize right quotient multisets"), Blocks(
            Describe.Lean(
                DescribeId.Create("aliabadi-full-quotient-obstruction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/AliabadiQuotientObstruction.exists_obstructed_multiset"),
                H("A nonidentity element of the commutator subgroup suffices"),
                StatementSource.FromAuthor(ExactStatement()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let G be any finite group with noncommutative multiplication, and put n=|G|. The canonical map pi is Abelianization.of from G to G/[G,G]. There exists a genuine multiset A of cardinality n, counted with multiplicity, for which the product of the pi-images is one, while no two bijective functions b,c from Fin n to G have A equal to the multiset of b(i) times the inverse of c(i). In the formula, RightQuotientMultiset(b,c) denotes the map of the univ multiset of Fin n under i mapped to b(i) times the inverse of c(i); MultisetMap and MultisetProd preserve all multiplicities. AbelianizationOf denotes exactly the canonical Abelianization.of. Fin n consists of 0 through n-1; adding one identifies this index set with 1 through n. A Fintype structure presents an arbitrary finite group and adds no group-theoretic assumption.")),
                    Paragraph(Text("The commutator subgroup is nontrivial, since commutator_eq_bot_iff identifies its triviality with commutativity. Subgroup.nontrivial_iff_exists_ne_one supplies a nonidentity element a in it. Abelianization.ker_of proves pi(a)=1. Take A to contain a once and the identity n-1 times. A group is nonempty, so n is positive and the multiset has cardinality n. All entries have pi-image one, so their multiplicity-counted product in the abelian quotient is one.")),
                    Paragraph(Text("Suppose b and c realize A. Regard both bijections as equivalences and form the permutation tau=c inverse composed with b on Fin n. Then tau(i) differs from i exactly when b(i) times the inverse of c(i) differs from one. Filter the asserted multiset equality by being different from the identity. The left side has cardinality one. Multiset.filter_map and Multiset.card_map identify the right side with the cardinality of tau.support. Equiv.Perm.card_support_ne_one rules out this value. The permutation and multiset bridge is proved within the argument, with no additional realization assumption.")),
                    Paragraph(Text("Repeated identity entries are allowed. The construction imposes no solvability, parity, group-family or identity-free condition. Every ordering of A in G has product a, which differs from one; the product used in the theorem is exclusively in the abelianization. Thus the statement answers the literal Problem 7.6 and leaves the stronger product-one-ordering variant separate. The argument applies existing general results about commutators, multiset operations and permutation support; it does not assert a new general method or literature priority."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("aliabadi-2605-16478v2-problem-7-6"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula ExactStatement()
    {
        var g = F.Id("G"); var a = F.Id("A"); var b = F.Id("b"); var c = F.Id("c");
        var n = Call("FintypeCard", g);
        var index = new Formula.TypeArrow(Call("Fin", n), g);
        var realization = Ex("b", index, Ex("c", index,
            And(Call("Bijective", b), And(Call("Bijective", c),
                Eq(a, Call("RightQuotientMultiset", b, c))))));
        var result = Ex("A", Call("Multiset", g),
            And(Eq(Call("MultisetCard", a), n),
                And(Eq(Call("MultisetProd", Call("MultisetMap", Call("AbelianizationOf", g), a)), D(1)),
                    new Formula.Not(realization))));
        return Disp(All("G", F.Id("Typeu"),
            All("group", Call("Group", g), All("finite", Call("Fintype", g),
                All("hna", new Formula.Not(Call("IsMulCommutative", g)), result)))));
    }
}
