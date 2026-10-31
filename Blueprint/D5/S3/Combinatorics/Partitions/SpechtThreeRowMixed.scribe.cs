using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtThreeRowMixedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal three-row shapes and the mixed pairing", H("Literal three-row shapes and the mixed pairing"), Blocks(
            Paragraph(Text("For a natural triple r of total n, tripleShape(r) is the partition of n whose parts are the positive entries of r, with their multiplicities. This is the existing weightPartition of the finitely supported function r. When r0 is at least r1 and r1 is at least r2, its sorted parts are the list [r0,r1,r2] with zeros deleted. Its first three row lengths, padded with zeros, are exactly r. This includes n=0, equal rows and any number of zero rows.")),
            Paragraph(Text("The ordered-colouring character at a natural margin a equals the fixed-coset character of the literal Young subgroup for tripleShape(a). To see this, take the coefficient of the monomial a in the full-cycle power sum of the permutation. coeff_psumPart_partition computes it as the number of invariant colourings. coeff_psumPart_eq_card_fixedPoints computes the same coefficient as fixed cosets of youngSubgroup(weightPartition(a)). These are independently defined actual permutation actions. The comparison retains labels on equal or empty colours and introduces no factorial for equal rows or zero rows.")),
            Paragraph(Text("For a natural weight a, the existing permutation carrying a to partWeight gives a permutation of its three entries to the first three literal row lengths. The latter decrease. Therefore a0 is at most the first row length and a0+a1 is at most the sum of the first two row lengths. Checking the possible distinct positions of the two selected entries proves these inequalities, uniformly in the entries and total n.")),
            Paragraph(Text("Let s be a nonidentity permutation of the three indices. The integer shifted entries are r(i)-i+s(i). Their sum is n. If s(0) is positive, the first shifted prefix strictly exceeds r0. If s(0)=0, injectivity forces s(1) to be positive; if it were 1 then s would be the identity, so s(1)=2 and the second shifted prefix strictly exceeds r0+r1. When all shifted entries are nonnegative, sorting increases these prefixes. Thus tripleShape(r) does not dominate the shifted weight partition. The existing finrank_hom_spechtModuleComplex_permutationModuleComplex_eq_zero kills its actual mixed pairing. A negative shifted entry gives no colourings at all.")),
            Paragraph(Text("At the identity shift, the Young partition is tripleShape(r) itself. Its actual complex Hom dimension from the same Specht module is one. The full-cycle trace pairing is n factorial times this dimension. Summing with the six signs leaves n factorial. The resulting mixed pairing enters the integer sum-of-squares criterion for the ordinary trace; only its self-Gram hypothesis remains at this stage.")),
            Node("mixed-pairing", "sum_spechtChar_mul_virtualCharacter", "The actual same-shape mixed pairing", MixedStatement(),
                "The character chi is the integral trace of the existing complex polytabloid Specht module with literal partition tripleShape(r). Theta is the signed sum of the actual ordered-colouring characters. The identity holds for every natural degree n."),
            Node("trace-selfgram", "ordinaryTrace_eq_frobChar_of_selfGram", "The trace criterion with the mixed pairing supplied", TraceStatement(),
                "The full conjugacy partition rho and the full multiset of tau include every one-cycle and every repeated part. The only additional scalar hypothesis is signedContingencyGram(n,r,r)=1."))));

    private static Formula MixedStatement() => All("n", Nat(), All("r", Call("NatTriple"),
        Imp(Call("totalEq", Id("r"), Id("n")), Imp(Call("decreasing", Id("r")),
            Eq(Call("mixedSpechtThetaSum", Call("tripleShape", Id("r")), Id("r")), Call("intFactorial", Id("n")))))));
    private static Formula TraceStatement() => All("n", Nat(), All("r", Call("NatTriple"), All("rho", Call("Partition", Id("n")),
        All("g", Call("PermFin", Id("n")), All("tau", Call("ListNat"),
        Imp(Call("totalEq", Id("r"), Id("n")), Imp(Call("decreasing", Id("r")),
        Imp(Eq(Call("signedContingencyGram", Id("n"), Id("r"), Id("r")), D(1)),
        Imp(Call("hasFullConjugacyPartition", Id("g"), Id("rho")), Imp(Call("multisetEqParts", Id("tau"), Id("rho")),
        Eq(Call("ordinarySpechtTrace", Call("tripleShape", Id("r")), Id("g")), Call("complexIntCast", Call("HSWfrobChar", Id("r"), Id("tau"))))))))))))));
    private static DocumentBlock Node(string id, string name, string title, Formula statement, string prose) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtThreeRowMixed." + name), H(title),
        StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula Nat() => Call("Nat");
}
