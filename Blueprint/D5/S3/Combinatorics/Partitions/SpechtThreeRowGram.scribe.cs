using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtThreeRowGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint ordered-colouring Gram matrices", H("Joint ordered-colouring Gram matrices"), Blocks(
            Paragraph(Text("Fix an arbitrary natural degree n. An ordered colouring is a map f from Fin n to Fin 3. Its three labelled fibres are the three ordered blocks. For an integer margin a, Colourings(n,a) consists of f with cardinality of the i-th fibre equal to a(i) in the integers. The symmetric group acts by precomposition with the inverse permutation. A negative margin gives the empty type. Zero margins remain labelled empty blocks, and equal margins retain distinct labels: there is no extra factorial for repeated or empty rows.")),
            Paragraph(Text("eta(a,g) is the number of colourings fixed by g, with margin a. colouringRepresentation is the actual complex permutation representation on Colourings(n,a), defined independently of eta. The character formula below proves that its trace is eta. Fixedness under g inverse and fixedness under g are equivalent.")),
            Paragraph(Text("A contingency table is a function A from Fin 3 times Fin 3 to the natural numbers, with total n and integer row and column margins a and b. contingencyTables is the finite set of such functions and C(n,a,b) is its cardinality. Each entry is automatically at most n. This definition also gives zero if a margin is negative or has the wrong total.")),
            Paragraph(Text("For each single permutation g, a pair of invariant colourings f and h is equivalent to the invariant joint colouring x mapped to (f(x),h(x)). The joint fibre A(i,j) has the intersection cardinality of the two blocks. Its row and column sums recover the original marginal sizes. Summing first over g and then over joint colourings counts each joint colouring with the order of its fibre-preserving subgroup. Grouping by its nine fibre sizes gives n factorial for each table: all colourings of the same fibre sizes form one orbit, every such fibre-size function occurs, and quotient cardinality times stabilizer cardinality is the order of the symmetric group. Both marginal invariance conditions use the same g throughout.")),
            Paragraph(Text("For a natural triple r and a permutation s of Fin 3, shifted(r,s)(i) is the integer r(i)-i+s(i). Define Theta(r,g) as the sum of sign(s) times eta(shifted(r,s),g) over all six s. The signed contingency Gram is the double sum of sign(s)sign(t) C(n,shifted(r,s),shifted(q,t)). Expanding both finite sums and applying the joint Gram formula proves the signed character identity below. This uses no Specht multiplicity, tableau number or Frobenius coefficient.")),
            Describe.Lean(DescribeId.Create("character-colouringrepresentation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.character_colouringRepresentation"),
                H("The count is the actual permutation trace"), StatementSource.FromAuthor(Disp(All("n", Nat(), All("a", Call("IntTriple"), All("g", Call("PermFin", Id("n")), Eq(Call("traceColouring", Id("n"), Id("a"), Id("g")), Call("complexNatCast", Call("eta", Id("a"), Id("g"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("traceColouring is the character of colouringRepresentation; eta is fixedColourings. The trace is obtained from the actual permutation action."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-fixedcolourings-mul"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.sum_fixedColourings_mul"),
                H("Joint fixed colourings give the contingency Gram matrix"), StatementSource.FromAuthor(Disp(All("n", Nat(), All("a", Call("IntTriple"), All("b", Call("IntTriple"), Eq(Call("sumPerm", Id("n"), Call("etaProduct", Id("a"), Id("b"))), Call("mul", Call("factorial", Id("n")), Call("C", Id("n"), Id("a"), Id("b"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("etaProduct(a,b)(g) is eta(a,g)eta(b,g). C counts the finite tables just defined. The equation is unnormalised and valid for arbitrary integer margins."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-colouringtrace-mul"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.sum_colouringTrace_mul"),
                H("The Gram identity for actual complex permutation traces"), StatementSource.FromAuthor(Disp(All("n", Nat(), All("a", Call("IntTriple"), All("b", Call("IntTriple"), Eq(Call("sumPerm", Id("n"), Call("colouringTraceProduct", Id("a"), Id("b"))), Call("complexNatCast", Call("mul", Call("factorial", Id("n")), Call("C", Id("n"), Id("a"), Id("b")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("Both factors are the actual characters of the ordered-colouring representations. The formula is obtained by the exact natural-to-complex cast of the joint count."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-virtualcharacter-mul"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.sum_virtualCharacter_mul"),
                H("The signed contingency sum is the virtual character Gram matrix"), StatementSource.FromAuthor(Disp(All("n", Nat(), All("r", Call("NatTriple"), All("q", Call("NatTriple"), Eq(Call("sumPerm", Id("n"), Call("ThetaProduct", Id("r"), Id("q"))), Call("mul", Call("intNatCast", Call("factorial", Id("n"))), Call("signedContingencyGram", Id("n"), Id("r"), Id("q"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("ThetaProduct(r,q)(g) is Theta(r,g)Theta(q,g). The finite double sum has six times six terms, but the symmetric-group degree n is unrestricted."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Nat() => Call("Nat");
}
