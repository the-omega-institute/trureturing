using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class HemmerStraubWestremOrdinaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary Specht characters in both HSW averages", H("Ordinary Specht characters in both HSW averages"), Blocks(
            Paragraph(Text("ordinaryCharacter(mu,rho) is the complex linear trace of the independently constructed polytabloid representation spechtModuleComplex(mu) at a representative of the full positive cycle partition rho. The representative is selected from the permutation conjugacy class; its definition contains no Frobenius coefficient. The inherited same-partition ordinary-trace theorem supplies irreducibility and independence from the representative, with fixed points retained. The literal triplePartition removes zero rows and preserves the three original row lengths.")),
            Paragraph(Text("For a partition lambda of n, evTypes(lambda.parts.toList) is the original list of independent per-occurrence replacements a by (2a) or (a,a). It is kept as a list, including duplicate outcomes. Each occurrence tau is converted to its full partition of 2n using positivity and the doubled sum. leftTerm(lambda) sums (-1) to the length of tau times the ordinary character over every weakly decreasing even triple of size 2n, with zero padding. rightTerm(lambda) sums the ordinary character at the literal rectangle (n,n,0), for odd and even n alike. Attaching membership proofs to these lists and finite shape sets changes no multiplicity.")),
            Paragraph(Text("leftAverage(n) and rightAverage(n) sum those terms over every partition lambda of n with the rational weight inverse(zPartition(lambda)), then cast that rational weight into the complex numbers. The existing zPartition is the full product of k to multiplicity(k) times factorial(multiplicity(k)), with positive cycle sizes including one. coefficientLeftAverage and coefficientRightAverage below denote the literal rational sums displayed in averages_eq_frobenius, using the existing HSW frobChar and the same Ev list, shapes, sign and weight. ratToComplex is the canonical rational cast. The integer coefficient is cast into the rationals before this final cast.")),
            Describe.Lean(DescribeId.Create("representative"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary.ordinaryCharacter_eq_trace"),
                H("Independence of the full-cycle representative"),
                StatementSource.FromAuthor(Disp(All("n", Nat(), All("mu", Part(Id("n")), All("rho", Part(Id("n")), All("pi", Call("PermFin", Id("n")), Imp(Call("sameFullPartition", Id("pi"), Id("rho")), Eq(Call("ordinaryCharacter", Id("mu"), Id("rho")), Call("complexTrace", Call("spechtModuleComplex", Id("mu")), Id("pi")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("sameFullPartition states equality of the complete partition parts, including all fixed points."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pointwise"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary.pointwise_identity"),
                H("Ordinary identity for each input partition"),
                StatementSource.FromAuthor(Disp(All("n", Nat(), Imp(Call("positive", Id("n")), All("lambda", Part(Id("n")), Eq(Call("leftTerm", Id("lambda")), Call("rightTerm", Id("lambda")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/hemmerstraubwestrem2025riordan")),
                Blocks(Paragraph(Text("The actual trace comparison is used in both terms before applying the existing HSW pointwise coefficient identity. No coefficient is defined to be an ordinary character."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("transport"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary.averages_eq_frobenius"),
                H("Transport of both original weighted averages"),
                StatementSource.FromAuthor(Disp(All("n", Nat(), And(
                    Eq(Call("leftAverage", Id("n")), Call("ratToComplex", Call("coefficientLeftAverage", Id("n")))),
                    Eq(Call("rightAverage", Id("n")), Call("ratToComplex", Call("coefficientRightAverage", Id("n")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/hemmerstraubwestrem2025riordan")),
                Blocks(Paragraph(Text("This transport is unrestricted in degree. Both integer coefficient sums are cast through the rationals. Every original partition, Ev occurrence, sign and even three-row shape remains present."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary.weighted_identity"),
                H("Equality of the two ordinary weighted averages"),
                StatementSource.FromAuthor(Disp(All("n", Nat(), Imp(Call("positive", Id("n")), Eq(Call("leftAverage", Id("n")), Call("rightAverage", Id("n"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/hemmerstraubwestrem2025riordan")),
                Blocks(Paragraph(Text("The domain is every natural n at least one. This theorem asserts equality of the averages. Evaluation as choose(n/2+2,2) for even n and zero for odd n requires the existing weighted coefficient supplier; that evaluation is outside these transport declarations."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Nat() => Call("Nat");
    private static Formula Part(Formula n) => Call("Partition", n);
}
