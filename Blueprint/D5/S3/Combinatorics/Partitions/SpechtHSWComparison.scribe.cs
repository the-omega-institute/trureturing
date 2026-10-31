using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtHSWComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Same-shape ordinary trace and the HSW coefficient", H("Same-shape ordinary trace and the HSW coefficient"), Blocks(
            Paragraph(Text("The descending HSW Vandermonde equals the staircase alternant with exponents (2,1,0). Height vanishing removes diagrams with more than three rows. The division-free bialternant and strict decrease of beta numbers isolate exactly the literal target partition. Applying this coefficient to unrestricted Frobenius identifies the existing integer frobChar with the same-partition integer character. The integer-to-complex cast then gives the actual trace of the preserved polytabloid representation. A decreasing triple constructs its literal positive-parts partition and retains zero padding in all row coordinates. The full permutation partition in the hypothesis includes fixed points. The degree and parity are unrestricted. In the formulas, sameFullPartition means both partition(pi).parts = rho.parts and the multiset of the list tau equals rho.parts. decreasingTripleSum means Antitone(a) and the sum of its three entries is n. firstThreeRows records the row-length function, including zero rows. intToComplex is the canonical integer cast.")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtHSWComparison.spechtTrace_eq_hsw_frobChar"),
                H("The actual ordinary trace equals the existing coefficient"), StatementSource.FromAuthor(Disp(All("n", Nat(), All("mu", Part(Id("n")), All("rho", Part(Id("n")), Imp(Call("heightLe", Id("mu"), new Formula.Number(3)), All("pi", Call("PermFin", Id("n")), All("tau", Call("List", Nat()), Imp(Call("sameFullPartition", Id("pi"), Id("rho"), Id("tau")), Eq(Call("complexTrace", Call("spechtModuleComplex", Id("mu")), Id("pi")), Call("intToComplex", Call("HSWfrobChar", Call("firstThreeRows", Id("mu")), Id("tau"))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("statement-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtHSWComparison.spechtTrace_triplePartition_eq_hsw_frobChar"),
                H("Literal zero-padded triples"), StatementSource.FromAuthor(Disp(All("n", Nat(), All("a", Call("Function", Call("Fin", new Formula.Number(3)), Nat()), Imp(Call("decreasingTripleSum", Id("a"), Id("n")), All("rho", Part(Id("n")), All("pi", Call("PermFin", Id("n")), All("tau", Call("List", Nat()), Imp(Call("sameFullPartition", Id("pi"), Id("rho"), Id("tau")), Eq(Call("complexTrace", Call("spechtModuleComplex", Call("triplePartition", Id("a"))), Id("pi")), Call("intToComplex", Call("HSWfrobChar", Id("a"), Id("tau"))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Nat() => Call("Nat");
    private static Formula Part(Formula n) => Call("Partition", n);
}
